// Regions over the loan engine (docs/ARCH.md section 5): rustc's NLL for one body.
//
// Checked types are region-erased. This file renumbers every region slot of every
// local's type into a region variable, adds outlives constraints (`'a: 'b`, an edge
// a -> b) from each statement and call by relating types with variance, and solves
// them by reachability. A loan's region then reaches a set of locals (those whose
// types it flows into) and maybe universal regions (`'static` or a lifetime param of
// the fn). `mod.rs` turns that into loan scopes: a loan is in scope from its borrow
// on, through points where one of those locals is live, and everywhere reachable
// when it reaches a universal region. Region values are location-insensitive sets,
// as in rustc, so a reference local that is reassigned keeps every loan it ever held
// for as long as it is live (Polonius would forget them; rustc does not).
//
// Slots of an erased type, in canonical pre-order: a reference contributes its own
// region, then its pointee's slots; an Adt its region params (builtin `Chars` has
// one), then its type args in order; tuples, arrays, slices, and raw pointers their
// elements; a closure its upvar types; a fn pointer type that names a lifetime of
// the enclosing item one, that free region (W-BORROW3, `fnptr`); a dyn type its
// object lifetime, then the regions of its trait args (`dyn_arg_tys`, R11). Type
// params, projections, other fn pointers, fn items, and scalars have none. A region
// a dyn's `Fn*` sugar binds itself (`ty::DYN_LATE`, late-bound) has no slot.
//
// Signatures keep their regions in a side table (`RegionTables`) that collect fills
// with the resolver's keep mode (check/generics.rs `RegionMode`): `Region::Static`
// for `'static`, `Region::Param(i)` for the i-th universal region (each elided input
// gets its own, outputs follow Rust's elision rules). Fns without an entry (lang
// trait stubs, instances) get a conservative signature from their erased types.
use super::bit_iter;
use crate::check::collect::*;
use crate::diag::{Diag, Span};
use crate::intern::FxMap;
type FxSet<T> = std::collections::HashSet<T, std::hash::BuildHasherDefault<crate::intern::FxHasher>>;
use crate::ir::*;
use crate::ty::*;

mod fnptr;
mod replay;
mod selfproj;
mod store;
mod supers;
pub use selfproj::normalize_self_projections;
pub use supers::check_impl_supers;
pub(crate) use fnptr::{lub_items_fit, lub_shapes_fit, paired_slot_regions, ptr_free};

/// The variance of a type position.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Variance {
    Co,
    Contra,
    Inv,
    /// Unused: no constraint. The bottom of `join`.
    Bi,
}

impl Variance {
    /// The variance of a position of variance `inner` inside one of variance `self`.
    pub fn then(self, inner: Variance) -> Variance {
        use Variance::*;
        match (self, inner) {
            (Bi, _) | (_, Bi) => Bi,
            (Inv, _) | (_, Inv) => Inv,
            (Co, x) => x,
            (Contra, Co) => Contra,
            (Contra, Contra) => Co,
        }
    }
    /// The variance of a parameter used at both positions.
    pub fn join(self, o: Variance) -> Variance {
        use Variance::*;
        match (self, o) {
            (Bi, x) | (x, Bi) => x,
            (a, b) if a == b => a,
            _ => Inv,
        }
    }
}

/// How dropping a value of an Adt touches values of one of its type params
/// (drop check, ARCH 5.4): not at all, by dropping them (their own drop check
/// applies), or through a user `Drop` impl that may read all of them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DropMode {
    None,
    Owned,
    All,
}

impl DropMode {
    /// The mode of a position inside a position of mode `self`.
    fn then(self, inner: DropMode) -> DropMode {
        match (self, inner) {
            (DropMode::None, _) | (_, DropMode::None) => DropMode::None,
            (DropMode::All, _) | (_, DropMode::All) => DropMode::All,
            _ => DropMode::Owned,
        }
    }
    fn join(self, o: DropMode) -> DropMode {
        match (self, o) {
            (DropMode::All, _) | (_, DropMode::All) => DropMode::All,
            (DropMode::Owned, _) | (_, DropMode::Owned) => DropMode::Owned,
            _ => DropMode::None,
        }
    }
}

/// The region signature of one fn: params (self first) and return with regions
/// kept, in the shape of the erased types in `FnInfo`. Universal region `i` is
/// `Region::Param(i)`; `'static` is `Region::Static`. `facts` are the known
/// outlives relations `'a: 'b` between universals (from where clauses; implied
/// bounds of the signature types are added when a body is checked).
#[derive(Clone, Debug)]
pub struct RegionSig {
    pub n_univ: u32,
    pub params: Vec<Ty>,
    pub ret: Ty,
    pub facts: Vec<(Region, Region)>,
    /// Display names of the universals, for diagnostics (`'a`, or the
    /// parameter an elided region sits in).
    pub names: Vec<String>,
    /// Per named lifetime (universals `0..early.len()`): early-bound.
    pub early: Vec<bool>,
    /// The `Fn*(A..) -> R` bounds on the type params of the fn, its impl,
    /// or its trait, with regions (see `FnBound`).
    pub fn_bounds: Vec<FnBound>,
    /// The `T: Tr<'a, ..>` bounds on type params (the fn's, its impl's,
    /// its trait's, and `impl Tr<'a>` arguments) for traits with lifetime
    /// params, with the written lifetime args (see `TraitLts`).
    pub trait_bounds: Vec<TraitLts>,
    /// The `I: Tr<Item = X>` bounds on type params (`param`, trait, `X`
    /// with regions; an elided region is `Region::Bound`). A call relates
    /// the `Iterator`/`IntoIterator` ones (`item_bound_equate`).
    pub item_bounds: Vec<(u32, DefId, Ty)>,
    /// The universals (`Region::Param` indices) a return-position `impl
    /// Trait` with a `use<..>` list captures (check/use_caps.rs); None
    /// when it captures every one.
    pub opaque_caps: Option<Vec<u32>>,
    /// A method's impl header types (Self and the trait's type args),
    /// regioned: their outlives requirements are implied bounds of the
    /// method too (`check::outlives`).
    pub header: Vec<Ty>,
    /// The trait and assoc-eq bounds of the fn, its impl, and its trait
    /// (a trait method also has its implicit `Self: Tr<P..>`), regions
    /// kept. A call replays the impl each one selects (`replay_bounds`).
    pub bounds: Vec<Predicate>,
}

impl RegionSig {
    /// The signature of a body with no parameters whose value has type
    /// `ret` (every region `'static`): a const or static initializer, or
    /// an anonymous const (check/const_body.rs, lower.rs `check_anon_consts`).
    pub fn const_value(ret: Ty) -> RegionSig {
        RegionSig {
            n_univ: 0,
            params: Vec::new(),
            ret,
            facts: Vec::new(),
            names: Vec::new(),
            early: Vec::new(),
            fn_bounds: Vec::new(),
            trait_bounds: Vec::new(),
            item_bounds: Vec::new(),
            opaque_caps: None,
            header: Vec::new(),
            bounds: Vec::new(),
        }
    }
}

/// A bound `T: Tr<'a, ..>` on type param `param` for a trait with lifetime
/// params: the lifetime args as written (`Region::Param` of the fn's
/// universals, or `Region::Static`). A call of a `Tr` method through `T`
/// instantiates the trait's lifetimes with them, and a call that binds
/// `T` replays the selected impl's lifetimes against them.
#[derive(Clone, Debug)]
pub struct TraitLts {
    pub param: u32,
    pub trait_def: DefId,
    pub lifetimes: Vec<Region>,
}

/// One impl of a trait with lifetime params (W-BORROW): its regioned Self
/// type and the lifetime args of its trait ref, over the impl's lifetimes
/// (`impl Tr<'static> for S`: `[Static]`; `impl<'d> Tr<'d> for S<'d>`:
/// `[Param(0)]`, matched through Self).
#[derive(Clone, Debug)]
pub struct ImplHead {
    pub self_ty: Ty,
    pub trait_lifetimes: Vec<Region>,
    /// The impl's own bounds on its type params for traits with lifetime
    /// params (`impl<'a, T: Tr<'a>> Tr<'a> for Wrap<T>`), replayed
    /// through the parts of Self they name (`trait_lts_for`).
    pub where_lts: Vec<TraitLts>,
}

/// One trait impl's header and where-clauses with regions kept, for any
/// trait: a bound that selects the impl gives the bound's types the
/// header's regions (`impl Tk<&'static u32> for S`; `impl<'x> Tk<&'x u32,
/// &'x u32> for S` ties two). Collect keeps the impls `wanted` says.
#[derive(Clone, Debug)]
pub struct ImplRegions {
    /// Self, then the trait's type args.
    pub header: Vec<Ty>,
    /// `'a: 'b` between the impl's lifetimes (`b == STATIC_FACT`: `'static`).
    pub facts: Vec<(u32, u32)>,
    /// The impl's trait, assoc-eq and outlives where-clauses.
    pub preds: Vec<Predicate>,
    /// The impl's associated type values, by name.
    pub assoc: Vec<(crate::intern::Sym, Ty)>,
}

/// A `F: Fn*(A..) -> R` bound on a type param, with regions: a lifetime
/// the bound writes as itself (the fn's universal or `'static`), an elided
/// one `Region::Bound` (higher-ranked by the sugar). Closures passed for
/// `F` (`link_bound_closure`) and calls through `F` in the body
/// (`call_fn_bound`) follow it.
#[derive(Clone, Debug)]
pub struct FnBound {
    /// The type param's index, or `RPIT_PARAM` for a bound of the fn's
    /// return-position `impl Fn*(..) -> R`.
    pub param: u32,
    pub inputs: Vec<Ty>,
    /// The written output type (`-> R`); `None` for `()`.
    pub output: Option<Ty>,
}

/// `FnBound::param` of a return-position `impl Fn*` bound
/// (`OpaqueInfo::fn_outs`): no type param has it.
pub const RPIT_PARAM: u32 = u32::MAX;

/// The borrow checker's side table of region signatures (W-BORROW, ARCH 5),
/// filled by collect. Read-only after collect, apart from the Adt tables that
/// are computed on first use.
#[derive(Default)]
pub struct RegionTables {
    /// Source fns and methods, by local def.
    pub fns: FxMap<LocalDefId, RegionSig>,
    /// Trait method signatures by method def (the stubs' callee signatures).
    pub trait_methods: FxMap<DefId, RegionSig>,
    /// Fns whose return-position `impl Trait` has a `use<..>` list, by
    /// local def: their region signature (`RegionSig::opaque_caps`; the
    /// return is a placeholder). Only the opaque rules read it (the
    /// definer's own signature, `captured_args`); calls keep the opaque
    /// rule, as for any `impl Trait` fn (`fns` has none of them).
    pub opaque_sigs: FxMap<LocalDefId, RegionSig>,
    /// Regioned field types of each user Adt template, by def: per variant,
    /// per field, with the Adt's lifetime params as `Region::Param(i)`.
    pub adt_fields: FxMap<DefId, Vec<Vec<Ty>>>,
    /// The headers of impls of traits with lifetime params, by impl def.
    pub impl_heads: FxMap<DefId, ImplHead>,
    /// Trait impls whose header or where-clauses may tie regions, by impl def.
    pub impl_regions: FxMap<DefId, ImplRegions>,
    /// The trait bounds of user Adts (`struct W<Q: Tk<A>, A>`), regions
    /// kept, by def: building a value replays them (`replay_adt`).
    pub adt_bounds: FxMap<DefId, Vec<Predicate>>,
    /// The trait bounds of user traits (supertraits and where-clauses),
    /// regions kept, by def: each impl owes them by regions too
    /// (`check_impl_supers`).
    pub trait_preds: FxMap<DefId, Vec<Predicate>>,
    /// Declared outlives facts between an Adt's lifetime params
    /// (`struct H<'a, 'b: 'a>`), by def: `(x, y)` is `'x: 'y` by param
    /// index, `y == STATIC_FACT` is `'static`. Every use of the type must
    /// meet them (well-formedness), and a signature that names the type
    /// may assume them (implied bounds).
    pub adt_facts: FxMap<DefId, Vec<(u32, u32)>>,
    /// Per user Adt, the outlives requirements every use must meet, over
    /// its own params (`check::outlives::infer_adts`): `(T, 'a)` is `T: 'a`.
    pub adt_outlives: FxMap<DefId, Vec<(GenericArg, Region)>>,
    /// Items whose written types `check::outlives::check_all` checks,
    /// recorded at collect.
    pub outlives_items: Vec<crate::check::outlives::Item>,
    adts: std::sync::OnceLock<AdtTables>,
    /// The trait method of each trait method stub (the reverse of
    /// `GenTables::trait_method_stubs`), built on first use.
    stub_methods: std::sync::OnceLock<FxMap<LocalDefId, DefId>>,
    /// Per trait, its impls with `X: 'static` where-clauses (the impl and
    /// those params), built on first use (`Builder::impl_static_edges`).
    static_impls: std::sync::OnceLock<FxMap<DefId, Vec<(crate::traits::index::ImplId, Vec<u32>)>>>,
    /// The traits whose impl selection may tie regions, built on first
    /// use (`replay_traits`).
    replay_traits: std::sync::OnceLock<FxSet<DefId>>,
}

/// Per user Adt template: variance and drop mode of each generic param, by
/// param index (const params are `Bi` and `None`).
#[derive(Default)]
struct AdtTables {
    variance: FxMap<DefId, Vec<Variance>>,
    drop: FxMap<DefId, Vec<DropMode>>,
    /// Per lifetime param of each user Adt template (W-BORROW): its
    /// variance, and whether dropping the Adt may need it live.
    region_variance: FxMap<DefId, Vec<Variance>>,
    region_drop: FxMap<DefId, Vec<DropMode>>,
    /// Some Adt's drop may read a param (a `Drop` impl, or a field that
    /// owns a trait object): bodies must then compute drop-liveness.
    any_drop: bool,
}

impl RegionTables {
    /// The Adt tables, computed once from the program's Adt templates.
    fn adts(&self, p: &Program) -> &AdtTables {
        self.adts.get_or_init(|| AdtTables::compute(p))
    }

    /// The impls of `trait_def` with `X: 'static` where-clauses.
    fn static_impls(&self, p: &Program, trait_def: DefId) -> &[(crate::traits::index::ImplId, Vec<u32>)] {
        let all = self.static_impls.get_or_init(|| {
            let mut m: FxMap<DefId, Vec<(crate::traits::index::ImplId, Vec<u32>)>> = FxMap::default();
            for (id, rec) in p.gx.index.all_impls() {
                let ks: Vec<u32> = rec
                    .generics
                    .predicates
                    .iter()
                    .filter_map(|pr| match pr {
                        Predicate::TypeOutlives(x, Region::Static) => match p.tys.kind(*x) {
                            TyKind::Param(k) => Some(k.0),
                            _ => None,
                        },
                        _ => None,
                    })
                    .collect();
                if !ks.is_empty() {
                    m.entry(rec.trait_def).or_default().push((id, ks));
                }
            }
            m
        });
        all.get(&trait_def).map_or(&[], |v| v.as_slice())
    }

    /// The trait method a stub fn stands for (a stub has its own def).
    /// The region signature body `f` is checked against: its own, its
    /// template's (an instance), or its trait method's (a trait default
    /// body: a template fn with the trait method's def, or its stub).
    pub fn body_sig(&self, p: &Program, f: LocalDefId) -> Option<&RegionSig> {
        let of = |g: LocalDefId| {
            self.fns
                .get(&g)
                .or_else(|| p.fn_defs.get(g.0 as usize).and_then(|d| self.trait_methods.get(d)))
                .or_else(|| self.stub_method(p, g).and_then(|m| self.trait_methods.get(&m)))
        };
        of(f).or_else(|| of(p.gx.instances.get(&f)?.template_local?))
    }

    /// The signature body `f`'s own universals come from (`own_sig`):
    /// `body_sig`, else `opaque_sig` (a fn whose `impl Trait` return has a
    /// `use<..>` list or a lifetime bound).
    pub fn own_body_sig(&self, p: &Program, f: LocalDefId) -> Option<&RegionSig> {
        self.body_sig(p, f).or_else(|| self.opaque_sig(p, f))
    }

    /// `opaque_sigs` for `f`, or for the template of instance `f`.
    pub fn opaque_sig(&self, p: &Program, f: LocalDefId) -> Option<&RegionSig> {
        self.opaque_sigs.get(&f).or_else(|| self.opaque_sigs.get(&p.gx.instances.get(&f)?.template_local?))
    }

    fn stub_method(&self, p: &Program, f: LocalDefId) -> Option<DefId> {
        self.stub_methods.get_or_init(|| p.gx.trait_method_stubs.iter().map(|(&m, &s)| (s, m)).collect()).get(&f).copied()
    }
}

/// The user Adt templates: (def, template id), skipping builtins and
/// materialized instances.
fn adt_templates(p: &Program) -> Vec<(DefId, AdtId)> {
    let mut out = Vec::new();
    for i in 0..p.adts.len() {
        let id = AdtId(i as u32);
        if let Some(def) = p.defs.def_of_adt(id)
            && p.defs.local_adt(def) == Some(id)
        {
            out.push((def, id));
        }
    }
    out
}

/// The number of generic params an Adt def's args carry (types and consts).
fn adt_param_count(p: &Program, def: DefId) -> usize {
    p.defs.generics_of(def).map_or(0, |g| g.params.len())
}

impl AdtTables {
    /// Variance and drop mode of every user Adt template's params, by
    /// fixpoint over field types (ARCH 5.3): start unused, join the variance
    /// of each use, and iterate until no table changes. Recursive types
    /// converge because both lattices are finite.
    fn compute(p: &Program) -> AdtTables {
        let templates = adt_templates(p);
        let mut t = AdtTables::default();
        for &(def, _) in &templates {
            let n = adt_param_count(p, def);
            t.variance.insert(def, vec![Variance::Bi; n]);
            let has_drop = super::drop_heads(p).contains(&def);
            t.drop.insert(def, vec![if has_drop { DropMode::All } else { DropMode::None }; n]);
        }
        for &(def, _) in &templates {
            let n = p.gx.adt_lifetimes.get(&def).map_or(0, |v| v.len());
            let has_drop = super::drop_heads(p).contains(&def);
            t.region_variance.insert(def, vec![Variance::Bi; n]);
            t.region_drop.insert(def, vec![if has_drop { DropMode::All } else { DropMode::None }; n]);
        }
        loop {
            let mut changed = false;
            for &(def, id) in &templates {
                let n = adt_param_count(p, def);
                let mut var = vec![Variance::Bi; n];
                let mut drop = t.drop[&def].clone();
                for v in &p.adt(id).variants {
                    for f in &v.fields {
                        t.param_uses(p, f.ty, Variance::Co, DropMode::Owned, &mut var, &mut drop);
                    }
                }
                // `PhantomData<T>` acts as a field of type T (std source,
                // W-STD-C): covariant, and owned for drop.
                if p.is_phantom_adt(id) {
                    var.iter_mut().for_each(|x| *x = x.join(Variance::Co));
                    drop.iter_mut().for_each(|x| *x = x.join(DropMode::Owned));
                }
                if t.variance[&def] != var {
                    t.variance.insert(def, var);
                    changed = true;
                }
                if t.drop[&def] != drop {
                    t.drop.insert(def, drop);
                    changed = true;
                }
                // Lifetime params, from the regioned field types.
                let nr = t.region_variance[&def].len();
                if nr > 0 {
                    let mut rvar = vec![Variance::Bi; nr];
                    let mut rdrop = t.region_drop[&def].clone();
                    if let Some(fields) = p.regions.adt_fields.get(&def) {
                        for v in fields {
                            for &f in v {
                                t.region_uses(p, f, Variance::Co, DropMode::Owned, &mut rvar, &mut rdrop);
                            }
                        }
                    }
                    if t.region_variance[&def] != rvar {
                        t.region_variance.insert(def, rvar);
                        changed = true;
                    }
                    if t.region_drop[&def] != rdrop {
                        t.region_drop.insert(def, rdrop);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        t.any_drop = t.drop.values().chain(t.region_drop.values()).flatten().any(|&m| m == DropMode::All);
        t
    }

    /// Joins into `var` and `drop` the uses of each lifetime param
    /// (`Region::Param(i)`) in regioned field type `ty`, at variance `v`
    /// and drop mode `m`: a reference's region at the reference's own
    /// position (only a `Drop` impl reading through it needs it live), an
    /// Adt's region args at that Adt's param variance and drop mode.
    fn region_uses(&self, p: &Program, ty: Ty, v: Variance, m: DropMode, var: &mut [Variance], drop: &mut [DropMode]) {
        let note = |r: Region, v: Variance, m: DropMode, var: &mut [Variance], drop: &mut [DropMode]| {
            if let Region::Param(i) = r {
                if let Some(x) = var.get_mut(i as usize) {
                    *x = x.join(v);
                }
                if let Some(x) = drop.get_mut(i as usize) {
                    *x = x.join(if m == DropMode::All { DropMode::All } else { DropMode::None });
                }
            }
        };
        match p.tys.kind(ty) {
            TyKind::Ref(r, mt, inner) => {
                note(r, v, m, var, drop);
                let iv = if mt.is_mut() { Variance::Inv } else { Variance::Co };
                self.region_uses(p, inner, v.then(iv), if m == DropMode::All { DropMode::All } else { DropMode::None }, var, drop);
            }
            TyKind::RawPtr(mt, inner) => {
                let iv = if mt.is_mut() { Variance::Inv } else { Variance::Co };
                self.region_uses(p, inner, v.then(iv), DropMode::None, var, drop);
            }
            TyKind::Tuple(ts) => {
                for &e in p.tys.tys_of(ts) {
                    self.region_uses(p, e, v, m, var, drop);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) => self.region_uses(p, e, v, m, var, drop),
            TyKind::Adt(def, args) => {
                let (mut k, mut j) = (0usize, 0usize);
                for g in p.tys.args(args) {
                    match *g {
                        GenericArg::Lifetime(r) => {
                            let rv = self.region_variance.get(&def).and_then(|x| x.get(k)).copied().unwrap_or(Variance::Inv);
                            let rm = match builtin_region_drop(&p.tys, ty) {
                                Some(m) => m,
                                None => self.region_drop.get(&def).and_then(|x| x.get(k)).copied().unwrap_or(DropMode::All),
                            };
                            let mm = if m == DropMode::None { DropMode::None } else { m.join(rm) };
                            note(r, v.then(rv), mm, var, drop);
                            k += 1;
                        }
                        GenericArg::Ty(e) => {
                            let (pv, pm) = self.arg_modes(p, def, j);
                            self.region_uses(p, e, v.then(pv), m.then(pm), var, drop);
                            j += 1;
                        }
                        GenericArg::Const(_) => j += 1,
                    }
                }
            }
            // A dyn's object lifetime: covariant (`dyn Tr + 'long` is a
            // `dyn Tr + 'short`), drop-visible (an unknown destructor).
            // The regions of its trait args are invariant (R11).
            TyKind::Dyn(_, r) => {
                let dm = if m == DropMode::None { DropMode::None } else { DropMode::All };
                note(r, v.then(Variance::Co), dm, var, drop);
                for e in dyn_arg_tys(&p.tys, ty) {
                    self.region_uses(p, e, v.then(Variance::Inv), dm, var, drop);
                }
            }
            _ => {
                // A region inside anything else (fn pointers, closures)
                // is held invariant and drop-visible: the safe answer.
                let mut rs = Vec::new();
                regions_of(&p.tys, ty, &mut rs);
                for r in rs {
                    note(r, Variance::Inv, if m == DropMode::None { DropMode::None } else { DropMode::All }, var, drop);
                }
            }
        }
    }

    /// The variance and drop mode of lifetime param `k` of Adt `def`.
    fn region_modes(&self, def: DefId, k: usize) -> (Variance, DropMode) {
        let v = self.region_variance.get(&def).and_then(|x| x.get(k)).copied().unwrap_or(Variance::Inv);
        let m = self.region_drop.get(&def).and_then(|x| x.get(k)).copied().unwrap_or(DropMode::All);
        (v, m)
    }

    /// Joins into `var` and `drop` the uses of each `Param(i)` in field type `ty`
    /// at position variance `v` and drop mode `m`.
    fn param_uses(&self, p: &Program, ty: Ty, v: Variance, m: DropMode, var: &mut [Variance], drop: &mut [DropMode]) {
        match p.tys.kind(ty) {
            TyKind::Param(i) => {
                if let Some(x) = var.get_mut(i.0 as usize) {
                    *x = x.join(v);
                }
                if let Some(x) = drop.get_mut(i.0 as usize) {
                    *x = x.join(m);
                }
            }
            TyKind::Ref(_, mt, inner) => {
                let iv = if mt.is_mut() { Variance::Inv } else { Variance::Co };
                self.param_uses(p, inner, v.then(iv), DropMode::None, var, drop);
            }
            TyKind::RawPtr(mt, inner) => {
                let iv = if mt.is_mut() { Variance::Inv } else { Variance::Co };
                self.param_uses(p, inner, v.then(iv), DropMode::None, var, drop);
            }
            TyKind::Tuple(ts) => {
                for &e in p.tys.tys_of(ts) {
                    self.param_uses(p, e, v, m, var, drop);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) => self.param_uses(p, e, v, m, var, drop),
            TyKind::Adt(def, args) => {
                for (j, g) in p.tys.args(args).iter().enumerate() {
                    if let GenericArg::Ty(e) = g {
                        let (pv, pm) = self.arg_modes(p, def, j);
                        self.param_uses(p, *e, v.then(pv), m.then(pm), var, drop);
                    }
                }
            }
            TyKind::FnPtr(sig) => {
                let s = p.tys.sig(sig).value;
                for &i in p.tys.tys_of(s.inputs) {
                    self.param_uses(p, i, v.then(Variance::Contra), DropMode::None, var, drop);
                }
                self.param_uses(p, s.output, v, DropMode::None, var, drop);
            }
            // Anything else that names a param (closures, fn items, projections,
            // dyn, opaque types) is held invariant and fully drop-visible: the
            // conservative answer.
            _ => {
                if p.tys.flags(ty).contains_param() {
                    for x in var.iter_mut() {
                        *x = x.join(Variance::Inv);
                    }
                    if m != DropMode::None {
                        for x in drop.iter_mut() {
                            *x = x.join(DropMode::All);
                        }
                    }
                }
            }
        }
    }

    /// The variance and drop mode of arg `j` of Adt `def`: builtin containers
    /// are covariant and own their elements; a user Adt answers from the table
    /// (unknown defs are invariant and fully drop-visible).
    fn arg_modes(&self, p: &Program, def: DefId, j: usize) -> (Variance, DropMode) {
        use crate::ty::iter::IterKind;
        match p.tys.builtins().kind_of(def) {
            // `mpsc::Iter<'a, T>` holds `&'a Receiver<T>` (invariant in
            // `T`); `mpsc::IntoIter<T>` owns the receiver, whose `Drop`
            // reads `T` (W-THREADS).
            Some(BuiltinTy::Iter(IterKind::RecvIter | IterKind::RecvTryIter)) => return (Variance::Inv, DropMode::None),
            Some(BuiltinTy::Iter(IterKind::RecvIntoIter)) => return (Variance::Inv, DropMode::All),
            // `slice::IterMut<'a, T>` holds `&'a mut [T]`: invariant in `T`.
            Some(BuiltinTy::Iter(IterKind::SliceIterMut)) => return (Variance::Inv, DropMode::None),
            Some(BuiltinTy::Iter(IterKind::SliceIter)) => return (Variance::Co, DropMode::None),
            // `hash_map::IterMut<'a, K, V>` and `ValuesMut` hold `&'a mut V`
            // (W-STD-B): invariant in V, covariant in K, no drop.
            Some(BuiltinTy::Iter(IterKind::MapIterMut | IterKind::MapValuesMut)) => {
                return if j == 1 { (Variance::Inv, DropMode::None) } else { (Variance::Co, DropMode::None) };
            }
            // The hashed collections (W-STD-B): HashMap and HashSet are
            // covariant and own their elements (hashbrown's RawTable);
            // `BuildHasherDefault<H>` holds `PhantomData<fn() -> H>`; an
            // Entry holds `&'a mut HashMap<K, V>`: invariant, and it owns
            // only its probe key.
            Some(BuiltinTy::Hash(k)) => {
                use crate::ty::hash::HashTy;
                return match k {
                    HashTy::HashMap | HashTy::HashSet => (Variance::Co, DropMode::Owned),
                    HashTy::BuildHasherDefault => (Variance::Co, DropMode::None),
                    HashTy::Entry | HashTy::VacantEntry => (Variance::Inv, if j == 0 { DropMode::Owned } else { DropMode::None }),
                    // `OccupiedEntry` holds the map's `&'a mut` and owns nothing.
                    HashTy::OccupiedEntry => (Variance::Inv, DropMode::None),
                    HashTy::RandomState | HashTy::DefaultHasher => (Variance::Inv, DropMode::Owned),
                    // The C forms of the iterators are never types (no def).
                    HashTy::IterPairs
                    | HashTy::IterKeys
                    | HashTy::IterValues
                    | HashTy::IntoPairs
                    | HashTy::IntoKeys
                    | HashTy::IntoValues
                    | HashTy::DrainPairs
                    | HashTy::DrainKeys => {
                        (Variance::Inv, DropMode::All)
                    }
                };
            }
            // Owning containers and the other iterators: covariant, their
            // drop may reach the elements. Exhaustive on purpose: a new
            // builtin picks its variance here (a `Cell`-like type is
            // invariant; covariance there would be unsound).
            Some(
                BuiltinTy::String
                | BuiltinTy::Vec
                | BuiltinTy::Option
                | BuiltinTy::Result
                | BuiltinTy::Boxed
                | BuiltinTy::Rc
                | BuiltinTy::Chars
                | BuiltinTy::Iter(_)
                | BuiltinTy::Weak,
            ) => return (Variance::Co, DropMode::Owned),
            // `fmt` types (W-STD-B) and `ExitCode` take no type args.
            Some(BuiltinTy::Fmt(_) | BuiltinTy::ExitCode) => return (Variance::Inv, DropMode::Owned),
            // `LocalKey<T>` holds an `fn` that returns `*const T`:
            // covariant, and it never drops a `T`; `AccessError` takes no
            // type args (W-TLS).
            Some(BuiltinTy::LocalKey) => return (Variance::Co, DropMode::None),
            Some(BuiltinTy::AccessError) => return (Variance::Inv, DropMode::Owned),
            // `RefMut<'b, T>` acts as `&'b mut T`, `Ref<'b, T>` as `&'b T`;
            // neither drops the `T` (W-STD-A).
            Some(BuiltinTy::RefMutGuard) => return (Variance::Inv, DropMode::None),
            Some(BuiltinTy::RefGuard) => return (Variance::Co, DropMode::None),
            // Interior mutability: `Cell<T>` and `RefCell<T>` are invariant.
            Some(BuiltinTy::Cell | BuiltinTy::RefCell) => return (Variance::Inv, DropMode::Owned),
            // `Arc<T>` and `sync::Weak<T>` are like `Rc` and `rc::Weak`;
            // the atomics take no type args (W-THREADS).
            Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::Arc | crate::ty::sync::SyncTy::ArcWeak)) => return (Variance::Co, DropMode::Owned),
            // `MutexGuard` and `RwLockWriteGuard` act as `&'b mut T`,
            // `RwLockReadGuard` as `&'b T` (its `NonNull<T>` is
            // covariant); none drops the `T`. `PoisonError<T>` owns its
            // `T`. The locks are invariant (`UnsafeCell`).
            Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::MutexGuard | crate::ty::sync::SyncTy::RwLockWriteGuard)) => return (Variance::Inv, DropMode::None),
            Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::RwLockReadGuard)) => return (Variance::Co, DropMode::None),
            Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::PoisonError)) => return (Variance::Co, DropMode::Owned),
            // The channel ends and join handles have std `Drop` impls with
            // no `#[may_dangle]`: their drop may read every `T` region.
            Some(BuiltinTy::Sync(
                crate::ty::sync::SyncTy::Sender
                | crate::ty::sync::SyncTy::SyncSender
                | crate::ty::sync::SyncTy::Receiver
                | crate::ty::sync::SyncTy::JoinHandle
                | crate::ty::sync::SyncTy::ScopedJoinHandle,
            )) => return (Variance::Inv, DropMode::All),
            // `ScopedJoinHandle<'scope, T>` owns its `T` (an `Arc` of a
            // packet with an `UnsafeCell`: invariant).
            Some(BuiltinTy::Sync(_)) => return (Variance::Inv, DropMode::Owned),
            None => {}
        }
        let v = self.variance.get(&def).and_then(|v| v.get(j)).copied().unwrap_or(Variance::Inv);
        let m = self.drop.get(&def).and_then(|d| d.get(j)).copied().unwrap_or(DropMode::All);
        (v, m)
    }
}

/// The number of region params an Adt type carries ahead of its type args:
/// a user Adt's declared lifetimes, or one for the builtin borrowing
/// iterators (`Chars`, `slice::Iter`, `slice::IterMut`) and the `RefCell`
/// guards (`Ref`, `RefMut`), whose erased types drop the lifetime.
/// The drop mode of a builtin Adt's lifetimes (None for any other type):
/// a guard's drop gives its borrow back and a `Drain`'s moves the tail
/// back, so they use it (rustc E0499 on `let d = v.drain(..); v.push(1)`);
/// the other builtins have no destructor that reads their borrow.
fn builtin_region_drop(tys: &impl TyIntern, t: Ty) -> Option<DropMode> {
    use crate::ty::iter::IterKind;
    let b = tys.builtin_of(t)?;
    let uses = tys.guard_elem(t).is_some() || matches!(b, BuiltinTy::Iter(IterKind::VecDrain | IterKind::StringDrain));
    Some(if uses { DropMode::All } else { DropMode::None })
}

fn adt_regions(p: &Program, tys: &impl TyIntern, t: Ty) -> u32 {
    adt_region_count(&p.gx.adt_lifetimes, tys, t)
}

/// `adt_regions` from the user Adts' lifetime params alone (check uses it
/// before a `Program` exists, `fnptr::paired_slot_regions`).
pub(crate) fn adt_region_count(adt_lifetimes: &FxMap<DefId, Vec<crate::intern::Sym>>, tys: &impl TyIntern, t: Ty) -> u32 {
    use crate::ty::iter::IterKind;
    match tys.builtin_of(t) {
        Some(
            BuiltinTy::Chars
            | BuiltinTy::Iter(
                IterKind::SliceIter
                | IterKind::SliceIterMut
                | IterKind::RecvIter
                | IterKind::RecvTryIter
                | IterKind::Windows
                | IterKind::Chunks
                | IterKind::ChunksMut
                | IterKind::ChunksExact
                | IterKind::ChunksExactMut
                | IterKind::SliceSplit
                | IterKind::ChunkBy
                | IterKind::ChunkByMut
                | IterKind::SliceSplitMut
                | IterKind::Utf8Chunks
                | IterKind::Utf8Chunk
                | IterKind::CharIndices
                | IterKind::VecDrain
                | IterKind::StringDrain
                | IterKind::OptionIter
                | IterKind::OptionIterMut
                | IterKind::ResultIter
                | IterKind::ResultIterMut,
            )
            | BuiltinTy::Iter(IterKind::StrSplit | IterKind::StrMatches | IterKind::EncodeUtf16)
            | BuiltinTy::RefGuard
            | BuiltinTy::RefMutGuard,
        ) => return 1,
        // The borrowing hash iterators hold `&'a` (or `&'a mut`) of their table (W-STD-B).
        Some(BuiltinTy::Iter(k)) if k.is_hash() && !k.is_hash_owning() => return 1,
        // A Debug builder holds `&mut Formatter`, a map Entry `&mut` its
        // map (W-STD-B). An `Arguments<'a>` borrows its format
        // arguments, so it holds one region too (R9).
        Some(BuiltinTy::Fmt(k)) if k.is_builder() || k == crate::ty::fmt::FmtTy::Arguments => return 1,
        // The lock guards borrow their lock (W-THREADS).
        Some(BuiltinTy::Sync(k)) if k.regions() > 0 => return k.regions(),
        Some(BuiltinTy::Hash(crate::ty::hash::HashTy::Entry | crate::ty::hash::HashTy::OccupiedEntry | crate::ty::hash::HashTy::VacantEntry)) => return 1,
        Some(_) => return 0,
        None => {}
    }
    match tys.kind(t) {
        // A lifetime of a dyn's `Fn*` sugar that the object binds itself
        // (`Lifetime(DYN_LATE)`, R11) is no slot.
        TyKind::Adt(def, args) => {
            let late = tys.args(args).iter().filter(|g| matches!(g, GenericArg::Lifetime(r) if *r == crate::ty::DYN_LATE)).count() as u32;
            adt_lifetimes.get(&def).map_or(0, |v| v.len() as u32).saturating_sub(late)
        }
        _ => 0,
    }
}

/// Per lifetime arg of an Adt in check's types: a `DYN_LATE` mark (R11).
/// Empty for an Adt with no lifetime args (every region a slot).
fn adt_late_marks(tys: &impl TyIntern, args: ArgsId) -> Vec<bool> {
    tys.args(args).iter().filter_map(|g| if let GenericArg::Lifetime(r) = g { Some(*r == crate::ty::DYN_LATE) } else { None }).collect()
}

/// The pointees of two pointers whose object lifetime a coercion may
/// shorten (`Builder::relate`): with `refs`, `&`/`&mut dyn Tr` with free
/// regions, also through a `RefCell` or lock whose value is the dyn
/// (`&RefCell<dyn Tr + 'a>` to `&RefCell<dyn Tr + 'b>`: std's unsizing
/// goes through a struct's last field; neither has region slots of its
/// own); with `guards`, the same `RefCell` guard (`Ref`, `RefMut`) over
/// `dyn Tr`.
fn outer_dyn_pointees(tys: &impl TyIntern, a: Ty, b: Ty, refs: bool, guards: bool) -> Option<(Ty, Ty)> {
    let cell = |t: Ty| tys.refcell_elem(t).or_else(|| tys.lock_elem(t).map(|(_, e)| e));
    let (ai, bi) = match (tys.kind(a), tys.kind(b)) {
        (TyKind::Ref(ra, _, ai), TyKind::Ref(rb, _, bi)) if refs && !bound(ra) && !bound(rb) => match (cell(ai), cell(bi)) {
            (Some(x), Some(y)) if tys.adt_parts(ai).map(|p| p.0) == tys.adt_parts(bi).map(|p| p.0) => (x, y),
            _ => (ai, bi),
        },
        (TyKind::Adt(da, xa), TyKind::Adt(db, xb))
            if guards && da == db && matches!(tys.builtin_of(a), Some(BuiltinTy::RefGuard | BuiltinTy::RefMutGuard)) =>
        {
            (tys.args(xa).iter().find_map(|g| g.as_ty())?, tys.args(xb).iter().find_map(|g| g.as_ty())?)
        }
        _ => return None,
    };
    matches!((tys.kind(ai), tys.kind(bi)), (TyKind::Dyn(..), TyKind::Dyn(..))).then_some((ai, bi))
}

/// The variance of a builtin type's region params: covariant, but for
/// `thread::Scope<'scope, 'env>`, invariant in both (std's
/// `PhantomData<&'scope mut &'scope ()>`), which pins a scoped spawn's
/// `'scope` to the scope closure's whole body.
fn builtin_region_variance(tys: &impl TyIntern, t: Ty) -> Variance {
    if crate::ty::sync::sync_kind(tys, t) == Some(crate::ty::sync::SyncTy::Scope) { Variance::Inv } else { Variance::Co }
}

/// True when a drop of a value of type `t` drops a `RefCell` or lock
/// guard, whose own drop uses its borrow (Rust's `BorrowRef` is `Drop`),
/// or a std type whose `Drop` reads its `T` (a channel end, a join
/// handle: no `#[may_dangle]`; W-THREADS).
fn drops_guard(tys: &impl TyIntern, t: Ty) -> bool {
    use crate::ty::sync::SyncTy as S;
    match tys.kind(t) {
        TyKind::Adt(_, args) => {
            tys.guard_elem(t).is_some()
                || matches!(crate::ty::sync::sync_kind(tys, t), Some(S::Sender | S::SyncSender | S::Receiver | S::JoinHandle | S::ScopedJoinHandle))
                || tys.builtin_of(t) == Some(BuiltinTy::Iter(crate::ty::iter::IterKind::RecvIntoIter))
                || (!matches!(tys.builtin_of(t), Some(BuiltinTy::Weak | BuiltinTy::Sync(crate::ty::sync::SyncTy::ArcWeak)))
                    && tys.args(args).iter().any(|g| g.as_ty().is_some_and(|e| drops_guard(tys, e))))
        }
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| drops_guard(tys, e)),
        TyKind::Array(e, _) => drops_guard(tys, e),
        TyKind::Closure(_, args) => closure_fields(tys, args).into_iter().any(|e| drops_guard(tys, e)),
        _ => false,
    }
}

/// True when a value of type `t` owns a trait object (`Box<dyn ..>`,
/// `Rc<dyn ..>`, a closure that captures one), whose unknown destructor
/// may use every region the object holds (rustc drop check).
fn owns_dyn(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Dyn(..) => true,
        TyKind::Adt(_, args) => tys.args(args).iter().any(|g| g.as_ty().is_some_and(|e| owns_dyn(tys, e))),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| owns_dyn(tys, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) => owns_dyn(tys, e),
        TyKind::Closure(_, args) => closure_fields(tys, args).into_iter().any(|e| owns_dyn(tys, e)),
        _ => false,
    }
}

/// True for a late-bound region of a dyn type's `Fn*` sugar (R11): the
/// object binds it itself, so it is no slot of any value.
fn bound(r: Region) -> bool {
    r == crate::ty::DYN_LATE
}

/// The types whose regions are a dyn type's slots after its object
/// lifetime (R11): the principal's type args after Self, then its
/// binding types (`Output`), in order. Those slots are invariant and
/// drop-visible; `DYN_LATE` regions in them are the object's own.
pub(crate) fn dyn_arg_tys(tys: &impl TyIntern, t: Ty) -> Vec<Ty> {
    let TyKind::Dyn(b, _) = tys.kind(t) else { return Vec::new() };
    let Some(pr) = tys.dyn_bounds(b).principal else { return Vec::new() };
    let mut out: Vec<Ty> = tys.args(pr.value.args).iter().skip(1).filter_map(|g| g.as_ty()).collect();
    out.extend(tys.bindings(pr.value.bindings).iter().filter_map(|(_, g)| g.as_ty()));
    out
}

/// True when a local of `body` holds a dyn type with a late-bound place
/// (`DYN_LATE`, R11) or a loose one: the region pass must pair them.
pub(super) fn has_dyn_late(body: &Body) -> bool {
    fn go(tys: &impl TyIntern, t: Ty, depth: u32) -> bool {
        if depth > 32 || tys.flags(t).contains_loose_bound() {
            return depth <= 32;
        }
        match tys.kind(t) {
            TyKind::Dyn(_, r) => bound(r) || dyn_arg_tys(tys, t).into_iter().any(|e| go(tys, e, depth + 1)),
            TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => go(tys, e, depth + 1),
            TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| go(tys, e, depth + 1)),
            TyKind::Adt(_, a) | TyKind::Closure(_, a) => tys.args(a).iter().any(|g| match g {
                GenericArg::Ty(e) => go(tys, *e, depth + 1),
                GenericArg::Lifetime(r) => bound(*r),
                _ => false,
            }),
            _ => false,
        }
    }
    body.locals.iter().any(|l| go(&body.tys, l.ty, 0))
}

/// Type facts the region walks need, over one type store.
pub(super) struct SlotCx<'t, 'p, T: TyIntern> {
    pub tys: &'t T,
    pub p: &'p Program,
    memo: FxMap<Ty, u32>,
}

impl<'t, 'p, T: TyIntern> SlotCx<'t, 'p, T> {
    pub fn new(tys: &'t T, p: &'p Program) -> Self {
        SlotCx { tys, p, memo: FxMap::default() }
    }

    /// The number of region slots of an erased type.
    pub fn slots(&mut self, t: Ty) -> u32 {
        if let Some(&n) = self.memo.get(&t) {
            return n;
        }
        let n = match self.tys.kind(t) {
            TyKind::Ref(r, _, inner) => u32::from(!bound(r)) + self.slots(inner),
            TyKind::Adt(_, args) => {
                let mut n = adt_regions(self.p, self.tys, t);
                for g in self.tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        n += self.slots(e);
                    }
                }
                n
            }
            TyKind::Tuple(ts) => self.tys.tys_of(ts).to_vec().into_iter().map(|e| self.slots(e)).sum(),
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.slots(e),
            TyKind::Closure(_, args) => closure_fields(self.tys, args).into_iter().map(|e| self.slots(e)).sum(),
            // The object lifetime (`dyn Tr + 'o`), then the trait args'.
            TyKind::Dyn(_, r) => u32::from(!bound(r)) + dyn_arg_tys(self.tys, t).into_iter().map(|e| self.slots(e)).sum::<u32>(),
            // A fn pointer type's free region (W-BORROW3).
            TyKind::FnPtr(_) => u32::from(ptr_free(self.tys, t).is_some()),
            _ => 0,
        };
        self.memo.insert(t, n);
        n
    }

    /// The region an erased type keeps at each of its slots (`Erased`, or
    /// `'static` where the erased form kept it), in slot order.
    pub fn slot_regions(&mut self, t: Ty, out: &mut Vec<Region>) {
        match self.tys.kind(t) {
            TyKind::Ref(r, _, inner) => {
                if !bound(r) {
                    out.push(r);
                }
                self.slot_regions(inner, out);
            }
            TyKind::Adt(_, args) => {
                for _ in 0..adt_regions(self.p, self.tys, t) {
                    out.push(Region::Erased);
                }
                for g in self.tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.slot_regions(e, out);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in self.tys.tys_of(ts).to_vec() {
                    self.slot_regions(e, out);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.slot_regions(e, out),
            TyKind::Closure(_, args) => {
                for e in closure_fields(self.tys, args) {
                    self.slot_regions(e, out);
                }
            }
            // A trait bounded by `'static` makes its object lifetime
            // `'static` whatever the default would be (rustc, ARCH 2.8).
            TyKind::Dyn(_, r) => {
                if !bound(r) {
                    out.push(if crate::check::object::dyn_is_static(self.p, self.tys, t) { Region::Static } else { r });
                }
                for e in dyn_arg_tys(self.tys, t) {
                    self.slot_regions(e, out);
                }
            }
            TyKind::FnPtr(_) => out.extend(ptr_free(self.tys, t)),
            _ => {}
        }
    }

    /// Calls `f(slot, variance)` for each slot of `t`, in order, starting at
    /// slot index `at`, where `t` sits at position variance `v`. Returns the
    /// next slot index.
    pub fn each_slot(&mut self, t: Ty, v: Variance, at: u32, f: &mut impl FnMut(u32, Variance)) -> u32 {
        match self.tys.kind(t) {
            TyKind::Ref(r, m, inner) => {
                let mut at = at;
                if !bound(r) {
                    f(at, v);
                    at += 1;
                }
                let iv = if m.is_mut() { Variance::Inv } else { Variance::Co };
                self.each_slot(inner, v.then(iv), at, f)
            }
            TyKind::Adt(def, args) => {
                let mut at = at;
                for k in 0..adt_regions(self.p, self.tys, t) {
                    let rv = if self.tys.builtin_of(t).is_some() { builtin_region_variance(self.tys, t) } else { self.p.regions.adts(self.p).region_modes(def, k as usize).0 };
                    f(at, v.then(rv));
                    at += 1;
                }
                for (j, g) in self.tys.args(args).to_vec().into_iter().enumerate() {
                    if let GenericArg::Ty(e) = g {
                        let (pv, _) = self.p.regions.adts(self.p).arg_modes(self.p, def, j);
                        at = self.each_slot(e, v.then(pv), at, f);
                    }
                }
                at
            }
            TyKind::Tuple(ts) => {
                let mut at = at;
                for e in self.tys.tys_of(ts).to_vec() {
                    at = self.each_slot(e, v, at, f);
                }
                at
            }
            TyKind::Array(e, _) | TyKind::Slice(e) => self.each_slot(e, v, at, f),
            TyKind::RawPtr(m, e) => self.each_slot(e, v.then(if m.is_mut() { Variance::Inv } else { Variance::Co }), at, f),
            TyKind::Closure(_, args) => {
                let mut at = at;
                for e in closure_fields(self.tys, args) {
                    at = self.each_slot(e, Variance::Inv, at, f);
                }
                at
            }
            TyKind::Dyn(_, r) => {
                let mut at = at;
                if !bound(r) {
                    f(at, v.then(Variance::Co));
                    at += 1;
                }
                for e in dyn_arg_tys(self.tys, t) {
                    at = self.each_slot(e, v.then(Variance::Inv), at, f);
                }
                at
            }
            // Held invariant: the free region may sit in input and output
            // places alike (conservative).
            TyKind::FnPtr(_) if ptr_free(self.tys, t).is_some() => {
                f(at, Variance::Inv);
                at + 1
            }
            _ => at,
        }
    }

    /// Marks in `out` (one bool per slot of `t`, starting at `at`) the slots a
    /// drop of a value of type `t` at mode `m` may need live (drop check, ARCH
    /// 5.4): every slot under a user `Drop` impl, the owned parts below
    /// containers, and nothing behind a reference. Returns the next index.
    pub fn drop_slots(&mut self, t: Ty, m: DropMode, at: u32, out: &mut Vec<bool>) -> u32 {
        let all = m == DropMode::All;
        match self.tys.kind(t) {
            TyKind::Ref(r, _, inner) => {
                let mut at = at;
                if !bound(r) {
                    out[at as usize] = all;
                    at += 1;
                }
                self.drop_slots(inner, if all { DropMode::All } else { DropMode::None }, at, out)
            }
            TyKind::RawPtr(_, inner) => self.drop_slots(inner, if all { DropMode::All } else { DropMode::None }, at, out),
            TyKind::Adt(def, args) => {
                let mut at = at;
                for k in 0..adt_regions(self.p, self.tys, t) {
                    let rm = if let Some(m) = builtin_region_drop(self.tys, t) {
                        m
                    } else {
                        self.p.regions.adts(self.p).region_modes(def, k as usize).1
                    };
                    out[at as usize] = all || (m != DropMode::None && rm == DropMode::All);
                    at += 1;
                }
                for (j, g) in self.tys.args(args).to_vec().into_iter().enumerate() {
                    if let GenericArg::Ty(e) = g {
                        let (_, pm) = self.p.regions.adts(self.p).arg_modes(self.p, def, j);
                        at = self.drop_slots(e, m.then(pm), at, out);
                    }
                }
                at
            }
            TyKind::Tuple(ts) => {
                let mut at = at;
                for e in self.tys.tys_of(ts).to_vec() {
                    at = self.drop_slots(e, m, at, out);
                }
                at
            }
            TyKind::Array(e, _) | TyKind::Slice(e) => self.drop_slots(e, m, at, out),
            TyKind::Closure(_, args) => {
                let mut at = at;
                for e in closure_fields(self.tys, args) {
                    at = self.drop_slots(e, m, at, out);
                }
                at
            }
            // An owned dyn's unknown destructor may use what it borrows,
            // its trait args' regions too.
            TyKind::Dyn(..) => {
                let n = self.slots(t);
                for k in at..at + n {
                    out[k as usize] = m != DropMode::None;
                }
                at + n
            }
            // A fn pointer has no destructor.
            TyKind::FnPtr(_) if ptr_free(self.tys, t).is_some() => at + 1,
            _ => at,
        }
    }
}

/// `t` with every region erased: references get `Region::Erased`, Adt lifetime
/// args are dropped. The erased form is what check, mono, and cgen read.
#[allow(dead_code)] // Collect resolves signatures twice today; Adt lifetime params erase with this.
pub fn erase(tys: &mut impl TyIntern, t: Ty) -> Ty {
    match tys.kind(t) {
        TyKind::Ref(r, m, inner) => {
            let i = erase(tys, inner);
            if r == Region::Erased && i == inner { t } else { tys.intern(TyKind::Ref(Region::Erased, m, i)) }
        }
        TyKind::RawPtr(m, inner) => {
            let i = erase(tys, inner);
            if i == inner { t } else { tys.intern(TyKind::RawPtr(m, i)) }
        }
        TyKind::Slice(e) => {
            let i = erase(tys, e);
            if i == e { t } else { tys.intern(TyKind::Slice(i)) }
        }
        TyKind::Array(e, n) => {
            let i = erase(tys, e);
            if i == e { t } else { tys.intern(TyKind::Array(i, n)) }
        }
        TyKind::Tuple(ts) => {
            let old = tys.tys_of(ts).to_vec();
            let new: Vec<Ty> = old.iter().map(|&e| erase(tys, e)).collect();
            if new == old { t } else {
                let id = tys.intern_tys(&new);
                tys.intern(TyKind::Tuple(id))
            }
        }
        TyKind::Adt(def, args) => {
            let (new, same) = erase_args(tys, args);
            if same { t } else { tys.mk_adt(def, &new) }
        }
        TyKind::Projection(a, args) => {
            let (new, same) = erase_args(tys, args);
            if same { t } else {
                let id = tys.intern_args(&new);
                tys.intern(TyKind::Projection(a, id))
            }
        }
        // A fn pointer's insides are already in erased form (`'static`
        // kept); only its free region names a lifetime.
        TyKind::FnPtr(sig) => {
            let b = tys.sig(sig);
            if b.value.free_region == Region::Erased { t } else {
                let s = tys.intern_sig(Binder { count: b.count, value: FnSig { free_region: Region::Erased, ..b.value } });
                tys.intern(TyKind::FnPtr(s))
            }
        }
        _ => t,
    }
}

/// An arg list with regions erased and lifetime args dropped, and whether
/// it is unchanged.
fn erase_args(tys: &mut impl TyIntern, args: ArgsId) -> (Vec<GenericArg>, bool) {
    let old = tys.args(args).to_vec();
    let mut new = Vec::with_capacity(old.len());
    for g in &old {
        match *g {
            GenericArg::Ty(e) => new.push(GenericArg::Ty(erase(tys, e))),
            GenericArg::Lifetime(_) => {}
            c => new.push(c),
        }
    }
    let same = new == old;
    (new, same)
}

/// Every region of a regioned type, in slot order.
pub fn regions_of(tys: &impl TyIntern, t: Ty, out: &mut Vec<Region>) {
    regions_walk(tys, t, true, out)
}

/// `regions_of` without fn pointer free regions: the input lifetimes
/// elision counts (rustc does not look into fn pointer types there).
pub fn elision_regions(tys: &impl TyIntern, t: Ty, out: &mut Vec<Region>) {
    regions_walk(tys, t, false, out)
}

fn regions_walk(tys: &impl TyIntern, t: Ty, fn_ptrs: bool, out: &mut Vec<Region>) {
    let regions_of = |tys: &_, t, out: &mut Vec<Region>| regions_walk(tys, t, fn_ptrs, out);
    match tys.kind(t) {
        TyKind::Ref(r, _, inner) => {
            if !bound(r) {
                out.push(r);
            }
            regions_of(tys, inner, out);
        }
        // The free regions of a dyn's trait args (R11); its object
        // lifetime is not counted here.
        TyKind::Dyn(..) => {
            for e in dyn_arg_tys(tys, t) {
                regions_of(tys, e, out);
            }
        }
        TyKind::Adt(_, args) => {
            if tys.is_chars_ty(t) {
                out.push(Region::Erased);
            }
            for g in tys.args(args).to_vec() {
                match g {
                    GenericArg::Ty(e) => regions_of(tys, e, out),
                    GenericArg::Lifetime(r) if !bound(r) => out.push(r),
                    _ => {}
                }
            }
        }
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts).to_vec() {
                regions_of(tys, e, out);
            }
        }
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => regions_of(tys, e, out),
        TyKind::Closure(_, args) => {
            for e in closure_fields(tys, args) {
                regions_of(tys, e, out);
            }
        }
        TyKind::FnPtr(_) if fn_ptrs => out.extend(ptr_free(tys, t)),
        _ => {}
    }
}

/// `regions_of` plus each dyn's object lifetime where it is not
/// late-bound (`'static` when the trait needs it), in the slot order of
/// `Builder::sugar_regions`: a fn item's signature paired with a
/// `dyn Fn*` target's places (`entail_dyn`).
fn sig_slot_regions(p: &Program, tys: &impl TyIntern, t: Ty, out: &mut Vec<Region>) {
    match tys.kind(t) {
        TyKind::Ref(r, _, inner) => {
            if !bound(r) {
                out.push(r);
            }
            sig_slot_regions(p, tys, inner, out);
        }
        TyKind::Dyn(_, r) => {
            if !bound(r) {
                out.push(if crate::check::object::dyn_is_static(p, tys, t) { Region::Static } else { r });
            }
            for e in dyn_arg_tys(tys, t) {
                sig_slot_regions(p, tys, e, out);
            }
        }
        TyKind::Adt(_, args) => {
            if tys.is_chars_ty(t) {
                out.push(Region::Erased);
            }
            for g in tys.args(args).to_vec() {
                match g {
                    GenericArg::Ty(e) => sig_slot_regions(p, tys, e, out),
                    GenericArg::Lifetime(r) if !bound(r) => out.push(r),
                    _ => {}
                }
            }
        }
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts).to_vec() {
                sig_slot_regions(p, tys, e, out);
            }
        }
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => sig_slot_regions(p, tys, e, out),
        _ => regions_of(tys, t, out),
    }
}

/// `t` (a template-form type over the Adt's params) with `args` substituted,
/// if every type it needs is already interned. Never interns.
fn subst_get(tys: &impl TyIntern, t: Ty, args: &[GenericArg]) -> Option<Ty> {
    if !tys.flags(t).contains_param() {
        return Some(t);
    }
    match tys.kind(t) {
        TyKind::Param(j) => args.get(j.0 as usize)?.as_ty(),
        TyKind::Ref(r, m, i) => {
            let i = subst_get(tys, i, args)?;
            tys.get(TyKind::Ref(r, m, i))
        }
        TyKind::RawPtr(m, i) => {
            let i = subst_get(tys, i, args)?;
            tys.get(TyKind::RawPtr(m, i))
        }
        TyKind::Slice(e) => {
            let e = subst_get(tys, e, args)?;
            tys.get(TyKind::Slice(e))
        }
        TyKind::Array(e, n) => {
            let e = subst_get(tys, e, args)?;
            tys.get(TyKind::Array(e, n))
        }
        TyKind::Tuple(ts) => {
            let v: Option<Vec<Ty>> = tys.tys_of(ts).to_vec().into_iter().map(|e| subst_get(tys, e, args)).collect();
            let id = tys.get_tys(&v?)?;
            tys.get(TyKind::Tuple(id))
        }
        TyKind::Adt(d, a) => {
            let v: Option<Vec<GenericArg>> = tys
                .args(a)
                .to_vec()
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(e) => subst_get(tys, e, args).map(GenericArg::Ty),
                    x => Some(x),
                })
                .collect();
            let id = tys.get_args(&v?)?;
            tys.get(TyKind::Adt(d, id))
        }
        _ => None,
    }
}

/// A universal region index: 0 is `'static`, `k + 1` is `Region::Param(k)`.
pub(super) type Univ = u32;

/// The universal regions of the body being checked: per parameter local and
/// the return place, the universal of each slot, plus known relations.
pub(super) struct OwnSig {
    pub n_univ: u32,
    /// Per local `0..=arg_count`: the universal of each slot.
    pub slots: Vec<Vec<Univ>>,
    /// Known `'a: 'b` facts between universals (closed by `known`).
    pub facts: Vec<(Univ, Univ)>,
    /// Display names, by universal (index 0 is `'static`).
    pub names: Vec<String>,
    /// Report universal relations that do not hold (false in instance
    /// bodies: rustc checks the template, and lust's call rules are coarser
    /// than a template's opaque type params).
    pub check: bool,
    /// A closure body: its universals are the closure rule's, not its
    /// parent's named lifetimes.
    pub closure: bool,
    /// In a closure body, by universal: the requirement end it stands for
    /// (`'static`, a captured slot, a free argument slot, an output slot).
    /// Relations among the first three are its creator's to prove
    /// (`closure_requirements`), not errors here; the env reference and
    /// higher-ranked argument slots are None.
    pub ends: Vec<Option<End>>,
    /// A closure body passed for a bound whose output holds a callee type
    /// param (`ClosureEntry::call_out`): what it needs of its output slots
    /// is also its creator's to prove (`flow_closure_output`).
    pub call_out: bool,
    /// An `impl Trait` return: the universal the returned value's
    /// capture var equals (`Builder::cap_var` of local 0), for the
    /// captures its hidden type has no slot for. The ret slots' rule
    /// applies to it: only the captured universals outlive it.
    pub ret_cap: Option<Univ>,
    /// An `impl Trait` return with a region signature: the returned
    /// value's vars only outlive `ret_cap` (its regions are inferred, each
    /// a captured lifetime), they equal no universal; and the universals
    /// they must outlive (`OpaqueInfo::outlives`) and its item's regioned
    /// type (`OpaqueInfo::item_out`, `Builder::rpit_item_edges`).
    pub ret_vars: Option<(Vec<Univ>, Option<Ty>)>,
    /// The universal an elided lifetime in that item type stands for:
    /// Rust's output elision (`&self`'s, else the one input lifetime).
    pub ret_elided: Option<Univ>,
    /// Per type param that a dyn coercion in the body unsizes: its index
    /// and the universal that stands for it (`param_univs`).
    pub param_univ: Vec<(u32, Univ)>,
    /// In a closure body, per lifetime `k` of the enclosing fn that one of
    /// the fn's `Fn*` bounds names: the universal that stands for `'k`
    /// (`End::Fn(k)`). A call through such a bound (or passing the bounded
    /// param on) binds `'k` to it; the creator proves what the body needs
    /// of it with its own `'k`.
    pub fn_lts: Vec<Option<Univ>>,
}

/// One end of a closure requirement (`closure_requirements`): `'static`,
/// a captured slot (in the closure type's slot order), a free argument
/// slot (in `closure_arg_slots` order), an output slot (only as the
/// longer-lived side's target: what the output may hold), or lifetime `k`
/// of the enclosing fn (`OwnSig::fn_lts`; the creator reads it as its own
/// universal for `'k`, `Builder::fn_ends`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum End {
    Static,
    Cap(u32),
    Arg(u32),
    Out(u32),
    Fn(u32),
}

/// What a callee's `Fn*` bound makes of one closure argument slot
/// (`bound_slots`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BoundSlot {
    /// The call's instantiation of a projection: free in the closure.
    Free,
    /// Slot `q` of the `n` slots of the call's instantiation of the
    /// callee's type param `j`: free in the closure, paired with the
    /// call's binding of `j` (`link_bound_closure`).
    Param { j: u32, q: u32, n: u32 },
    /// An elided lifetime the bound writes: higher-ranked.
    Hr,
    /// A lifetime the bound names: this var (`'static` is 0).
    Tie(u32),
}

/// The fn whose body holds `f`: `f` itself, or a closure's enclosing fn.
fn root_fn(p: &Program, f: LocalDefId) -> LocalDefId {
    let mut root = f;
    while let Some(e) = p.gx.closure_fns.get(&root).and_then(|d| p.gx.closures.get(d)) {
        root = e.parent;
    }
    root
}

/// The lifetimes (`Region::Param` indices) that the bounds of the fn
/// enclosing body `f` name (`Fn*`, `Item = X`, `T: Tr<'a>`, `T: 'a`,
/// implied ones): a closure body in it gets a universal for each
/// (`OwnSig::fn_lts`).
fn root_bound_lifetimes(p: &Program, f: LocalDefId) -> Vec<(u32, String)> {
    let Some(sig) = p.regions.own_body_sig(p, root_fn(p, f)) else { return Vec::new() };
    let mut rs = Vec::new();
    for b in &sig.fn_bounds {
        for &t in b.inputs.iter().chain(&b.output) {
            regions_of(&p.tys, t, &mut rs);
        }
    }
    for &(_, _, t) in &sig.item_bounds {
        regions_of(&p.tys, t, &mut rs);
    }
    for b in &sig.trait_bounds {
        rs.extend(b.lifetimes.iter().copied());
    }
    let root = root_fn(p, f);
    rs.extend(crate::check::outlives::param_bounds(p, Some(sig), fn_env(p, root)).into_iter().map(|(_, r)| r));
    let mut ks: Vec<u32> = rs.iter().filter_map(|r| if let Region::Param(k) = r { Some(*k) } else { None }).filter(|&k| k < sig.n_univ).collect();
    ks.sort_unstable();
    ks.dedup();
    ks.into_iter().map(|k| (k, sig.names.get(k as usize).cloned().unwrap_or_else(|| "a lifetime of the enclosing fn".into()))).collect()
}

/// True when a call in `body` may pass a type param with a regioned `Fn`
/// bound (the fn holding it has one), a fn item, or a closure with its
/// own signature (`free_sig_bound`) to a generic fn, which proves the
/// callee's bound from its signature (`entail_bound`) even in a body
/// with no loans.
pub(super) fn may_entail_bounds(p: &Program, body: &Body) -> bool {
    p.regions.own_body_sig(p, root_fn(p, body.fn_id)).is_some_and(|s| !s.fn_bounds.is_empty())
        || body.blocks.iter().any(|b| b.stmts.iter().any(|s| matches!(s.kind, StmtKind::Assign(_, Rvalue::FnValue(..)))))
        || body.locals.iter().any(|l| mentions_fn_ptr(&body.tys, l.ty) || free_sig_closure(p, &body.tys, l.ty))
}

/// True for a closure type (also behind references) whose output holds
/// regions: passed for a bound, its output must match the bound's
/// (`free_sig_bound`).
fn free_sig_closure(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(_, _, e) => free_sig_closure(p, tys, e),
        TyKind::Closure(def, _) => p.gx.closures.get(&def).is_some_and(|c| holds_slots(p, &p.tys, c.output)),
        _ => false,
    }
}

/// True when erased type `t` has region slots: a reference, a dyn type,
/// or an Adt with lifetime params (which check's types do not write).
fn holds_slots(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(..) | TyKind::Dyn(..) => true,
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| holds_slots(p, tys, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) => holds_slots(p, tys, e),
        TyKind::Adt(_, a) => adt_regions(p, tys, t) > 0 || tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| holds_slots(p, tys, e))),
        _ => crate::check::closure::may_hold_region(tys, t),
    }
}

/// True when type `t` holds a fn pointer (W-BORROW3: a body with one runs
/// the region pass, which proves fn pointer coercions).
fn mentions_fn_ptr(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::FnPtr(_) => true,
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => mentions_fn_ptr(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| mentions_fn_ptr(tys, e)),
        TyKind::Adt(_, a) => tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| mentions_fn_ptr(tys, e))),
        _ => false,
    }
}

/// What a region of a `Fn` signature is when one signature proves
/// another (`match_fn_sides`): a fixed var of this body, a binder of the
/// signature (each elided input lifetime of `Fn` sugar is its own,
/// numbered in order, and an elided output is the one input's; a fn
/// item's late-bound lifetime is one wherever it is written), or a region
/// nothing ties (a type param's instantiation).
#[derive(Clone, Copy, PartialEq)]
enum Side {
    Tie(u32),
    Binder(u32),
    Free,
}

/// The sides of a source signature's regions in order (`Side`): `F`'s
/// bound over this body's universals, or a fn item's (`early`: its
/// early-bound lifetimes, fresh vars of this use).
struct FnSides {
    item: Option<Vec<bool>>,
    early: FxMap<u32, u32>,
    n: u32,
    /// In a closure body, the universal of each lifetime of the enclosing
    /// fn (`OwnSig::fn_lts`); else `'k` is universal `k + 1`.
    fn_lts: Option<Vec<Option<u32>>>,
}

impl FnSides {
    fn new(item: Option<Vec<bool>>) -> Self {
        FnSides { item, early: FxMap::default(), n: 0, fn_lts: None }
    }

    fn side(&mut self, b: &mut Builder<'_, '_>, r: Region, out: bool) -> Side {
        match (r, &self.item) {
            (Region::Static, _) => Side::Tie(0),
            (Region::Param(k), None) => match &self.fn_lts {
                Some(lts) => lts.get(k as usize).copied().flatten().map_or(Side::Free, Side::Tie),
                None => Side::Tie(k + 1),
            },
            (Region::Param(k), Some(e)) if e.get(k as usize) == Some(&true) => Side::Tie(*self.early.entry(k).or_insert_with(|| b.fresh())),
            (Region::Param(k), Some(_)) => Side::Binder(k),
            (Region::Bound(_), None) if out => Side::Binder(0),
            (Region::Bound(_), None) => {
                self.n += 1;
                Side::Binder(self.n - 1)
            }
            _ => Side::Free,
        }
    }
}

/// The type params a type names (indices), in order, repeats included.
fn type_params_in(tys: &impl TyIntern, t: Ty, out: &mut Vec<u32>) {
    match tys.kind(t) {
        TyKind::Param(j) => out.push(j.0),
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => type_params_in(tys, e, out),
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts).to_vec() {
                type_params_in(tys, e, out);
            }
        }
        TyKind::Adt(_, a) | TyKind::Projection(_, a) => {
            for g in tys.args(a).to_vec() {
                if let GenericArg::Ty(e) = g {
                    type_params_in(tys, e, out);
                }
            }
        }
        _ => {}
    }
}

/// The regions of `b` in the places where `a` (the same shape, as for
/// `region_pairs`) has a type param or a projection.
fn param_covered_regions(tys: &impl TyIntern, a: Ty, b: Ty, out: &mut Vec<Region>) {
    match (tys.kind(a), tys.kind(b)) {
        (TyKind::Param(_) | TyKind::Projection(..), _) => regions_of(tys, b, out),
        (TyKind::Ref(_, _, x), TyKind::Ref(_, _, y))
        | (TyKind::Array(x, _), TyKind::Array(y, _))
        | (TyKind::Slice(x), TyKind::Slice(y))
        | (TyKind::RawPtr(_, x), TyKind::RawPtr(_, y)) => param_covered_regions(tys, x, y, out),
        (TyKind::Tuple(x), TyKind::Tuple(y)) => {
            for (x, y) in tys.tys_of(x).to_vec().into_iter().zip(tys.tys_of(y).to_vec()) {
                param_covered_regions(tys, x, y, out);
            }
        }
        (TyKind::Adt(da, xa), TyKind::Adt(db, xb)) if da == db => {
            for (x, y) in tys.args(xa).to_vec().into_iter().zip(tys.args(xb).to_vec()) {
                if let (GenericArg::Ty(x), GenericArg::Ty(y)) = (x, y) {
                    param_covered_regions(tys, x, y, out);
                }
            }
        }
        _ => {}
    }
}

/// True when `b` (the same shape as `a`, as for `param_covered_regions`)
/// holds only `'static` data in every place where `a` has a type param or
/// a projection: no region but `'static`, and nothing (a type param, a
/// dyn, an opaque, a fn pointer, a closure) whose regions are not written.
fn static_at_params(tys: &impl TyIntern, a: Ty, b: Ty) -> bool {
    match (tys.kind(a), tys.kind(b)) {
        (TyKind::Param(_) | TyKind::Projection(..), _) => static_closed(tys, b),
        (TyKind::Ref(_, _, x), TyKind::Ref(_, _, y))
        | (TyKind::Array(x, _), TyKind::Array(y, _))
        | (TyKind::Slice(x), TyKind::Slice(y))
        | (TyKind::RawPtr(_, x), TyKind::RawPtr(_, y)) => static_at_params(tys, x, y),
        (TyKind::Tuple(x), TyKind::Tuple(y)) => {
            let (x, y) = (tys.tys_of(x).to_vec(), tys.tys_of(y).to_vec());
            x.len() == y.len() && x.into_iter().zip(y).all(|(x, y)| static_at_params(tys, x, y))
        }
        (TyKind::Adt(da, xa), TyKind::Adt(db, xb)) if da == db => {
            tys.args(xa).to_vec().into_iter().zip(tys.args(xb).to_vec()).all(|(x, y)| match (x, y) {
                (GenericArg::Ty(x), GenericArg::Ty(y)) => static_at_params(tys, x, y),
                _ => true,
            })
        }
        (TyKind::Adt(..) | TyKind::Tuple(_) | TyKind::Ref(..) | TyKind::Array(..) | TyKind::Slice(_) | TyKind::RawPtr(..), _) => false,
        _ => true,
    }
}

/// True when `t` holds no region but `'static` and no part whose regions
/// are not written in it (see `static_at_params`).
fn static_closed(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Unit | TyKind::Bool | TyKind::Char | TyKind::Never | TyKind::Int(_) | TyKind::Float(_) | TyKind::Str => true,
        TyKind::Ref(r, _, e) => r == Region::Static && static_closed(tys, e),
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => static_closed(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).to_vec().into_iter().all(|e| static_closed(tys, e)),
        TyKind::Adt(_, args) => {
            !tys.is_chars_ty(t)
                && tys.args(args).to_vec().into_iter().all(|g| match g {
                    GenericArg::Ty(e) => static_closed(tys, e),
                    GenericArg::Lifetime(r) => r == Region::Static,
                    GenericArg::Const(_) => true,
                })
        }
        _ => false,
    }
}

/// The pairs of regions at the same places of two regioned types (a
/// callee's bound and the argument's signature, `entail_bound`); a type
/// param or projection on either side (an instantiation) pairs nothing.
/// False when the shapes differ.
fn region_pairs(tys: &impl TyIntern, a: Ty, b: Ty, out: &mut Vec<(Region, Region)>) -> bool {
    match (tys.kind(a), tys.kind(b)) {
        (TyKind::Param(_) | TyKind::Projection(..), _) | (_, TyKind::Param(_) | TyKind::Projection(..)) => true,
        (TyKind::Ref(ra, ma, ia), TyKind::Ref(rb, mb, ib)) if ma == mb => {
            if bound(ra) != bound(rb) {
                return false;
            }
            if !bound(ra) {
                out.push((ra, rb));
            }
            region_pairs(tys, ia, ib, out)
        }
        (TyKind::Adt(da, xa), TyKind::Adt(db, xb)) if da == db => {
            let (xa, xb) = (tys.args(xa).to_vec(), tys.args(xb).to_vec());
            xa.len() == xb.len()
                && xa.into_iter().zip(xb).all(|(x, y)| match (x, y) {
                    (GenericArg::Lifetime(r), GenericArg::Lifetime(s)) => {
                        if !bound(r) && !bound(s) {
                            out.push((r, s));
                        }
                        bound(r) == bound(s)
                    }
                    (GenericArg::Ty(x), GenericArg::Ty(y)) => region_pairs(tys, x, y, out),
                    (GenericArg::Const(_), GenericArg::Const(_)) => true,
                    _ => false,
                })
        }
        (TyKind::Tuple(x), TyKind::Tuple(y)) => {
            let (x, y) = (tys.tys_of(x).to_vec(), tys.tys_of(y).to_vec());
            x.len() == y.len() && x.into_iter().zip(y).all(|(x, y)| region_pairs(tys, x, y, out))
        }
        (TyKind::Array(x, _), TyKind::Array(y, _)) | (TyKind::Slice(x), TyKind::Slice(y)) => region_pairs(tys, x, y, out),
        (TyKind::Dyn(_, r), TyKind::Dyn(_, s)) => {
            if bound(r) != bound(s) {
                return false;
            }
            if !bound(r) {
                out.push((r, s));
            }
            let (x, y) = (dyn_arg_tys(tys, a), dyn_arg_tys(tys, b));
            x.len() == y.len() && x.into_iter().zip(y).all(|(x, y)| region_pairs(tys, x, y, out))
        }
        (TyKind::FnPtr(_), TyKind::FnPtr(_)) => match (ptr_free(tys, a), ptr_free(tys, b)) {
            (Some(r), Some(s)) => {
                out.push((r, s));
                true
            }
            (None, None) => true,
            _ => false,
        },
        _ => {
            let (mut x, mut y) = (Vec::new(), Vec::new());
            regions_of(tys, a, &mut x);
            regions_of(tys, b, &mut y);
            x.is_empty() && y.is_empty()
        }
    }
}

/// Whether type param `j` outlives universal `Region::Param(i)` of `sig`:
/// a bound gives it a region that reaches `i` through the declared facts.
fn outlives_univ(sig: &RegionSig, bounds: &[(u32, Region)], j: u32, i: u32) -> bool {
    let mut seen: Vec<Region> = bounds.iter().filter(|(k, _)| *k == j).map(|&(_, r)| r).collect();
    let mut at = 0;
    while at < seen.len() {
        let x = seen[at];
        at += 1;
        if x == Region::Param(i) || x == Region::Static {
            return true;
        }
        for &(a, b) in &sig.facts {
            if a == x && !seen.contains(&b) {
                seen.push(b);
            }
        }
    }
    false
}

/// The type params that the dyn coercions of `body` unsize.
fn dyn_src_params(body: &Body) -> Vec<u32> {
    let mut params: Vec<u32> = Vec::new();
    for s in body.blocks.iter().flat_map(|b| &b.stmts) {
        if let StmtKind::Assign(_, Rvalue::MakeDyn { src, .. }) = &s.kind {
            params_in(&body.tys, *src, &mut params);
        }
    }
    params
}

/// The env of fn `f` (its bounds, `T: 'static` ones included).
fn fn_env(p: &Program, f: LocalDefId) -> &[Predicate] {
    p.gx.fn_scopes.get(f.0 as usize).map_or(&[][..], |fs| &fs.env)
}

/// The erased form of `t` (every region `Erased`, Adt lifetime args
/// dropped) when this body's interner has it; None when it does not or `t`
/// holds a `dyn` or a fn pointer with a free region.
fn erased_lookup(tys: &impl TyIntern, t: Ty) -> Option<Ty> {
    match tys.kind(t) {
        TyKind::Ref(_, m, i) => tys.get(TyKind::Ref(Region::Erased, m, erased_lookup(tys, i)?)),
        TyKind::RawPtr(m, i) => tys.get(TyKind::RawPtr(m, erased_lookup(tys, i)?)),
        TyKind::Slice(e) => tys.get(TyKind::Slice(erased_lookup(tys, e)?)),
        TyKind::Array(e, n) => tys.get(TyKind::Array(erased_lookup(tys, e)?, n)),
        TyKind::Tuple(ts) => {
            let es = tys.tys_of(ts).iter().map(|&e| erased_lookup(tys, e)).collect::<Option<Vec<Ty>>>()?;
            tys.get(TyKind::Tuple(tys.get_tys(&es)?))
        }
        TyKind::Adt(def, args) => {
            let mut a = Vec::new();
            for g in tys.args(args).iter() {
                match *g {
                    GenericArg::Ty(e) => a.push(GenericArg::Ty(erased_lookup(tys, e)?)),
                    GenericArg::Lifetime(_) => {}
                    c => a.push(c),
                }
            }
            tys.get(TyKind::Adt(def, tys.get_args(&a)?))
        }
        TyKind::Dyn(..) => None,
        TyKind::FnPtr(sig) if tys.sig(sig).value.free_region != Region::Erased => None,
        _ => Some(t),
    }
}

/// The type params in `t` (also inside projections), by index, once each.
/// True when `t` may hold a closure value (also behind a type param, an
/// infer var, or an opaque type): `closure_only_call`.
fn holds_closure(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Closure(..) | TyKind::Opaque(..) | TyKind::Param(_) | TyKind::Projection(..) | TyKind::Infer(_) | TyKind::Dyn(..) => true,
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => holds_closure(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| holds_closure(tys, e)),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) => tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| holds_closure(tys, e))),
        _ => false,
    }
}

fn params_in(tys: &impl TyIntern, t: Ty, out: &mut Vec<u32>) {
    match tys.kind(t) {
        TyKind::Param(j) => {
            if !out.contains(&j.0) {
                out.push(j.0);
            }
        }
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => params_in(tys, e, out),
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts).to_vec() {
                params_in(tys, e, out);
            }
        }
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Projection(_, a) | TyKind::Opaque(_, a) => {
            for g in tys.args(a).to_vec() {
                if let GenericArg::Ty(e) = g {
                    params_in(tys, e, out);
                }
            }
        }
        TyKind::FnPtr(sig) => {
            let b = tys.sig(sig);
            for e in tys.tys_of(b.value.inputs).to_vec() {
                params_in(tys, e, out);
            }
            params_in(tys, b.value.output, out);
        }
        _ => {}
    }
}

/// The universal of a regioned signature region.
/// The universal of a fn's elided output lifetime under Rust's elision
/// rules: `&self`'s (or `&mut self`'s) region, else the one region its
/// inputs hold. None otherwise (rustc E0106).
fn output_elision(p: &Program, has_self: bool, sig: &RegionSig) -> Option<Univ> {
    if has_self
        && let Some(&p0) = sig.params.first()
        && let TyKind::Ref(Region::Param(k), _, _) = p.tys.kind(p0)
    {
        return Some(k + 1);
    }
    let mut rs = Vec::new();
    for &t in &sig.params {
        elision_regions(&p.tys, t, &mut rs);
    }
    rs.retain(|r| matches!(r, Region::Param(_)));
    rs.sort_by_key(|r| if let Region::Param(k) = r { *k } else { 0 });
    rs.dedup();
    match rs[..] {
        [Region::Param(k)] => Some(k + 1),
        _ => None,
    }
}

fn univ_of(r: Region, fresh: &mut impl FnMut() -> Univ) -> Univ {
    match r {
        Region::Static => 0,
        Region::Param(k) => k + 1,
        _ => fresh(),
    }
}

impl OwnSig {
    /// The own signature of a body. `sig` is its fn's region signature, if
    /// any; `closure` marks a closure body (env first). Slots `sig` cannot
    /// pair with the erased local types get fresh, unrelated universals:
    /// conservative inside the body, and callers use the same signature.
    pub fn build<'p>(p: &'p Program, body: &Body<'p>, sig: Option<&RegionSig>, closure: bool, check: bool) -> OwnSig {
        let mut sc = SlotCx::new(&body.tys, p);
        let mut own = OwnSig {
            n_univ: 0,
            slots: Vec::new(),
            facts: Vec::new(),
            names: vec!["'static".into()],
            check,
            closure,
            ends: Vec::new(),
            fn_lts: Vec::new(),
            call_out: false,
            ret_cap: None,
            ret_vars: None,
            ret_elided: None,
            param_univ: Vec::new(),
        };
        if closure {
            own.call_out = p.gx.closure_fns.get(&body.fn_id).and_then(|d| p.gx.closures.get(d)).is_some_and(|c| c.call_out);
            own.closure_sig(p, body, &mut sc);
            own.closure_param_univs(p, body);
            return own;
        }
        let f = p.fn_info(body.fn_id);
        if let Some(sig) = sig {
            own.n_univ = sig.n_univ;
            own.names.extend(sig.names.iter().cloned());
            while own.names.len() < own.n_univ as usize + 1 {
                own.names.push(format!("'{}", own.names.len()));
            }
            for &(a, b) in &sig.facts {
                let mut none = || 0;
                own.facts.push((univ_of(a, &mut none), univ_of(b, &mut none)));
            }
        }
        // Type param bindings shared across the signature (instances).
        let mut binds: FxMap<u32, Vec<Univ>> = FxMap::default();
        for l in 0..=body.arg_count {
            let erased = body.locals[l].ty;
            let regioned = sig.and_then(|s| if l == 0 { Some(s.ret) } else { s.params.get(l - 1).copied() });
            let mut out = Vec::new();
            let ok = match regioned {
                Some(r) => own.pair(&mut sc, r, erased, &mut binds, &mut out),
                None => false,
            };
            let n = sc.slots(erased) as usize;
            if !ok || out.len() != n {
                out.clear();
                for _ in 0..n {
                    out.push(own.fresh_univ(&f.name, p));
                }
            }
            own.slots.push(out);
        }
        // An `impl Trait` return captures every input region (edition
        // 2024), and callers assume its value lives no longer than any of
        // them (`call_opaque`): each region of the returned value must
        // outlive one fresh universal that every other universal outlives
        // (W-CHECK-G3).
        // An `impl Trait + 'static` return: every region of the returned
        // value is `'static` instead.
        if opaque_static_ret(p, p.ret_view(body.fn_id)) && !own.slots.is_empty() {
            own.slots[0].fill(0);
            own.ret_cap = Some(0);
        } else if crate::check::opaque::mentions_opaque(&p.tys, p.ret_view(body.fn_id), None) && !own.slots.is_empty() {
            // A `use<..>` list captures only its universals: the returned
            // value may not hold another (rustc E0700).
            let caps = sig.and_then(|s| s.opaque_caps.as_ref());
            let mut ret: Vec<Univ> = own.slots[0].clone();
            let n = own.n_univ;
            let rc = own.fresh_univ(&f.name, p);
            own.names[rc as usize] = "the lifetimes the returned `impl Trait` captures".into();
            own.ret_cap = Some(rc);
            if sig.is_some()
                && let TyKind::Opaque(od, _) = p.tys.kind(p.ret_view(body.fn_id))
                && let Some(info) = p.gx.opaques.get(&od)
            {
                let mut none = || 0;
                own.ret_vars = Some((info.outlives.iter().map(|&r| univ_of(r, &mut none)).collect(), info.item_out));
                own.ret_elided = sig.and_then(|s| output_elision(p, f.self_kind.is_some(), s));
            }
            ret.push(rc);
            for &r in &ret {
                if caps.is_some() && r > sig.map_or(0, |s| s.n_univ) {
                    own.names[r as usize] = "the lifetimes the returned `impl Trait` captures (its `use<..>` list)".into();
                }
                for u in 1..=n {
                    if !ret.contains(&u) && caps.is_none_or(|c| c.contains(&(u - 1))) {
                        own.facts.push((u, r));
                    }
                }
            }
        }
        own.param_univs(p, body, sig);
        own.implied(&mut sc, body);
        own
    }

    /// One universal per type param that a dyn coercion in the body
    /// unsizes (`Box<dyn Tr + 'o>` from `T` needs `T: 'o`, rustc E0309).
    /// It outlives what the fn's implied bounds and `T: 'static` bounds
    /// give the param (`check::outlives::param_bounds`); the coercion
    /// makes it outlive the object lifetime (`Rvalue::MakeDyn`).
    /// Without a region signature every slot is a fresh universal, so the
    /// implied bounds are unknown and nothing is added.
    fn param_univs(&mut self, p: &Program, body: &Body, sig: Option<&RegionSig>) {
        let Some(sig) = sig else { return };
        let params = dyn_src_params(body);
        if params.is_empty() {
            return;
        }
        let bounds = crate::check::outlives::param_bounds(p, Some(sig), fn_env(p, body.fn_id));
        for j in params {
            let u = self.param_univ_new(p, body.fn_id, j);
            for &(_, r) in bounds.iter().filter(|(k, _)| *k == j) {
                match r {
                    Region::Static => self.facts.push((u, 0)),
                    Region::Param(i) => self.facts.push((u, i + 1)),
                    _ => {}
                }
            }
        }
    }

    /// `param_univs` in a closure body. Its universals are its own slots,
    /// not the enclosing fn's lifetimes, so a type param's universal
    /// outlives `'static` when the fn bounds it so, every slot when the
    /// fn's bounds make it outlive every universal of the fn (a slot can
    /// only hold those or local regions), and nothing otherwise (a dyn
    /// object it makes may then reach no slot).
    fn closure_param_univs(&mut self, p: &Program, body: &Body) {
        let params = dyn_src_params(body);
        if params.is_empty() {
            return;
        }
        let mut f = body.fn_id;
        while let Some(c) = p.gx.closure_fns.get(&f).and_then(|d| p.gx.closures.get(d)) {
            f = c.parent;
        }
        let Some(sig) = p.regions.body_sig(p, f) else { return };
        let bounds = crate::check::outlives::param_bounds(p, Some(sig), fn_env(p, f));
        let slots = self.n_univ;
        for j in params {
            let u = self.param_univ_new(p, f, j);
            self.ends.push(None);
            if bounds.contains(&(j, Region::Static)) {
                self.facts.push((u, 0));
            } else if (0..sig.n_univ).all(|i| outlives_univ(sig, &bounds, j, i)) {
                self.facts.extend((1..=slots).map(|v| (u, v)));
            }
        }
    }

    /// A new universal for type param `j` of fn `f` (`param_univ`).
    fn param_univ_new(&mut self, p: &Program, f: LocalDefId, j: u32) -> Univ {
        self.n_univ += 1;
        let names = p.gx.fn_templates.get(f.0 as usize).and_then(|t| t.as_ref()).map(|t| &t.generics.params);
        let name = names.and_then(|ps| ps.get(j as usize)).map_or_else(|| "?".to_string(), |d| p.display_name(d.name).to_string());
        self.names.push(format!("the type parameter `{name}`"));
        self.param_univ.push((j, self.n_univ));
        self.n_univ
    }

    fn fresh_univ(&mut self, fname: &crate::intern::Sym, p: &Program) -> Univ {
        self.n_univ += 1;
        self.names.push(format!("an anonymous lifetime of `{}`", p.display_name(*fname)));
        self.n_univ
    }

    /// Pairs regioned signature type `r` with erased local type `e`, pushing
    /// the universal of each slot. False when the shapes differ.
    fn pair<T: TyIntern>(
        &mut self,
        sc: &mut SlotCx<'_, '_, T>,
        r: Ty,
        e: Ty,
        binds: &mut FxMap<u32, Vec<Univ>>,
        out: &mut Vec<Univ>,
    ) -> bool {
        let tys = sc.tys;
        match (tys.kind(r), tys.kind(e)) {
            (TyKind::Param(j), _) => {
                let n = sc.slots(e) as usize;
                if let TyKind::Param(k) = tys.kind(e)
                    && k == j
                {
                    return true;
                }
                let us = match binds.get(&j.0) {
                    Some(us) if us.len() == n => us.clone(),
                    Some(_) => return false,
                    None => {
                        let us: Vec<Univ> = (0..n)
                            .map(|_| {
                                self.n_univ += 1;
                                self.names.push("a lifetime of a type argument".into());
                                self.n_univ
                            })
                            .collect();
                        binds.insert(j.0, us.clone());
                        us
                    }
                };
                out.extend(us);
                true
            }
            (TyKind::Ref(rr, rm, ri), TyKind::Ref(er, em, ei)) if rm == em => {
                if bound(rr) != bound(er) {
                    return false;
                }
                if !bound(rr) {
                    let mut fresh = || {
                        self.n_univ += 1;
                        self.n_univ
                    };
                    let u = univ_of(rr, &mut fresh);
                    while self.names.len() < self.n_univ as usize + 1 {
                        self.names.push("an anonymous lifetime".into());
                    }
                    out.push(u);
                }
                self.pair(sc, ri, ei, binds, out)
            }
            (TyKind::Adt(rd, ra), TyKind::Adt(ed, ea)) if rd == ed => {
                let lts: Vec<Region> = tys.args(ra).iter().filter_map(|g| if let GenericArg::Lifetime(r) = g && *r != crate::ty::DYN_LATE { Some(*r) } else { None }).collect();
                for k in 0..adt_regions(sc.p, tys, e) as usize {
                    let mut fresh = || {
                        self.n_univ += 1;
                        self.n_univ
                    };
                    let u = match lts.get(k) {
                        Some(&r) => univ_of(r, &mut fresh),
                        None => fresh(),
                    };
                    while self.names.len() < self.n_univ as usize + 1 {
                        self.names.push("an anonymous lifetime".into());
                    }
                    out.push(u);
                }
                let rargs: Vec<Ty> = tys.args(ra).iter().filter_map(|g| g.as_ty()).collect();
                let eargs: Vec<Ty> = tys.args(ea).iter().filter_map(|g| g.as_ty()).collect();
                rargs.len() == eargs.len() && rargs.iter().zip(&eargs).all(|(&a, &b)| self.pair(sc, a, b, binds, out))
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                let (a, b) = (tys.tys_of(a).to_vec(), tys.tys_of(b).to_vec());
                a.len() == b.len() && a.iter().zip(&b).all(|(&x, &y)| self.pair(sc, x, y, binds, out))
            }
            (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
                self.pair(sc, a, b, binds, out)
            }
            // The object lifetime the signature names (or its default;
            // `'static` for a trait bounded by `'static`).
            (TyKind::Dyn(_, rr), TyKind::Dyn(_, er)) => {
                if bound(rr) != bound(er) {
                    return false;
                }
                if !bound(rr) {
                    let rr = if crate::check::object::dyn_is_static(sc.p, tys, e) { Region::Static } else { rr };
                    let mut fresh = || {
                        self.n_univ += 1;
                        self.n_univ
                    };
                    let u = univ_of(rr, &mut fresh);
                    while self.names.len() < self.n_univ as usize + 1 {
                        self.names.push("an anonymous lifetime".into());
                    }
                    out.push(u);
                }
                // The trait args' regions (R11): the written ones, or fresh
                // universals of their own.
                let (ra, ea) = (dyn_arg_tys(tys, r), dyn_arg_tys(tys, e));
                ra.len() == ea.len() && ra.into_iter().zip(ea).all(|(x, y)| self.pair(sc, x, y, binds, out))
            }
            // A fn pointer's free region: the lifetime the signature names.
            (TyKind::FnPtr(_), TyKind::FnPtr(_)) if ptr_free(tys, e).is_some() => {
                let Some(rr) = ptr_free(tys, r) else { return false };
                let mut fresh = || {
                    self.n_univ += 1;
                    self.n_univ
                };
                let u = univ_of(rr, &mut fresh);
                while self.names.len() < self.n_univ as usize + 1 {
                    self.names.push("an anonymous lifetime".into());
                }
                out.push(u);
                true
            }
            _ => r == e && sc.slots(e) == 0,
        }
    }

    /// A closure body's universals: one per slot of its env (the env
    /// reference's region, then each captured region), of its output, and
    /// of its inputs. The facts are the closure contract (`closure_roles`):
    /// every source (captured, or a free argument slot) outlives every
    /// other sink and every output slot. Relations among the captured
    /// slots, the free argument slots, and `'static` are not errors here:
    /// the creator adds what the body needs of them (`ends`,
    /// `closure_requirements`). Higher-ranked argument slots take no part.
    fn closure_sig<T: TyIntern>(&mut self, p: &Program, body: &Body, sc: &mut SlotCx<'_, '_, T>) {
        let free = p.gx.closure_fns.get(&body.fn_id).and_then(|d| p.gx.closures.get(d)).and_then(|c| c.free_args.clone());
        let fresh = |own: &mut OwnSig, name: &str| -> Univ {
            own.n_univ += 1;
            own.names.push(name.into());
            own.n_univ
        };
        let mut env_caps: Vec<Univ> = Vec::new();
        let mut roles: Vec<(bool, bool)> = Vec::new();
        let inputs: Vec<Ty> = (2..=body.arg_count).map(|l| body.locals[l].ty).collect();
        let entry = p.gx.closure_fns.get(&body.fn_id).and_then(|d| p.gx.closures.get(d));
        let arg_roles: Vec<Option<(bool, bool)>> = match entry.map(|c| closure_arg_slots(sc, c)) {
            Some(Ok(slots)) => slots.into_iter().map(|(r, _)| r).collect(),
            // Unpaired annotations are the creator's error; every slot is
            // higher-ranked here.
            _ => {
                let mut v = Vec::new();
                closure_arg_roles(sc, &inputs, free.as_deref(), &mut v);
                v
            }
        };
        let mut arg_at = 0usize;
        for l in 0..=body.arg_count {
            let t = body.locals[l].ty;
            let n = sc.slots(t) as usize;
            let mut out = Vec::with_capacity(n);
            if l == 0 {
                // A return annotation's `'static` slots are `'static`.
                let mut named: Vec<Region> = Vec::new();
                let entry = p.gx.closure_fns.get(&body.fn_id).and_then(|d| p.gx.closures.get(d));
                let paired = entry
                    .and_then(|c| c.output_region)
                    .is_some_and(|r| regioned_slots(sc, r, t, &mut named) && named.len() == n);
                // So are the slots the inferred return type keeps as
                // `'static` (a `Box<dyn Fn()>` read from a field): the
                // body's locals of that type are `'static` there (`build`).
                let mut kept: Vec<Region> = Vec::new();
                sc.slot_regions(t, &mut kept);
                for k in 0..n {
                    match named.get(k) {
                        Some(Region::Static) if paired => out.push(0),
                        _ if !paired && kept.get(k) == Some(&Region::Static) => out.push(0),
                        _ => out.push(fresh(self, "the closure's return lifetime")),
                    }
                }
            } else if l == 1 {
                let cl = match sc.tys.kind(t) {
                    TyKind::Ref(_, _, inner) => {
                        out.push(fresh(self, "the closure environment's lifetime"));
                        inner
                    }
                    _ => t,
                };
                if let TyKind::Closure(cdef, args) = sc.tys.kind(cl) {
                    closure_roles(sc, cdef, args, &mut roles);
                }
                while out.len() < n {
                    let u = fresh(self, "a lifetime the closure captures");
                    env_caps.push(u);
                    out.push(u);
                }
            } else {
                // A slot the argument's type keeps as `'static` (`&Rc<dyn Tr>`
                // from a `'static` type) is `'static`, unless the body can
                // store into it (a sink: the contract would assume it). A
                // slot the `Fn` bound's own input type makes `'static`
                // (`Box<dyn Fn()>` in `impl FnOnce(&RefCell<Vec<Box<dyn
                // Fn()>>>)`) is `'static` in rustc's closure signature too,
                // sink or not (`ClosureEntry::bound_inputs`).
                let mut kept: Vec<Region> = Vec::new();
                sc.slot_regions(t, &mut kept);
                let mut fixed: Vec<Region> = Vec::new();
                if let Some(&bt) = entry.and_then(|c| c.bound_inputs.get(l - 2)) {
                    sc.slot_regions(bt, &mut fixed);
                }
                for k in 0..n {
                    let snk = arg_roles.get(arg_at + k).copied().flatten().is_some_and(|(_, snk)| snk);
                    if fixed.len() == n && fixed[k] == Region::Static {
                        out.push(0);
                    } else if kept.get(k) == Some(&Region::Static) && !snk && kept.len() == n {
                        out.push(0);
                    } else {
                        out.push(fresh(self, "a closure argument's lifetime"));
                    }
                }
                arg_at += n;
            }
            self.slots.push(out);
        }
        // The contract: every source (a captured one, a free argument
        // slot) outlives every other sink (a captured one, a free argument
        // slot behind `&mut`, the output). Higher-ranked argument slots
        // take no part.
        let args: Vec<Univ> = self.slots.iter().skip(2).flatten().copied().collect();
        let mut cap_srcs: Vec<Univ> = Vec::new();
        // Output slots pinned to `'static` (a return annotation) take no
        // contract facts: the body shows its result lives that long itself.
        let mut snks: Vec<Univ> = self.slots.first().map(|v| v.iter().copied().filter(|&u| u != 0).collect()).unwrap_or_default();
        for (i, &(src, snk)) in roles.iter().enumerate() {
            if let Some(&u) = env_caps.get(i) {
                if src {
                    cap_srcs.push(u);
                }
                if snk {
                    snks.push(u);
                }
            }
        }
        let mut arg_srcs: Vec<Univ> = Vec::new();
        let mut arg_snks: Vec<Univ> = Vec::new();
        for (i, r) in arg_roles.iter().enumerate() {
            if let (Some((src, snk)), Some(&u)) = (r, args.get(i))
                && u != 0
            {
                if *src {
                    arg_srcs.push(u);
                }
                if *snk {
                    arg_snks.push(u);
                }
            }
        }
        // Sources into sinks; an argument's regions do not flow into an
        // argument's `&mut` target (`closure_arg_vars` agrees).
        for &a in cap_srcs.iter().chain(&arg_srcs) {
            for &b in &snks {
                if a != b {
                    self.facts.push((a, b));
                }
            }
        }
        for &a in &cap_srcs {
            for &b in &arg_snks {
                self.facts.push((a, b));
            }
        }
        // `thread::scope`'s closure (W-THREADS): the scope is live for the
        // whole call, during which the closure's captures stay borrowed,
        // so every captured region (and the `Scope`'s `'env`) outlives the
        // `Scope`'s `'scope` (rustc: `'env: 'scope` from the scope type).
        if entry.is_some_and(|c| c.scope_body)
            && let Some(&[rf, sc, env]) = self.slots.get(2).map(|v| v.as_slice())
        {
            // `&'scope Scope<'scope, 'env>`: one region for both.
            self.facts.push((rf, sc));
            self.facts.push((sc, rf));
            for &u in env_caps.iter().chain(self.slots[1].first().filter(|_| self.slots[1].len() > env_caps.len())).chain([&env]) {
                self.facts.push((u, sc));
            }
        }
        for (k, name) in root_bound_lifetimes(p, body.fn_id) {
            if self.fn_lts.len() <= k as usize {
                self.fn_lts.resize(k as usize + 1, None);
            }
            self.fn_lts[k as usize] = Some(fresh(self, &name));
        }
        self.ends = vec![None; self.n_univ as usize + 1];
        self.ends[0] = Some(End::Static);
        for (k, u) in self.fn_lts.iter().enumerate() {
            if let Some(u) = *u {
                self.ends[u as usize] = Some(End::Fn(k as u32));
            }
        }
        // A lifetime of the enclosing fn may reach the output, as a captured
        // source may: what a call's result then holds is the call's rule
        // (`End::Fn` sources of `End::Out` slots).
        let outs: Vec<Univ> = self.slots.first().map(|v| v.iter().copied().filter(|&u| u != 0).collect()).unwrap_or_default();
        for &u in self.fn_lts.iter().flatten() {
            for &o in &outs {
                self.facts.push((u, o));
            }
        }
        for (k, &u) in self.slots.first().cloned().unwrap_or_default().iter().enumerate() {
            if u != 0 {
                self.ends[u as usize] = Some(End::Out(k as u32));
            }
        }
        for (i, &u) in env_caps.iter().enumerate() {
            self.ends[u as usize] = Some(End::Cap(i as u32));
        }
        for (j, r) in arg_roles.iter().enumerate() {
            if r.is_some()
                && let Some(&u) = args.get(j)
                && u != 0
            {
                self.ends[u as usize] = Some(End::Arg(j as u32));
            }
        }
        // A bound's higher-ranked output over its one elided input
        // lifetime (`F: Fn(&T) -> &U`): rustc gives the closure `for<'r>
        // fn(&'r T) -> &'r U`, so that argument slot (the only
        // higher-ranked one) outlives those output slots.
        if let Some(bo) = entry.and_then(|c| c.bound_output) {
            let mut named: Vec<Region> = Vec::new();
            let hr: Vec<usize> = (0..args.len()).filter(|&i| args[i] != 0 && arg_roles.get(i).is_none_or(|r| r.is_none())).collect();
            if regioned_slots(sc, bo, body.locals[0].ty, &mut named)
                && let [j] = hr[..]
            {
                let outs = self.slots.first().cloned().unwrap_or_default();
                for (r, &o) in named.iter().zip(&outs) {
                    if matches!(r, Region::Bound(_)) && o != 0 {
                        self.facts.push((args[j], o));
                    }
                }
            }
        }
        self.implied(sc, body);
    }

    /// Adds the implied bounds of the parameter and return types (rustc's
    /// implied outlives bounds): `&'a T` gives `T: 'a`, so every region
    /// inside a reference outlives the reference's own region.
    fn implied<T: TyIntern>(&mut self, sc: &mut SlotCx<'_, '_, T>, body: &Body) {
        for l in 0..=body.arg_count.min(self.slots.len().saturating_sub(1)) {
            let t = body.locals[l].ty;
            let us = self.slots[l].clone();
            let mut facts = Vec::new();
            implied_walk(sc, t, &us, &mut 0, &mut Vec::new(), &mut facts);
            self.facts.extend(facts);
        }
    }

    /// The reflexive, transitive closure of the facts, as a dense matrix:
    /// `m[a * n + b]` is true when `a: b` is known. `'static` outlives all.
    pub fn known(&self) -> Vec<bool> {
        let n = self.n_univ as usize + 1;
        let mut m = vec![false; n * n];
        for a in 0..n {
            m[a * n + a] = true;
            m[a] = true; // row 0: 'static: a
        }
        for &(a, b) in &self.facts {
            if (a as usize) < n && (b as usize) < n {
                m[a as usize * n + b as usize] = true;
            }
        }
        for k in 0..n {
            for a in 0..n {
                if m[a * n + k] {
                    for b in 0..n {
                        if m[k * n + b] {
                            m[a * n + b] = true;
                        }
                    }
                }
            }
        }
        m
    }
}

/// The region contract of a closure (W-BORROW, ARCH 5.2 closures): per
/// slot of its env field types, in slot order, whether the body may read
/// the region into other places (a source) and whether it may write a
/// region there (a sink). A shared capture `&'c T`: `'c` and `T`'s slots
/// are sources; a mutable one `&'c mut T`: `T`'s slots are sources and
/// sinks, `'c` neither (a captured `&mut` cannot escape), except in an
/// `FnOnce` closure, whose body owns its env and may move the `&mut`
/// out (`'c` a source); a by-value field: its slots are sources and
/// sinks. The body may make any source outlive any sink and its output;
/// the creator adds what the body needs of that (`closure_reqs`), or
/// every source-to-sink edge when the body does not solve, and a call's
/// result holds what the body returns.
pub(super) fn closure_roles<T: TyIntern>(sc: &mut SlotCx<'_, '_, T>, def: DefId, args: ArgsId, out: &mut Vec<(bool, bool)>) {
    let once = sc.p.gx.closures.get(&def).is_some_and(|c| c.kind == crate::check::closure::ClosureKind::FnOnce);
    for f in closure_fields(sc.tys, args) {
        match sc.tys.kind(f) {
            TyKind::Ref(_, m, inner) => {
                let n = sc.slots(inner) as usize;
                if m.is_mut() {
                    out.push((once, false));
                    out.extend(std::iter::repeat_n((true, true), n));
                } else {
                    out.push((true, false));
                    out.extend(std::iter::repeat_n((true, false), n));
                }
            }
            _ => {
                let n = sc.slots(f) as usize;
                out.extend(std::iter::repeat_n((true, true), n));
            }
        }
    }
}

/// The roles of a closure's argument slots, in slot order: `None` for a
/// higher-ranked region; `Some((source, sink))` for a free one. With
/// `free` (`ClosureEntry::free_args`, an iterator method's closure) the
/// arguments are items: free, except the outer reference of an `&item`
/// argument; every free slot is a source, and one behind a `&mut` is a
/// sink too. Without it every argument region is higher-ranked.
pub(super) fn closure_arg_roles<T: TyIntern>(
    sc: &mut SlotCx<'_, '_, T>,
    inputs: &[Ty],
    free: Option<&[bool]>,
    out: &mut Vec<Option<(bool, bool)>>,
) {
    for (i, &t) in inputs.iter().enumerate() {
        let Some(flags) = free else {
            let n = sc.slots(t) as usize;
            out.extend(std::iter::repeat_n(None, n));
            continue;
        };
        match sc.tys.kind(t) {
            TyKind::Ref(_, _, inner) if flags.get(i).copied().unwrap_or(false) => {
                out.push(None);
                arg_slot_roles(sc, inner, false, out);
            }
            _ => arg_slot_roles(sc, t, false, out),
        }
    }
}

/// The argument slots of a closure, in slot order: its role (`None`:
/// higher-ranked; see `closure_arg_roles`) and, for a slot its annotation
/// names (`|x: &'a T|`), the enclosing fn's region it is: such a slot is
/// free, and the creator ties it to that region. A `Region::Bound` slot
/// (an elided lifetime written on a closure with no expected signature)
/// is higher-ranked. `Err` when an annotated type does not pair with the
/// argument's erased type.
pub(super) fn closure_arg_slots<T: TyIntern>(
    sc: &mut SlotCx<'_, '_, T>,
    c: &crate::check::generics::ClosureEntry,
) -> Result<Vec<(Option<(bool, bool)>, Option<Region>)>, ()> {
    let mut roles = Vec::new();
    closure_arg_roles(sc, &c.inputs, c.free_args.as_deref(), &mut roles);
    let mut free_roles = Vec::new();
    closure_arg_roles(sc, &c.inputs, Some(&vec![false; c.inputs.len()]), &mut free_roles);
    let mut named: Vec<Region> = Vec::with_capacity(roles.len());
    for (i, &e) in c.inputs.iter().enumerate() {
        let n = sc.slots(e) as usize;
        match c.input_regions.get(i).copied().flatten() {
            Some(r) => {
                let start = named.len();
                if !regioned_slots(sc, r, e, &mut named) || named.len() - start != n {
                    // An annotation that names no lifetime only marks
                    // its elided ones: unpaired, it counts as unwritten.
                    if names_region(sc.tys, r) {
                        return Err(());
                    }
                    named.truncate(start);
                    named.extend(std::iter::repeat_n(Region::Erased, n));
                }
            }
            None => named.extend(std::iter::repeat_n(Region::Erased, n)),
        }
    }
    Ok(roles
        .into_iter()
        .zip(free_roles)
        .zip(named)
        .map(|((r, fr), nr)| match nr {
            Region::Param(_) | Region::Static => (fr, Some(nr)),
            // An elided lifetime in an annotation of a closure with no
            // expected signature: the closure's own, higher-ranked.
            Region::Bound(_) => (None, None),
            _ => (r, None),
        })
        .collect())
}

/// True when regioned type `r` names a lifetime (`'static` or a param).
fn names_region(tys: &impl TyIntern, r: Ty) -> bool {
    let named = |x: Region| matches!(x, Region::Static | Region::Param(_));
    match tys.kind(r) {
        TyKind::Ref(x, _, inner) => named(x) || names_region(tys, inner),
        TyKind::Adt(_, args) => tys.args(args).iter().any(|g| match g {
            GenericArg::Ty(t) => names_region(tys, *t),
            GenericArg::Lifetime(x) => named(*x),
            _ => false,
        }),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&t| names_region(tys, t)),
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => names_region(tys, e),
        TyKind::Dyn(_, x) => named(x) || dyn_arg_tys(tys, r).into_iter().any(|e| names_region(tys, e)),
        TyKind::FnPtr(_) => ptr_free(tys, r).is_some_and(named),
        _ => false,
    }
}

/// The region a regioned type `r` gives each slot of erased type `e`, in
/// slot order (`Erased` where `r` names none). False when they differ in
/// shape.
fn regioned_slots<T: TyIntern>(sc: &mut SlotCx<'_, '_, T>, r: Ty, e: Ty, out: &mut Vec<Region>) -> bool {
    let tys = sc.tys;
    match (tys.kind(r), tys.kind(e)) {
        (TyKind::Ref(rr, rm, ri), TyKind::Ref(er, em, ei)) if rm == em => {
            if bound(rr) != bound(er) {
                return false;
            }
            if !bound(er) {
                out.push(rr);
            }
            regioned_slots(sc, ri, ei, out)
        }
        (TyKind::Adt(rd, ra), TyKind::Adt(ed, ea)) if rd == ed => {
            let lts: Vec<Region> = tys.args(ra).iter().filter_map(|g| if let GenericArg::Lifetime(x) = g && *x != crate::ty::DYN_LATE { Some(*x) } else { None }).collect();
            for k in 0..adt_regions(sc.p, tys, e) as usize {
                out.push(lts.get(k).copied().unwrap_or(Region::Erased));
            }
            let rargs: Vec<Ty> = tys.args(ra).iter().filter_map(|g| g.as_ty()).collect();
            let eargs: Vec<Ty> = tys.args(ea).iter().filter_map(|g| g.as_ty()).collect();
            rargs.len() == eargs.len() && rargs.into_iter().zip(eargs).all(|(x, y)| regioned_slots(sc, x, y, out))
        }
        (TyKind::Tuple(a), TyKind::Tuple(b)) => {
            let (xs, ys) = (tys.tys_of(a).to_vec(), tys.tys_of(b).to_vec());
            xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| regioned_slots(sc, x, y, out))
        }
        (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
            regioned_slots(sc, a, b, out)
        }
        (TyKind::Dyn(_, rr), TyKind::Dyn(_, er)) => {
            if bound(rr) != bound(er) {
                return false;
            }
            if !bound(er) {
                out.push(rr);
            }
            let (ra, ea) = (dyn_arg_tys(tys, r), dyn_arg_tys(tys, e));
            ra.len() == ea.len() && ra.into_iter().zip(ea).all(|(x, y)| regioned_slots(sc, x, y, out))
        }
        (TyKind::FnPtr(_), TyKind::FnPtr(_)) if ptr_free(tys, e).is_some() => {
            out.extend(ptr_free(tys, r).or(Some(Region::Erased)));
            true
        }
        // A bound's type param (`ClosureEntry::bound_output`): the call's
        // instantiation, no written regions.
        (TyKind::Param(_) | TyKind::Projection(..), _) => {
            let n = sc.slots(e) as usize;
            out.extend(std::iter::repeat_n(Region::Erased, n));
            true
        }
        _ => {
            let n = sc.slots(e) as usize;
            out.extend(std::iter::repeat_n(Region::Erased, n));
            r == e || n == 0
        }
    }
}

fn arg_slot_roles<T: TyIntern>(sc: &mut SlotCx<'_, '_, T>, t: Ty, under_mut: bool, out: &mut Vec<Option<(bool, bool)>>) {
    match sc.tys.kind(t) {
        TyKind::Ref(_, m, inner) => {
            out.push(Some((true, under_mut)));
            arg_slot_roles(sc, inner, under_mut || m.is_mut(), out);
        }
        TyKind::Adt(_, args) => {
            let n = adt_regions(sc.p, sc.tys, t) as usize;
            out.extend(std::iter::repeat_n(Some((true, under_mut)), n));
            for g in sc.tys.args(args).to_vec() {
                if let GenericArg::Ty(e) = g {
                    arg_slot_roles(sc, e, under_mut, out);
                }
            }
        }
        TyKind::Tuple(ts) => {
            for e in sc.tys.tys_of(ts).to_vec() {
                arg_slot_roles(sc, e, under_mut, out);
            }
        }
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => arg_slot_roles(sc, e, under_mut, out),
        _ => {
            let n = sc.slots(t) as usize;
            out.extend(std::iter::repeat_n(Some((true, under_mut)), n));
        }
    }
}

/// Walks erased type `t` with slot universals `us` from `*at`, pushing a
/// fact `inner: outer` for every slot inside each enclosing reference.
fn implied_walk<T: TyIntern>(
    sc: &mut SlotCx<'_, '_, T>,
    t: Ty,
    us: &[Univ],
    at: &mut usize,
    outer: &mut Vec<Univ>,
    facts: &mut Vec<(Univ, Univ)>,
) {
    let each = |u: Univ, facts: &mut Vec<(Univ, Univ)>, outer: &Vec<Univ>| {
        for &o in outer {
            facts.push((u, o));
        }
    };
    match sc.tys.kind(t) {
        TyKind::Ref(r, _, inner) if bound(r) => implied_walk(sc, inner, us, at, outer, facts),
        TyKind::Ref(_, _, inner) => {
            let Some(&u) = us.get(*at) else { return };
            each(u, facts, outer);
            *at += 1;
            outer.push(u);
            implied_walk(sc, inner, us, at, outer, facts);
            outer.pop();
        }
        TyKind::Adt(def, args) => {
            let start = *at;
            for _ in 0..adt_regions(sc.p, sc.tys, t) {
                if let Some(&u) = us.get(*at) {
                    each(u, facts, outer);
                }
                *at += 1;
            }
            // The Adt's own outlives facts are implied by its use, and so
            // are the lifetime requirements its fields put (rustc's
            // inferred outlives: `S<'a, 'b> { x: &'a mut W<'b> }` gives
            // `'b: 'a`).
            for &(x, y) in sc.p.regions.adt_facts.get(&def).map_or(&[][..], |v| v.as_slice()) {
                let to = if y == crate::check::generics::STATIC_FACT { Some(0) } else { us.get(start + y as usize).copied() };
                if let (Some(&a), Some(b)) = (us.get(start + x as usize), to) {
                    facts.push((a, b));
                }
            }
            for &(g, r) in sc.p.regions.adt_outlives.get(&def).map_or(&[][..], |v| v.as_slice()) {
                let GenericArg::Lifetime(Region::Param(x)) = g else { continue };
                let to = match r {
                    Region::Static => Some(0),
                    Region::Param(y) => us.get(start + y as usize).copied(),
                    _ => None,
                };
                if let (Some(&a), Some(b)) = (us.get(start + x as usize), to) {
                    facts.push((a, b));
                }
            }
            for g in sc.tys.args(args).to_vec() {
                if let GenericArg::Ty(e) = g {
                    implied_walk(sc, e, us, at, outer, facts);
                }
            }
        }
        TyKind::Tuple(ts) => {
            for e in sc.tys.tys_of(ts).to_vec() {
                implied_walk(sc, e, us, at, outer, facts);
            }
        }
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => implied_walk(sc, e, us, at, outer, facts),
        TyKind::Closure(cdef, args) => {
            // The closure contract: every source outlives every sink.
            let start = *at;
            for e in closure_fields(sc.tys, args) {
                implied_walk(sc, e, us, at, outer, facts);
            }
            let mut roles = Vec::new();
            closure_roles(sc, cdef, args, &mut roles);
            for (i, &(src, _)) in roles.iter().enumerate() {
                for (j, &(_, snk)) in roles.iter().enumerate() {
                    if src && snk && i != j
                        && let (Some(&a), Some(&b)) = (us.get(start + i), us.get(start + j))
                    {
                        facts.push((a, b));
                    }
                }
            }
        }
        // `&'r (dyn Tr + 'o)` gives `'o: 'r`; the trait args imply
        // nothing (an object outlives by its object lifetime alone).
        TyKind::Dyn(_, r) => {
            if !bound(r) {
                let Some(&u) = us.get(*at) else { return };
                each(u, facts, outer);
                *at += 1;
            }
            for e in dyn_arg_tys(sc.tys, t) {
                *at += sc.slots(e) as usize;
            }
        }
        // A fn pointer implies nothing of its free region (rustc's
        // implied bounds do not look into fn pointer types).
        TyKind::FnPtr(_) => *at += sc.slots(t) as usize,
        _ => {}
    }
}

/// The region solution of one body, as the loan checks need it.
pub(super) struct Solution {
    /// Words per locals bitset.
    pub wn: usize,
    /// Per loan (`wn` words each): locals whose slots the loan's region
    /// reaches, and locals whose drop-live slots it reaches.
    pub use_locals: Vec<u64>,
    pub drop_locals: Vec<u64>,
    /// Per loan: its region reaches a universal region (it must outlive the
    /// whole body), and it reaches a slot of the return place.
    pub univ: Vec<bool>,
    pub to_ret: Vec<bool>,
    /// Per local: whether a `Drop` of it is a use of some of its regions.
    pub drop_live: Vec<bool>,
    /// Universal relations that do not hold (L0733).
    pub errs: Vec<Diag>,
    /// In a closure body: every `a: b` between universals its constraints
    /// need (`closure_requirements`).
    pub reqs: Vec<(u32, u32)>,
}

impl Solution {
    pub fn use_set(&self, loan: usize) -> &[u64] {
        &self.use_locals[loan * self.wn..(loan + 1) * self.wn]
    }
    pub fn drop_set(&self, loan: usize) -> &[u64] {
        &self.drop_locals[loan * self.wn..(loan + 1) * self.wn]
    }
}

/// Builds the region constraints of one body and solves them.
pub(super) struct Builder<'b, 'p> {
    p: &'p Program,
    body: &'b Body<'p>,
    sc: SlotCx<'b, 'p, Tys<'p>>,
    own: OwnSig,
    local_base: Vec<u32>,
    /// Per var: owning local + 1, or 0.
    owner: Vec<u32>,
    /// Per var: a drop-live slot of its owner.
    drop_slot: Vec<bool>,
    loan_var: Vec<u32>,
    edges: Vec<(u32, u32)>,
    edge_span: Vec<Span>,
    span: Span,
    /// The loan created by each statement, by body-wide statement index.
    loan_at: &'b [u32],
    stmt_base: &'b [usize],
    /// Errors the constraint walk finds (annotations it cannot follow).
    errs: Vec<Diag>,
    /// While a trait's signature is instantiated over an impl method's
    /// types (`trait_view`): fresh vars per projection, which the impl's
    /// own instantiation constrains.
    proj: Option<FxMap<Ty, Vec<u32>>>,
    /// While a call through an `Fn*` bound instantiates it
    /// (`call_fn_bound`): the one fresh var its elided (higher-ranked)
    /// lifetime takes, so an output elided like an input ties to it.
    bound_var: Option<u32>,
    /// While `call_fn_bound` instantiates a bound's inputs: each elided
    /// lifetime there is its own late-bound region, so each takes a fresh
    /// var, collected here (`Fn(&mut Dec<'_>)` has two).
    bound_each: Option<Vec<u32>>,
    /// The argument slot vars of each closure created here whose
    /// arguments are free (`ClosureEntry::free_args`), by closure def.
    closure_args: FxMap<DefId, Vec<u32>>,
    /// The requirements of each closure created here (`closure_reqs`).
    closure_reqs: FxMap<DefId, Option<std::rc::Rc<Vec<(End, End)>>>>,
    /// The closures a call's `F: Fn*(..)` bounds linked (`link_bound_closure`).
    bound_linked: Vec<DefId>,
    /// The `call_out` closures whose output requirements a call proved
    /// (`flow_closure_output`; `out_reqs_unproved` reports the others).
    out_proved: Vec<DefId>,
    /// While a call of a trait method instantiates its signature: the vars
    /// its first universals (the trait's lifetime params) take
    /// (`trait_lifetime_seeds`); empty otherwise.
    seed_univ: Vec<u32>,
    /// Set by `call_sig_with` when every `Item = T` bound of the callee
    /// was related exactly (`item_bound_flows`), so the call needs no
    /// over-approximation for it.
    item_bound_exact: bool,
    /// The slots of the value the last `store_parts` related exactly.
    store_covered: Vec<bool>,
    /// The builtin whose call the region pass reads, if any: its stores put
    /// each argument whole into the container (`call_opaque_from`).
    cur_builtin: Option<crate::check::Builtin>,
    /// The closures `closure_created` has seen.
    created: FxMap<DefId, ()>,
    /// The last check of the fn whose closures `closure_reqs` lowers
    /// (None when it has errors), shared by its closures.
    root_check: Option<(LocalDefId, Option<crate::check::Checked<'p>>)>,
    /// While a call's signature is instantiated: the erased type each
    /// type param binds (`inst_walk`), for trait-selection checks.
    bind_tys: FxMap<u32, Ty>,
    /// While a vtable call instantiates the trait method's signature: the
    /// vars and types the trait's type params take from the object's trait
    /// args (R11), by param index; empty otherwise.
    seed_binds: Vec<(u32, Vec<u32>, Ty)>,
    /// While `inst_walk` instantiates a signature type: whether the place
    /// is invariant, and whether the dyn type whose trait args hold it
    /// sits in an invariant place (R11; `None` outside dyn args).
    inst_inv: (bool, Option<bool>),
    /// While `call_sig_with` instantiates the return type: the callee's
    /// type flows out, so a late-bound place of the destination's dyn
    /// may not meet the callee's `T` (R11).
    inst_ret: bool,
    /// While `walk` pairs the trait args of two dyn types (R11): the
    /// variance of the dyn types' own position, and the vars of the other
    /// side that a late-bound (`DYN_LATE`) position met.
    dyn_walk: Option<(Variance, Vec<u32>)>,
    /// True while a value flows into a coercion site whose target type is
    /// written: the return place `_0`, or a call argument whose declared
    /// param type is a `RefCell` guard over `dyn Tr` (not a type param).
    /// There a guard's object lifetime may shorten (`relate`,
    /// `call_cell`). Elsewhere a guard stays invariant: lust cannot tell a
    /// coercion site from a move into an inferred place (`let o = Some(g)`).
    guard_coerce: bool,
    /// True while a value flows into a `Body::dyn_coerce` temporary: a
    /// `&mut dyn Tr` coerced at a rustc coercion site, where its object
    /// lifetime may shorten (`relate`). Elsewhere (`let g = c`, `Some(g)`,
    /// a generic argument) `&mut` keeps it invariant.
    dyn_coerce: bool,
    /// The capture var of each local that may hold an `impl Trait` value
    /// (`Body::opaque_locals`): the regions the opaque type captures
    /// (edition 2024: every argument region of the defining call), which
    /// the revealed hidden type may have no slot for (`String` behind
    /// `impl Display`). Owned by the local and drop-live (`cap_flow`).
    cap_var: FxMap<Local, u32>,
    /// The capture vars of the opaque locals the body borrows (`&v`,
    /// `&mut v`, a slice of one): a callee or a write through the borrow
    /// may store an opaque value in them (`v.push(f(&c))`), so the
    /// captures of a value a call takes by value, or one written through
    /// a deref, reach all of them (`cap_reach`).
    borrowed_caps: Vec<u32>,
}

impl<'b, 'p> Builder<'b, 'p> {
    pub fn new(p: &'p Program, body: &'b Body<'p>, own: OwnSig, n_loans: usize, loan_at: &'b [u32], stmt_base: &'b [usize]) -> Self {
        let mut b = Builder {
            p,
            body,
            sc: SlotCx::new(&body.tys, p),
            local_base: Vec::with_capacity(body.locals.len()),
            owner: Vec::new(),
            drop_slot: Vec::new(),
            loan_var: Vec::with_capacity(n_loans),
            edges: Vec::new(),
            edge_span: Vec::new(),
            span: Span::default(),
            loan_at,
            stmt_base,
            own,
            errs: Vec::new(),
            proj: None,
            bound_var: None,
            bound_each: None,
            closure_args: FxMap::default(),
            closure_reqs: FxMap::default(),
            bound_linked: Vec::new(),
            out_proved: Vec::new(),
            seed_univ: Vec::new(),
            item_bound_exact: false,
            store_covered: Vec::new(),
            cur_builtin: None,
            created: FxMap::default(),
            root_check: None,
            bind_tys: FxMap::default(),
            dyn_walk: None,
            guard_coerce: false,
            dyn_coerce: false,
            inst_inv: (false, None),
            inst_ret: false,
            seed_binds: Vec::new(),
            cap_var: FxMap::default(),
            borrowed_caps: Vec::new(),
        };
        // Vars 0..=n_univ: 'static and the universals.
        for _ in 0..=b.own.n_univ {
            b.owner.push(0);
            b.drop_slot.push(false);
        }
        let drops = !super::drop_heads(p).is_empty()
            || p.regions.adts(p).any_drop
            || body.locals.iter().any(|d| drops_guard(&body.tys, d.ty) || owns_dyn(&body.tys, d.ty));
        for (l, decl) in body.locals.iter().enumerate() {
            let n = b.local_slots(l as Local);
            let base = b.owner.len() as u32;
            b.local_base.push(base);
            let mut dl = vec![false; n as usize];
            let opaque = body.opaque_locals.contains(&(l as Local));
            let opaque_drop = opaque && !body.opaque_nodrop.contains(&(l as Local));
            if opaque_drop {
                // An `impl Trait` value's unknown destructor may use every
                // region it captures (W-CHECK-G3, `Body::opaque_locals`).
                dl = vec![true; n as usize];
            } else if drops && n > 0 && !fat_local(&body.tys, decl.ty) {
                b.sc.drop_slots(decl.ty, DropMode::Owned, 0, &mut dl);
            }
            for i in 0..n as usize {
                b.owner.push(l as u32 + 1);
                b.drop_slot.push(dl[i]);
            }
            if opaque {
                b.cap_var.insert(l as Local, b.owner.len() as u32);
                b.owner.push(l as u32 + 1);
                b.drop_slot.push(opaque_drop);
            }
        }
        for _ in 0..n_loans {
            let v = b.fresh();
            b.loan_var.push(v);
        }
        if !b.cap_var.is_empty() {
            for s in body.blocks.iter().flat_map(|bl| &bl.stmts) {
                if let StmtKind::Assign(_, Rvalue::Ref(_, pl) | Rvalue::SliceOf(pl)) = &s.kind
                    && !pl.proj.contains(&Proj::Deref)
                    && let Some(&c) = b.cap_var.get(&pl.local)
                    && !b.borrowed_caps.contains(&c)
                {
                    b.borrowed_caps.push(c);
                }
            }
        }
        b
    }

    fn fresh(&mut self) -> u32 {
        self.owner.push(0);
        self.drop_slot.push(false);
        (self.owner.len() - 1) as u32
    }

    fn edge(&mut self, sup: u32, sub: u32) {
        if sup != sub && sup != 0 {
            self.edges.push((sup, sub));
            self.edge_span.push(self.span);
        }
    }

    /// Edges for slot `x` of a subtype against slot `y` of its supertype.
    fn edge_v(&mut self, x: u32, y: u32, v: Variance) {
        match v {
            Variance::Co => self.edge(x, y),
            Variance::Contra => self.edge(y, x),
            Variance::Inv => {
                self.edge(x, y);
                self.edge(y, x);
            }
            Variance::Bi => {}
        }
    }

    /// Makes every var in `a` and `b` equal, through one hub var.
    fn equate_all(&mut self, a: &[u32], b: &[u32]) {
        if a.len() + b.len() < 2 {
            return;
        }
        let h = self.fresh();
        for &x in a.iter().chain(b) {
            self.edge(x, h);
            self.edge(h, x);
        }
    }

    /// Every var of `from` outlives every var of `to` (through a hub).
    fn flow_all(&mut self, from: &[u32], to: &[u32]) {
        if from.is_empty() || to.is_empty() {
            return;
        }
        let h = self.fresh();
        for &x in from {
            self.edge(x, h);
        }
        for &y in to {
            self.edge(h, y);
        }
    }

    /// The slot count of a local: its type's, plus one leading pointer
    /// slot for a bare slice or `str` local (lowering keeps a subslice in
    /// such a fat-pointer temporary before it becomes a reference).
    fn local_slots(&mut self, l: Local) -> u32 {
        let t = self.body.locals[l as usize].ty;
        self.sc.slots(t) + u32::from(fat_local(&self.body.tys, t))
    }

    fn local_vars(&mut self, l: Local, out: &mut Vec<u32>) {
        let base = self.local_base[l as usize];
        let n = self.local_slots(l);
        out.clear();
        out.extend(base..base + n);
    }

    /// The erased type of `place` and its slot vars, and the reborrow chain
    /// (one `(region var, mutable)` per dereferenced reference, in order).
    /// A projection lust cannot follow exactly returns `ERROR` with the
    /// vars reached so far; relating it equates everything (conservative).
    fn place(&mut self, place: &Place, out: &mut Vec<u32>, derefs: &mut Vec<(u32, bool)>) -> Ty {
        self.local_vars(place.local, out);
        derefs.clear();
        let mut ty = self.body.locals[place.local as usize].ty;
        if fat_local(&self.body.tys, ty) {
            // A fat-pointer local reads as the reference it stands for; an
            // index into it goes through that pointer (a reborrow of it).
            if let Some(Proj::Index(_)) = place.proj.first() {
                derefs.push((out[0], false));
                out.remove(0);
            } else {
                match self.body.tys.get(TyKind::Ref(Region::Erased, Mut::Shared, ty)) {
                    Some(r) => ty = r,
                    None => return ERROR,
                }
            }
        }
        let mut variant = 0u32;
        for pr in &place.proj {
            let tys = &self.body.tys;
            match *pr {
                Proj::Downcast(v) => variant = v,
                Proj::Deref => match tys.kind(ty) {
                    TyKind::Ref(_, m, inner) => {
                        derefs.push((out[0], m.is_mut()));
                        out.remove(0);
                        ty = inner;
                    }
                    TyKind::Adt(..) if tys.guard_elem(ty).is_some() => {
                        // A `RefCell` guard derefs like the reference it
                        // stands for: its own region leads, then the value's.
                        // The deref is `Deref::deref(&self)`, a borrow of the
                        // guard, so a reborrow chain goes on past it (as past
                        // a `&mut`) to the reference that reached the guard.
                        let (inner, _) = tys.guard_elem(ty).unwrap();
                        derefs.push((out[0], true));
                        out.remove(0);
                        let n = self.sc.slots(inner) as usize;
                        out.truncate(n);
                        ty = inner;
                    }
                    TyKind::Adt(..) if tys.adt_first_ty_arg(ty).is_some() && !tys.is_chars_ty(ty) => {
                        // A smart pointer (`Box<T>`): its pointee is its first type arg.
                        let inner = tys.adt_first_ty_arg(ty).unwrap();
                        let n = self.sc.slots(inner) as usize;
                        out.truncate(n);
                        ty = inner;
                    }
                    _ => return ERROR,
                },
                Proj::Field(i) => {
                    let next = self.field(ty, variant, i, out);
                    variant = 0;
                    match next {
                        Some(t) => ty = t,
                        None => return ERROR,
                    }
                }
                Proj::Index(_) => match tys.kind(ty) {
                    TyKind::Array(e, _) | TyKind::Slice(e) => ty = e,
                    _ => match tys.vec_elem(ty) {
                        Some(e) => ty = e,
                        None => return ERROR,
                    },
                },
            }
        }
        ty
    }

    /// Steps `out` (the vars of a value of type `ty`) to field `i` of
    /// `variant`; returns the field's erased type.
    fn field(&mut self, ty: Ty, variant: u32, i: u32, out: &mut Vec<u32>) -> Option<Ty> {
        let tys = &self.body.tys;
        match tys.kind(ty) {
            TyKind::Tuple(ts) => {
                let elems = tys.tys_of(ts).to_vec();
                self.sub_range(&elems, i as usize, 0, out)
            }
            TyKind::Closure(_, args) => {
                let elems = closure_fields(tys, args);
                self.sub_range(&elems, i as usize, 0, out)
            }
            TyKind::Adt(def, args) => {
                if let Some(e) = tys.option_elem(ty) {
                    return Some(e);
                }
                if let Some((t, e)) = tys.result_args(ty) {
                    let elems = [t, e];
                    return self.sub_range(&elems, if variant == 0 { 0 } else { 1 }, 0, out);
                }
                let tmpl = self.p.defs.local_adt(def)?;
                let ftmpl = self.p.adt(tmpl).variants.get(variant as usize)?.fields.get(i as usize)?.ty;
                let gargs = tys.args(args).to_vec();
                // The vars of each type arg inside `out`.
                let mut ranges: Vec<(usize, usize)> = Vec::with_capacity(gargs.len());
                let mut at = adt_regions(self.p, tys, ty) as usize;
                for g in &gargs {
                    let n = match g {
                        GenericArg::Ty(e) => self.sc.slots(*e) as usize,
                        _ => 0,
                    };
                    ranges.push((at, n));
                    at += n;
                }
                // The field's regioned form names the Adt's lifetime params;
                // without one (no references written) the erased template is
                // the same shape.
                let freg = self.p.regions.adt_fields.get(&def).and_then(|v| v.get(variant as usize)).and_then(|f| f.get(i as usize)).copied();
                let mut sub = Vec::new();
                self.subst_vars(freg.unwrap_or(ftmpl), &ranges, out, &mut sub);
                let fty = subst_get(&self.body.tys, ftmpl, &gargs)
                    .or_else(|| {
                        let a = self.body.tys.local_adt(ty)?;
                        Some(self.p.adt(a).variants.get(variant as usize)?.fields.get(i as usize)?.ty)
                    })?;
                if self.sc.slots(fty) as usize != sub.len() {
                    return None;
                }
                *out = sub;
                Some(fty)
            }
            _ => None,
        }
    }

    /// Narrows `out` to the vars of element `i` of `elems` (laid out in
    /// order after `skip` leading vars).
    fn sub_range(&mut self, elems: &[Ty], i: usize, skip: usize, out: &mut Vec<u32>) -> Option<Ty> {
        let mut at = skip;
        for (k, &e) in elems.iter().enumerate() {
            let n = self.sc.slots(e) as usize;
            if k == i {
                let v: Vec<u32> = out.get(at..at + n)?.to_vec();
                *out = v;
                return Some(e);
            }
            at += n;
        }
        None
    }

    /// The vars of regioned field type `f` (template form) under the Adt's
    /// vars: its lifetime param `k` is `vars[k]`, type param `j` the vars in
    /// `ranges[j]`, `'static` var 0.
    fn subst_vars(&mut self, f: Ty, ranges: &[(usize, usize)], vars: &[u32], out: &mut Vec<u32>) {
        let tys = &self.p.tys;
        let region = |r: Region| match r {
            Region::Param(k) => vars.get(k as usize).copied().unwrap_or(0),
            _ => 0,
        };
        match tys.kind(f) {
            TyKind::Param(j) => {
                if let Some(&(s, n)) = ranges.get(j.0 as usize) {
                    out.extend_from_slice(&vars[s.min(vars.len())..(s + n).min(vars.len())]);
                }
            }
            TyKind::Ref(r, _, inner) => {
                if !bound(r) {
                    out.push(region(r));
                }
                self.subst_vars(inner, ranges, vars, out);
            }
            TyKind::Adt(_, args) => {
                let lts: Vec<Region> = tys.args(args).iter().filter_map(|g| if let GenericArg::Lifetime(r) = g && *r != crate::ty::DYN_LATE { Some(*r) } else { None }).collect();
                for k in 0..adt_regions(self.p, tys, f) as usize {
                    out.push(lts.get(k).map_or(0, |&r| region(r)));
                }
                for g in tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.subst_vars(e, ranges, vars, out);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in tys.tys_of(ts).to_vec() {
                    self.subst_vars(e, ranges, vars, out);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.subst_vars(e, ranges, vars, out),
            TyKind::Closure(_, args) => {
                for e in closure_fields(tys, args) {
                    self.subst_vars(e, ranges, vars, out);
                }
            }
            // A `dyn` type's object lifetime: an Adt lifetime param, else
            // `'static` (`Box<dyn Tr>` in a field); then its trait args'.
            TyKind::Dyn(_, r) => {
                if !bound(r) {
                    out.push(region(r));
                }
                for e in dyn_arg_tys(tys, f) {
                    self.subst_vars(e, ranges, vars, out);
                }
            }
            _ => {}
        }
    }

    /// Adds the edges for `a <: b` at variance `v`. Returns false (after
    /// equating every slot of both sides) when the shapes cannot be paired.
    fn relate(&mut self, a: Ty, av: &[u32], b: Ty, bv: &[u32], v: Variance) -> bool {
        if av.is_empty() && bv.is_empty() {
            return true;
        }
        // At a coercion site rustc may shorten the object lifetime of the
        // outermost `&`/`&mut dyn` (`&'r mut (dyn Tr + 'a)` to `&'r mut
        // (dyn Tr + 'b)`, `'a: 'b`), which plain `&mut` invariance would
        // equate: a `dyn_coerce` temporary, or a written target
        // (`guard_coerce`). The `RefCell` guards coerce the same way
        // (`RefMut<'r, dyn Tr + 'a>`, std's `CoerceUnsized`), only at a
        // written target; their one region slot comes first too.
        if v == Variance::Co
            && let Some((ai, bi)) = outer_dyn_pointees(&self.body.tys, a, b, self.dyn_coerce || self.guard_coerce, self.guard_coerce)
            && !av.is_empty()
            && !bv.is_empty()
        {
            self.edge(av[0], bv[0]);
            let (mut ia, mut ib) = (1usize, 1usize);
            if self.walk(ai, av, &mut ia, bi, bv, &mut ib, Variance::Co) && ia == av.len() && ib == bv.len() {
                return true;
            }
            self.equate_all(av, bv);
            return false;
        }
        // The same type pairs slot by slot; a fn pointer's free slot needs
        // its signature's variances (`walk`, `ptr_to_ptr`).
        if a == b && a != ERROR && av.len() == bv.len() && !store::has_fn_ptr(&self.body.tys, a) {
            let mut pairs: Vec<(u32, Variance)> = Vec::with_capacity(av.len());
            self.sc.each_slot(a, v, 0, &mut |i, var| pairs.push((i, var)));
            for (i, var) in pairs {
                self.edge_v(av[i as usize], bv[i as usize], var);
            }
            return true;
        }
        let (mut ia, mut ib) = (0usize, 0usize);
        if a != ERROR && b != ERROR && self.walk(a, av, &mut ia, b, bv, &mut ib, v) && ia == av.len() && ib == bv.len() {
            return true;
        }
        self.equate_all(av, bv);
        false
    }

    /// Pairs one region position of `walk` (a reference's region or an
    /// object lifetime): two slots relate at `v`. Inside a dyn's trait
    /// args (`dyn_walk`), a late-bound (`DYN_LATE`) position has no slot:
    /// it may meet a free slot of the other side only on the subtype
    /// side of a covariant pair (or the supertype side of a
    /// contravariant one), and then ties that slot; any other mix is a
    /// "not general enough" error. False when a slot is missing.
    #[allow(clippy::too_many_arguments)]
    fn late_pair(&mut self, ra: Region, av: &[u32], ia: &mut usize, rb: Region, bv: &[u32], ib: &mut usize, v: Variance) -> bool {
        match (bound(ra), bound(rb)) {
            (false, false) => {
                let (Some(&x), Some(&y)) = (av.get(*ia), bv.get(*ib)) else { return false };
                self.edge_v(x, y, v);
                *ia += 1;
                *ib += 1;
            }
            (true, true) => {}
            (late_a, _) => {
                let dyn_v = self.dyn_walk.as_ref().map_or(Variance::Inv, |w| w.0);
                let ok = if late_a { dyn_v == Variance::Co } else { dyn_v == Variance::Contra };
                let (vs, i) = if late_a { (bv, &mut *ib) } else { (av, &mut *ia) };
                let Some(&y) = vs.get(*i) else { return false };
                *i += 1;
                if ok && let Some(w) = self.dyn_walk.as_mut() {
                    w.1.push(y);
                } else {
                    self.dyn_not_general();
                }
            }
        }
        true
    }

    /// L0735: two dyn types whose trait args differ in which regions the
    /// object binds itself (rustc E0308, "one type is more general than
    /// the other").
    fn dyn_not_general(&mut self) {
        self.errs.push(Diag::new(
            "L0735",
            self.span,
            "mismatched `dyn` types: one is more general than the other (a lifetime the object takes for any region meets a fixed one)",
            "Make both types elide the same lifetimes, or both name them.",
        ));
    }

    #[allow(clippy::too_many_arguments)]
    fn walk(&mut self, a: Ty, av: &[u32], ia: &mut usize, b: Ty, bv: &[u32], ib: &mut usize, v: Variance) -> bool {
        let tys = &self.body.tys;
        match (tys.kind(a), tys.kind(b)) {
            (TyKind::Ref(ra, am, ai), TyKind::Ref(rb, bm, bi)) => {
                if !self.late_pair(ra, av, ia, rb, bv, ib, v) {
                    return false;
                }
                let iv = if am.is_mut() && bm.is_mut() { Variance::Inv } else { Variance::Co };
                self.walk(ai, av, ia, bi, bv, ib, v.then(iv))
            }
            (TyKind::Ref(_, _, ai), TyKind::RawPtr(bm, bi)) => {
                *ia += 1;
                self.walk(ai, av, ia, bi, bv, ib, v.then(if bm.is_mut() { Variance::Inv } else { Variance::Co }))
            }
            (TyKind::Adt(ad, aa), TyKind::Adt(bd, ba)) if ad == bd => {
                // A lifetime a dyn's sugar marks as its own (`DYN_LATE`,
                // R11) has no slot; `late_pair` pairs the rest.
                let (la, lb) = (adt_late_marks(tys, aa), adt_late_marks(tys, ba));
                let n = adt_regions(self.p, tys, a) as usize + la.iter().filter(|&&x| x).count();
                for k in 0..n {
                    let rv = if tys.builtin_of(a).is_some() { builtin_region_variance(tys, a) } else { self.p.regions.adts(self.p).region_modes(ad, k).0 };
                    let mark = |l: &[bool]| if l.get(k) == Some(&true) { crate::ty::DYN_LATE } else { Region::Erased };
                    if !self.late_pair(mark(&la), av, ia, mark(&lb), bv, ib, v.then(rv)) {
                        return false;
                    }
                }
                let (xs, ys) = (tys.args(aa).to_vec(), tys.args(ba).to_vec());
                if xs.len() != ys.len() {
                    return false;
                }
                for (j, (x, y)) in xs.into_iter().zip(ys).enumerate() {
                    if let (GenericArg::Ty(x), GenericArg::Ty(y)) = (x, y) {
                        let (pv, _) = self.p.regions.adts(self.p).arg_modes(self.p, ad, j);
                        if !self.walk(x, av, ia, y, bv, ib, v.then(pv)) {
                            return false;
                        }
                    }
                }
                true
            }
            (TyKind::Adt(..), TyKind::Slice(be)) if tys.vec_elem(a).is_some() => {
                let ae = tys.vec_elem(a).unwrap();
                self.walk(ae, av, ia, be, bv, ib, v)
            }
            (TyKind::Tuple(x), TyKind::Tuple(y)) => {
                let (xs, ys) = (tys.tys_of(x).to_vec(), tys.tys_of(y).to_vec());
                xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| self.walk(x, av, ia, y, bv, ib, v))
            }
            (TyKind::Array(x, _) | TyKind::Slice(x), TyKind::Array(y, _) | TyKind::Slice(y)) => self.walk(x, av, ia, y, bv, ib, v),
            (TyKind::RawPtr(m, x), TyKind::RawPtr(_, y)) => {
                self.walk(x, av, ia, y, bv, ib, v.then(if m.is_mut() { Variance::Inv } else { Variance::Co }))
            }
            (TyKind::Closure(x, xa), TyKind::Closure(y, ya)) if x == y => {
                let (xs, ys) = (closure_fields(tys, xa), closure_fields(tys, ya));
                xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| self.walk(x, av, ia, y, bv, ib, Variance::Inv))
            }
            (TyKind::Dyn(_, ra), TyKind::Dyn(_, rb)) => {
                if !self.late_pair(ra, av, ia, rb, bv, ib, v.then(Variance::Co)) {
                    return false;
                }
                // The trait args (R11): invariant. A late-bound position
                // of the subtype may meet a free one of the supertype
                // (`dyn for<'r> Fn(&'r u8)` is a `dyn Fn(&'x u8)`); the
                // free ones it meets are one region then (its output is
                // its input's).
                let (xs, ys) = (dyn_arg_tys(tys, a), dyn_arg_tys(tys, b));
                if xs.len() != ys.len() {
                    return false;
                }
                let outer = self.dyn_walk.replace((v, Vec::new()));
                let ok = xs.into_iter().zip(ys).all(|(x, y)| self.walk(x, av, ia, y, bv, ib, Variance::Inv));
                let (_, tied) = std::mem::replace(&mut self.dyn_walk, outer).unwrap_or((v, Vec::new()));
                for w in tied.windows(2) {
                    self.edge(w[0], w[1]);
                    self.edge(w[1], w[0]);
                }
                ok
            }
            // Fn pointers with a free region (W-BORROW3): the coercion
            // proof; two without one are check's (`sig_static_mismatch`).
            (TyKind::FnPtr(_), TyKind::FnPtr(_)) => {
                let (na, nb) = (self.sc.slots(a) as usize, self.sc.slots(b) as usize);
                let fa = if na == 1 { av.get(*ia).copied() } else { None };
                let fb = if nb == 1 { bv.get(*ib).copied() } else { None };
                *ia += na;
                *ib += nb;
                if na + nb > 0 {
                    self.ptr_to_ptr(a, fa, b, fb, v);
                }
                true
            }
            _ => self.sc.slots(a) == 0 && self.sc.slots(b) == 0,
        }
    }
}

/// One region place of a `dyn Fn*` signature (`dyn_positions`): the
/// object's own late-bound region, or a var (the object's slot, or 0).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Pos {
    Late,
    Var(u32),
}

/// Callee signature shapes the call rules distinguish.
enum Callee<'s> {
    /// A fn with a region signature: precise instantiation.
    Sig(&'s RegionSig),
    /// A closure body fn: env first, captured regions and output one class.
    Closure,
    /// Anything else: results may hold any argument's regions.
    Opaque,
}

impl<'b, 'p> Builder<'b, 'p> {
    /// The region of each slot of erased type `e` under its regioned
    /// annotation `r` (`Erased` where the annotation left it free). False
    /// when the two shapes differ.
    fn annotation_regions(&mut self, r: Ty, e: Ty, out: &mut Vec<Region>) -> bool {
        let et = &self.body.tys;
        match (et.kind(r), et.kind(e)) {
            (TyKind::Ref(rr, rm, ri), TyKind::Ref(er, em, ei)) if rm == em => {
                if bound(rr) != bound(er) {
                    return false;
                }
                if !bound(er) {
                    out.push(rr);
                }
                self.annotation_regions(ri, ei, out)
            }
            (TyKind::Adt(rd, ra), TyKind::Adt(ed, ea)) if rd == ed => {
                let lts: Vec<Region> = et.args(ra).iter().filter_map(|g| if let GenericArg::Lifetime(x) = g && *x != crate::ty::DYN_LATE { Some(*x) } else { None }).collect();
                for k in 0..adt_regions(self.p, et, e) as usize {
                    out.push(lts.get(k).copied().unwrap_or(Region::Erased));
                }
                let rargs: Vec<Ty> = et.args(ra).iter().filter_map(|g| g.as_ty()).collect();
                let eargs: Vec<Ty> = et.args(ea).iter().filter_map(|g| g.as_ty()).collect();
                rargs.len() == eargs.len() && rargs.into_iter().zip(eargs).all(|(x, y)| self.annotation_regions(x, y, out))
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                let (xs, ys) = (et.tys_of(a).to_vec(), et.tys_of(b).to_vec());
                xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| self.annotation_regions(x, y, out))
            }
            (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
                self.annotation_regions(a, b, out)
            }
            (TyKind::Dyn(_, rr), TyKind::Dyn(_, er)) => {
                if bound(rr) != bound(er) {
                    return false;
                }
                if !bound(er) {
                    out.push(if crate::check::object::dyn_is_static(self.p, et, e) { Region::Static } else { rr });
                }
                let (ra, ea) = (dyn_arg_tys(et, r), dyn_arg_tys(et, e));
                ra.len() == ea.len() && ra.into_iter().zip(ea).all(|(x, y)| self.annotation_regions(x, y, out))
            }
            (TyKind::FnPtr(_), TyKind::FnPtr(_)) if ptr_free(et, e).is_some() => match ptr_free(et, r) {
                Some(rr) => {
                    out.push(rr);
                    true
                }
                None => false,
            },
            _ => r == e || self.sc.slots(e) == 0,
        }
    }

    /// The vars of an operand (empty for constants, which hold only
    /// `'static` data) and its erased type (`ERROR` for constants).
    fn operand(&mut self, o: &Operand, out: &mut Vec<u32>) -> Ty {
        match o {
            Operand::Copy(p) | Operand::Move(p) => {
                let mut d = Vec::new();
                self.place(p, out, &mut d)
            }
            Operand::Const(_) => {
                out.clear();
                ERROR
            }
        }
    }

    /// Relates operand `o` into the place reached by `dest` plus `proj`.
    fn into_place(&mut self, o: &Operand, dest: &Place, proj: &[Proj]) {
        let mut ov = Vec::new();
        let ot = self.operand(o, &mut ov);
        if ov.is_empty() {
            return;
        }
        let mut target = dest.clone();
        target.proj.extend_from_slice(proj);
        let (mut dv, mut d) = (Vec::new(), Vec::new());
        let dt = self.place(&target, &mut dv, &mut d);
        self.relate(ot, &ov, dt, &dv, Variance::Co);
    }

    /// The constraints of every statement, terminator, and the entry.
    pub fn build(&mut self) {
        // Every local's type is well formed (`&'a T` needs `T: 'a`), and a
        // region the erased type kept (`&'static dyn Tr`, see
        // `check::object`) is `'static`.
        let mut vars = Vec::new();
        let mut regs = Vec::new();
        // A late-bound region of `dyn Fn*` sugar outside its object (R11)
        // would read as no slot: check maps them back (`ty::unbind`), and
        // one it missed is a cut, never a silent hole.
        if self.body.locals.iter().any(|d| self.body.tys.flags(d.ty).contains_loose_bound()) {
            self.errs.push(Diag::new(
                "L0203",
                self.span,
                "a value whose type holds a late-bound lifetime of a `dyn Fn` type is not supported yet",
                "Annotate the value's type with an owned type, or take it through a generic `F: Fn(..)` parameter.",
            ));
        }
        for l in 0..self.body.locals.len() {
            let t = self.body.locals[l].ty;
            if self.sc.slots(t) == 0 {
                continue;
            }
            self.local_vars(l as Local, &mut vars);
            let skip = usize::from(fat_local(&self.body.tys, t));
            let inner = vars[skip..].to_vec();
            self.implied_edges(t, &inner, &mut 0, &mut Vec::new());
            self.static_bound_edges(t, &inner, &mut 0);
            regs.clear();
            self.sc.slot_regions(t, &mut regs);
            for (i, r) in regs.iter().enumerate() {
                if *r == Region::Static
                    && let Some(&v) = inner.get(i)
                {
                    self.edge(v, 0);
                }
            }
        }
        // `let` annotations with explicit lifetimes (W-BORROW): the local's
        // regions equal the written ones (`'static`, or a named lifetime of
        // the fn); an elided one is free.
        for &(l, r) in &self.body.annotations.clone() {
            self.local_vars(l, &mut vars);
            let t = self.body.locals[l as usize].ty;
            let mut regs = Vec::new();
            let ok = !fat_local(&self.body.tys, t) && self.annotation_regions(r, t, &mut regs) && regs.len() == vars.len();
            if !ok {
                self.errs.push(Diag::new(
                    "L0203",
                    self.p.fn_def(self.body.fn_id).name_span,
                    "an explicit lifetime in a `let` annotation here is not supported yet",
                    "Drop the lifetime from the annotation, or write `'_`.",
                ));
                continue;
            }
            for (i, reg) in regs.into_iter().enumerate() {
                match reg {
                    Region::Static => self.edge(vars[i], 0),
                    Region::Param(k) if self.own.closure => {
                        let _ = k;
                        self.errs.push(Diag::new(
                            "L0203",
                            self.p.fn_def(self.body.fn_id).name_span,
                            "a named lifetime in a `let` annotation inside a closure is not supported yet",
                            "Drop the lifetime from the annotation, or write `'_`.",
                        ));
                    }
                    Region::Param(k) if k < self.own.n_univ => {
                        let u = k + 1;
                        self.edge(vars[i], u);
                        self.edge(u, vars[i]);
                    }
                    _ => {}
                }
            }
        }
        // Entry: parameter locals and the return place equal the signature.
        let ret_vars = self.own.ret_vars.clone();
        for l in 0..=self.body.arg_count.min(self.own.slots.len().saturating_sub(1)) {
            let base = self.local_base[l];
            for (i, u) in self.own.slots[l].clone().into_iter().enumerate() {
                if l == 0
                    && let (Some((outlives, _)), Some(rc)) = (&ret_vars, self.own.ret_cap)
                {
                    self.edge(base + i as u32, rc);
                    for &b in outlives {
                        self.edge(base + i as u32, b);
                    }
                    continue;
                }
                self.edge(base + i as u32, u);
                self.edge(u, base + i as u32);
            }
        }
        if let (Some(rc), Some(&c)) = (self.own.ret_cap, self.cap_var.get(&0)) {
            self.edge(c, rc);
            if ret_vars.is_none() {
                self.edge(rc, c);
            }
        }
        if let Some((_, Some(item))) = ret_vars {
            self.rpit_item_edges(item);
        }
        // The hidden type's type params outlive each lifetime an `impl
        // Trait + 'a` return names (rustc E0309): `-> impl Sized + 's { t }`
        // with `t: T` needs `T: 's`.
        if let Some((outlives, _)) = &ret_vars
            && self.own.check
        {
            let t = self.body.locals[0].ty;
            for &b in outlives {
                self.hidden_params_outlive(t, b);
            }
        }
        let body = self.body;
        for (bi, b) in body.blocks.iter().enumerate() {
            for (si, s) in b.stmts.iter().enumerate() {
                self.span = s.span;
                if let StmtKind::Assign(dest, rv) = &s.kind {
                    self.assign(bi, si, dest, rv);
                }
            }
            self.span = b.term_span;
            if let Terminator::Call { target, args, dest, .. } = &b.term {
                self.cur_builtin = if let CallTarget::Builtin(b) = target { Some(*b) } else { None };
                self.call(*target, args, dest);
                self.cur_builtin = None;
            }
        }
        self.out_reqs_unproved();
    }

    /// A `call_out` closure created in this body whose body needs
    /// something of its output slots (`(Out(k), x)` in `closure_reqs`, or
    /// requirements lust could not compute) that no call proved
    /// (`out_proved`): the body did not report it, so it is an error here.
    fn out_reqs_unproved(&mut self) {
        if !self.own.check {
            return;
        }
        let p = self.p;
        let mut seen: Vec<DefId> = Vec::new();
        for l in 0..self.body.locals.len() {
            let mut t = self.body.locals[l].ty;
            while let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
                t = inner;
            }
            let TyKind::Closure(def, args) = self.body.tys.kind(t) else { continue };
            let Some(c) = p.gx.closures.get(&def) else { continue };
            if !c.call_out || c.parent != self.body.fn_id || seen.contains(&def) || self.out_proved.contains(&def) {
                continue;
            }
            seen.push(def);
            let mut roles = Vec::new();
            closure_roles(&mut self.sc, def, args, &mut roles);
            let needs = match self.closure_reqs(def, &roles) {
                Some(reqs) => reqs.iter().any(|(x, _)| matches!(x, End::Out(_))),
                None => true,
            };
            if needs {
                self.errs.push(Diag::new(
                    "L0733",
                    p.fn_def(c.body_fn).name_span,
                    "lifetime may not live long enough: lust cannot prove what this closure's return value needs of the call's types",
                    "Return a value whose regions come from the closure's arguments or captures only, or annotate the closure's return type.",
                ));
            }
        }
    }

    /// The loan of the `Subslice` statement that assigns the slice pattern
    /// temporary `t` (`Body::pat_subslice`), or `u32::MAX`.
    fn subslice_loan(&self, t: Local) -> u32 {
        for (bi, b) in self.body.blocks.iter().enumerate() {
            for (si, s) in b.stmts.iter().enumerate() {
                if let StmtKind::Assign(dest, Rvalue::Subslice { .. }) = &s.kind
                    && dest.local == t
                    && dest.proj.is_empty()
                {
                    return self.loan_at[self.stmt_base[bi] + si];
                }
            }
        }
        u32::MAX
    }

    /// Carries the capture vars (`cap_var`) of the opaque locals `srcs`
    /// moves or copies into `dest`: into the dest local's capture var,
    /// or into every slot of a dest that has none (a reference to an
    /// opaque value, a `Box<dyn Tr>` made from one).
    fn cap_flow(&mut self, srcs: &[&Operand], dest: &Place) {
        let caps = self.caps_of(srcs.iter().copied());
        self.cap_into(&caps, dest);
    }

    /// Makes the vars `caps`, and the captures of every borrowed opaque
    /// local, outlive each borrowed opaque local's capture var
    /// (`borrowed_caps`): what one of them holds may move to another
    /// through the borrows (`mem::swap(&mut a, &mut b)`).
    fn cap_reach(&mut self, caps: &[u32]) {
        if self.borrowed_caps.is_empty() {
            return;
        }
        let to = self.borrowed_caps.clone();
        let from: Vec<u32> = caps.iter().chain(&to).copied().collect();
        self.flow_all(&from, &to);
    }

    /// The capture vars of the opaque locals the operands read.
    fn caps_of<'o>(&self, ops: impl Iterator<Item = &'o Operand>) -> Vec<u32> {
        ops.filter_map(|o| match o {
            Operand::Move(pl) | Operand::Copy(pl) => self.cap_var.get(&pl.local).copied(),
            _ => None,
        })
        .collect()
    }

    /// Makes the vars `caps` outlive what `dest` captures (`cap_flow`).
    /// A write through a deref may land in any borrowed opaque local.
    fn cap_into(&mut self, caps: &[u32], dest: &Place) {
        if caps.is_empty() {
            return;
        }
        if dest.proj.contains(&Proj::Deref) {
            self.cap_reach(caps);
        }
        if let Some(&dc) = self.cap_var.get(&dest.local) {
            self.flow_all(caps, &[dc]);
            return;
        }
        let (mut dv, mut d) = (Vec::new(), Vec::new());
        self.place(dest, &mut dv, &mut d);
        self.flow_all(caps, &dv);
    }

    /// The region var of `dest`'s own reference when its type is a
    /// reference with a region slot (`&'r T`), else None.
    fn ref_lead_var(&mut self, dest: &Place) -> Option<u32> {
        let (mut dv, mut d) = (Vec::new(), Vec::new());
        let dt = self.place(dest, &mut dv, &mut d);
        match self.body.tys.kind(dt) {
            TyKind::Ref(r, _, _) if !bound(r) => dv.first().copied(),
            _ => None,
        }
    }

    fn assign(&mut self, bi: usize, si: usize, dest: &Place, rv: &Rvalue) {
        if !self.cap_var.is_empty() {
            // Only the rvalues that move or copy a value into the result
            // carry its captures; a comparison or a format reads it.
            match rv {
                Rvalue::Use(o)
                | Rvalue::Cast(o, _)
                | Rvalue::Opt(_, Some(o))
                | Rvalue::Res(_, _, o)
                | Rvalue::MakeDyn { ptr: o, .. }
                | Rvalue::DynUpcast { ptr: o, .. }
                | Rvalue::DynData { ptr: o, .. }
                | Rvalue::VecRepeat(_, o, _)
                | Rvalue::ArrayRepeat(_, o, _) => self.cap_flow(&[o], dest),
                Rvalue::Aggregate(_, _, ops) | Rvalue::VecLit(_, ops) | Rvalue::TupleAgg(_, ops) | Rvalue::ArrayAgg(_, ops) => {
                    let ops: Vec<&Operand> = ops.iter().collect();
                    self.cap_flow(&ops, dest);
                }
                // A reference to an opaque value holds what it captures
                // (`&'r Opaque<'s>` needs `'s: 'r`): into the reference's
                // own region only. The pointee's slots are the place's
                // (the Ref rule relates them); a revealed closure's
                // `'static` dyn capture there is no bound on `'s`.
                Rvalue::Ref(_, pl) => {
                    if let Some(&c) = self.cap_var.get(&pl.local) {
                        let lead = (!self.cap_var.contains_key(&dest.local) && !dest.proj.contains(&Proj::Deref))
                            .then(|| self.ref_lead_var(dest))
                            .flatten();
                        match lead {
                            Some(r) => self.edge(c, r),
                            None => self.cap_into(&[c], dest),
                        }
                    }
                }
                _ => {}
            }
        }
        let (mut dv, mut d) = (Vec::new(), Vec::new());
        match rv {
            Rvalue::Use(o) | Rvalue::Cast(o, _) => {
                let mut ov = Vec::new();
                let ot = self.operand(o, &mut ov);
                if ov.is_empty() && ptr_free(&self.body.tys, self.body.locals[dest.local as usize].ty).is_none() {
                    return;
                }
                let dt = self.place(dest, &mut dv, &mut d);
                self.guard_coerce = dest.local == 0 && dest.proj.is_empty();
                self.dyn_coerce = dest.proj.is_empty() && self.body.dyn_coerce.contains(&dest.local);
                self.relate(ot, &ov, dt, &dv, Variance::Co);
                self.guard_coerce = false;
                self.dyn_coerce = false;
            }
            // A fn item coerced to a fn pointer (W-BORROW3, `fnptr`).
            Rvalue::FnValue(f, ty) if matches!(self.body.tys.kind(*ty), TyKind::FnPtr(_)) => {
                self.place(dest, &mut dv, &mut d);
                self.fn_item_to_ptr(*f, *ty, &dv);
            }
            Rvalue::Ref(_, place) | Rvalue::SliceOf(place) | Rvalue::Subslice { base: place, .. } => {
                let mut li = self.loan_at[self.stmt_base[bi] + si];
                // A reference to a slice pattern's subslice temporary holds
                // the subslice's loan of the base place (borrowck/mod.rs
                // `collect_loans` makes no loan of the temporary).
                if li == u32::MAX
                    && matches!(rv, Rvalue::Ref(..))
                    && place.proj.is_empty()
                    && self.body.pat_subslice.contains(&place.local)
                {
                    li = self.subslice_loan(place.local);
                }
                if li == u32::MAX {
                    return;
                }
                let lv = self.loan_var[li as usize];
                let mutable = match rv {
                    Rvalue::Ref(m, _) => *m,
                    Rvalue::Subslice { mutable, .. } => *mutable,
                    _ => matches!(self.body.tys.kind(self.body.locals[dest.local as usize].ty), TyKind::Ref(_, Mut::Mut, _)),
                };
                let (mut pv, mut derefs) = (Vec::new(), Vec::new());
                let pt = self.place(place, &mut pv, &mut derefs);
                // Reborrow constraints (rustc `add_reborrow_constraint`): each
                // dereferenced reference outlives the new loan, from the last
                // deref back, stopping after the first shared one.
                for &(r, is_mut) in derefs.iter().rev() {
                    self.edge(r, lv);
                    if !is_mut {
                        break;
                    }
                }
                // The new reference is well formed: every region in the
                // borrowed value outlives it (`&'l T` needs `T: 'l`).
                for &v in &pv {
                    self.edge(v, lv);
                }
                let dt = self.place(dest, &mut dv, &mut d);
                let Some(&d0) = dv.first() else { return };
                self.edge(lv, d0);
                if let TyKind::Ref(_, _, dinner) = self.body.tys.kind(dt) {
                    let inner_v = if mutable { Variance::Inv } else { Variance::Co };
                    self.relate(pt, &pv, dinner, &dv[1..], inner_v);
                } else {
                    self.equate_all(&pv, &dv);
                }
            }
            Rvalue::Aggregate(_, variant, ops) => {
                for (i, o) in ops.iter().enumerate() {
                    self.into_place(o, dest, &[Proj::Downcast(*variant), Proj::Field(i as u32)]);
                }
                let dt = self.place(dest, &mut dv, &mut d);
                self.replay_adt(dt, &dv);
            }
            Rvalue::Opt(_, Some(o)) => self.into_place(o, dest, &[Proj::Downcast(1), Proj::Field(0)]),
            Rvalue::Res(_, ok, o) => self.into_place(o, dest, &[Proj::Downcast(if *ok { 0 } else { 1 }), Proj::Field(0)]),
            Rvalue::TupleAgg(ty, ops) => {
                // A `ByNext` wrapper (W-STD-B) is no program Adt, so its
                // one field (the wrapped iterator, also a `&mut I` over
                // core's `impl Iterator for &mut I`: the loan region
                // covariant, `I` invariant) flows into its inner part as
                // a value of its own type, and its item type, which is not
                // a field, is tied through the iterator's `next`: else the
                // wrapped iterator's regions outlive the item's.
                if let Some((crate::ty::iter::IterKind::ByNext, a)) = crate::ty::iter::iter_parts(&self.body.tys, *ty)
                    && let [o] = &ops[..]
                {
                    self.place(dest, &mut dv, &mut d);
                    let own = adt_regions(self.p, &self.body.tys, *ty) as usize;
                    let n0 = self.sc.slots(a[0]) as usize;
                    let n1 = self.sc.slots(a[1]) as usize;
                    if let (Some(src), Some(item)) = (dv.get(own..own + n0), dv.get(own + n0..own + n0 + n1)) {
                        let (src, item) = (src.to_vec(), item.to_vec());
                        let mut ov = Vec::new();
                        let ot = self.operand(o, &mut ov);
                        if !ov.is_empty() {
                            self.relate(ot, &ov, a[0], &src, Variance::Co);
                        }
                        if !self.by_next_item(a[0], &src, a[1], &item) {
                            self.flow_all(&src, &item);
                        }
                    } else {
                        self.into_place(o, dest, &[Proj::Field(0)]);
                    }
                } else {
                    for (i, o) in ops.iter().enumerate() {
                        self.into_place(o, dest, &[Proj::Field(i as u32)]);
                    }
                }
                if let TyKind::Closure(def, args) = self.body.tys.kind(*ty) {
                    // The closure contract (`closure_roles`): its body may
                    // make any captured source outlive any captured sink.
                    // The creator adds what the body needs of it when the
                    // body solves (`closure_reqs`), else all of it.
                    self.place(dest, &mut dv, &mut d);
                    let mut roles = Vec::new();
                    closure_roles(&mut self.sc, def, args, &mut roles);
                    self.closure_created(def, &roles, &dv, true);
                }
            }
            Rvalue::ArrayAgg(_, ops) | Rvalue::VecLit(_, ops) => {
                for o in ops {
                    self.into_place(o, dest, &[Proj::Index(0)]);
                }
            }
            Rvalue::ArrayRepeat(_, o, _) | Rvalue::VecRepeat(_, o, _) => self.into_place(o, dest, &[Proj::Index(0)]),
            Rvalue::MakeDyn { ptr: o, .. } | Rvalue::DynUpcast { ptr: o, .. } => {
                // A dyn pointer from a thin one (or a narrower dyn). The
                // pointer's own region carries over (`&'p S` to `&'q dyn
                // Tr`: `'p: 'q`), and every region of the data outlives the
                // object lifetime (`S: 'o`, rustc's unsizing; an upcast
                // gives `'o1: 'o2`). An owning pointer (`Box<dyn Tr + 'o>`)
                // has only the object's slots: its object lifetime, then its
                // trait args' (R11), which the source's impl must fit
                // (`dyn_fn_coercion`).
                let mut ov = Vec::new();
                let ot = self.operand(o, &mut ov);
                let dt = self.place(dest, &mut dv, &mut d);
                let refs = (matches!(self.body.tys.kind(ot), TyKind::Ref(..)), matches!(self.body.tys.kind(dt), TyKind::Ref(..)));
                let n_obj = self.dyn_in(dt).map_or(1, |(t, _)| self.sc.slots(t) as usize);
                if let Rvalue::DynUpcast { .. } = rv
                    && (n_obj > 1 || self.dyn_in(ot).is_some_and(|(t, _)| self.sc.slots(t) > 1))
                {
                    self.dyn_upcast(ot, &ov, dt, &dv, refs);
                    return;
                }
                let (data, obj): (Vec<u32>, Option<u32>) = match refs {
                    (true, true) => {
                        if let (Some(&x), Some(&y)) = (ov.first(), dv.first()) {
                            self.edge(x, y);
                        }
                        (ov.iter().skip(1).copied().collect(), dv.get(1).copied())
                    }
                    (false, false) => (ov.clone(), dv.first().copied()),
                    // A reference to a raw dyn pointer (tf-fatptr): the raw
                    // pointer holds no loan, so only the data's regions reach
                    // the object lifetime.
                    (true, false) if matches!(self.body.tys.kind(dt), TyKind::RawPtr(..)) => (ov.iter().skip(1).copied().collect(), dv.first().copied()),
                    _ => (Vec::new(), None),
                };
                let fits = dv.len() == usize::from(refs.1) + n_obj;
                match obj {
                    Some(o) if fits => {
                        for &x in &data {
                            self.edge(x, o);
                        }
                    }
                    _ => self.equate_all(&ov, &dv),
                }
                if let (Rvalue::MakeDyn { src, .. }, Some(o)) = (rv, obj) {
                    // A type param's universal outlives the object lifetime.
                    let mut ps = Vec::new();
                    params_in(&self.body.tys, *src, &mut ps);
                    for j in ps {
                        if let Some(&(_, u)) = self.own.param_univ.iter().find(|(k, _)| *k == j) {
                            self.edge(u, o);
                        }
                    }
                }
                if let Rvalue::MakeDyn { src, dyn_ty, .. } = rv {
                    // A `'static` object lifetime (`Box<dyn Tr>` in a
                    // signature or field, `+ 'static`, a `'static` trait)
                    // may not be a slot of the place the object goes to:
                    // the data outlives `'static` here.
                    if crate::check::object::dyn_is_static(self.p, &self.body.tys, *dyn_ty) {
                        for &x in &data {
                            self.edge(x, 0);
                        }
                    }
                    let args: Vec<u32> = if fits { dv[usize::from(refs.1) + 1..].to_vec() } else { Vec::new() };
                    if obj.is_some() {
                        self.replay_dyn(*src, &data, *dyn_ty, &args);
                    }
                    if !fits && n_obj > 1 {
                        self.dyn_args_cut();
                    } else {
                        self.dyn_fn_coercion(*src, *dyn_ty, &data, &args);
                    }
                }
            }
            // A `format_args!` value (R9): an `Arguments<'a>` holds a
            // borrow of its arguments temporary, which holds the
            // argument references; all their regions flow into the
            // value's one region slot. A literal-only value relates
            // nothing (it is `'static`).
            Rvalue::FormatArgs(Some(env), _) => {
                self.place(dest, &mut dv, &mut d);
                let mut ov = Vec::new();
                self.operand(env, &mut ov);
                self.flow_all(&ov, &dv);
            }
            // A downcast (W-CHECK-G3): `&'p dyn Any` to `&'q T` needs
            // `'p: 'q`. T is `'static`; an owning pointer relates nothing.
            Rvalue::DynData { ptr: o, .. } => {
                let mut ov = Vec::new();
                self.operand(o, &mut ov);
                self.place(dest, &mut dv, &mut d);
                if let (Some(&x), Some(&y)) = (ov.first(), dv.first()) {
                    self.edge(x, y);
                }
            }
            _ => {}
        }
    }

    /// The dyn type behind any references and smart pointers of `t`, and
    /// the index of its first slot among `t`'s slots.
    fn dyn_in(&mut self, t: Ty) -> Option<(Ty, usize)> {
        let mut t = t;
        let mut at = 0usize;
        loop {
            match self.body.tys.kind(t) {
                TyKind::Dyn(..) => return Some((t, at)),
                TyKind::Ref(r, _, inner) => {
                    at += usize::from(!bound(r));
                    t = inner;
                }
                _ => {
                    let inner = self.body.tys.smart_elem(t)?;
                    at += adt_regions(self.p, &self.body.tys, t) as usize;
                    t = inner;
                }
            }
        }
    }

    /// The slot vars of the trait args of the dyn type behind `t` (vars
    /// `tv`), after its object lifetime (R11). None when they do not fit.
    fn dyn_arg_vars(&mut self, t: Ty, tv: &[u32]) -> Option<Vec<u32>> {
        let (d, at) = self.dyn_in(t)?;
        let TyKind::Dyn(_, r) = self.body.tys.kind(d) else { return None };
        let n = self.sc.slots(d) as usize;
        tv.get(at + usize::from(!bound(r))..at + n).map(|s| s.to_vec())
    }

    /// The inputs and output of a `dyn Fn*(I..) -> O` type, behind any
    /// references and smart pointers, in this body's types. None for any
    /// other type. Their regions are the object's own (`DYN_LATE`),
    /// `'static`, or free: the object's slots (`dyn_positions`).
    fn dyn_fn_sig(&self, t: Ty) -> Option<(Vec<Ty>, Ty)> {
        let tys = &self.body.tys;
        let mut t = t;
        loop {
            match tys.kind(t) {
                TyKind::Ref(_, _, inner) => t = inner,
                _ => match tys.smart_elem(t) {
                    Some(inner) => t = inner,
                    None => break,
                },
            }
        }
        let lang = self.p.gx.lang;
        let pr = crate::check::object::principal_of(tys, t)?;
        if !lang.is_fn_family(pr.def) {
            return None;
        }
        let tuple = tys.args(pr.args).get(1).and_then(|g| g.as_ty())?;
        let ins = match tys.kind(tuple) {
            TyKind::Tuple(ts) => tys.tys_of(ts).to_vec(),
            TyKind::Unit => Vec::new(),
            _ => return None,
        };
        let out_def = lang.output_of(lang.fn_once)?;
        let out = tys.bindings(pr.bindings).iter().find(|(d, _)| *d == out_def).and_then(|(_, g)| g.as_ty()).unwrap_or(UNIT);
        Some((ins, out))
    }

    /// The region of each region place of a type inside `dyn Fn*` sugar,
    /// in the slot order of the type a value there has (its own late-bound
    /// places included, as `DYN_LATE`; a nested object's are its own).
    fn sugar_regions(&mut self, t: Ty, out: &mut Vec<Region>) {
        match self.body.tys.kind(t) {
            TyKind::Ref(r, _, inner) => {
                out.push(r);
                self.sugar_regions(inner, out);
            }
            TyKind::Dyn(_, r) => {
                out.push(if crate::check::object::dyn_is_static(self.p, &self.body.tys, t) { Region::Static } else { r });
                for e in dyn_arg_tys(&self.body.tys, t) {
                    self.sc.slot_regions(e, out);
                }
            }
            TyKind::Adt(_, args) => {
                let lts: Vec<Region> = self.body.tys.args(args).iter().filter_map(|g| if let GenericArg::Lifetime(r) = g { Some(*r) } else { None }).collect();
                if lts.is_empty() {
                    for _ in 0..adt_regions(self.p, &self.body.tys, t) {
                        out.push(Region::Erased);
                    }
                } else {
                    out.extend(lts);
                }
                for g in self.body.tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.sugar_regions(e, out);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in self.body.tys.tys_of(ts).to_vec() {
                    self.sugar_regions(e, out);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.sugar_regions(e, out),
            _ => self.sc.slot_regions(t, out),
        }
    }

    /// The places of a `dyn Fn*(I..) -> O` signature (R11), inputs then
    /// output, in slot order: the object's own late-bound regions, and
    /// the rest, which take the object's trait-arg slot vars `args` in
    /// order (`'static` ones var 0). None when `args` does not fit.
    fn dyn_positions(&mut self, ins: &[Ty], out: Ty, args: &[u32]) -> Option<(Vec<Pos>, Vec<Pos>)> {
        let mut next = args.iter().copied();
        let mut statics: Vec<u32> = Vec::new();
        let mut place = |r: Region, next: &mut dyn Iterator<Item = u32>| -> Option<Pos> {
            if bound(r) {
                return Some(Pos::Late);
            }
            let v = next.next()?;
            if r == Region::Static {
                statics.push(v);
                return Some(Pos::Var(0));
            }
            Some(Pos::Var(v))
        };
        let mut pin = Vec::new();
        for &it in ins {
            let mut rs = Vec::new();
            self.sugar_regions(it, &mut rs);
            for r in rs {
                pin.push(place(r, &mut next)?);
            }
        }
        let mut rs = Vec::new();
        self.sugar_regions(out, &mut rs);
        let mut pout = Vec::new();
        for r in rs {
            pout.push(place(r, &mut next)?);
        }
        if next.next().is_some() {
            return None;
        }
        // A written `'static` place is a slot that is `'static`.
        for v in statics {
            self.edge(v, 0);
        }
        Some((pin, pout))
    }

    /// A call through a `dyn Fn*` value (the receiver first): each
    /// late-bound input place is a fresh region of this call that the
    /// argument outlives, each other one the object's slot (R11); a
    /// late-bound output place is the one late-bound input's. The
    /// receiver lends nothing else to the result: whatever is behind the
    /// object takes any region in its late-bound places
    /// (`dyn_fn_coercion`).
    fn call_dyn_fn(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let Some((rt, rv)) = avs.first() else { return false };
        let Some((ins, out)) = self.dyn_fn_sig(*rt) else { return false };
        let Some(args) = self.dyn_arg_vars(*rt, rv) else { return false };
        let Some((pin, pout)) = self.dyn_positions(&ins, out, &args) else { return false };
        let avs = &avs[1..];
        if ins.len() != avs.len() {
            return false;
        }
        let mut late: Vec<u32> = Vec::new();
        let mut k = 0usize;
        for (i, &it) in ins.iter().enumerate() {
            let (at, av) = &avs[i];
            let mut rs = Vec::new();
            self.sugar_regions(it, &mut rs);
            let mut pv: Vec<u32> = Vec::with_capacity(rs.len());
            for &p in &pin[k..k + rs.len()] {
                pv.push(match p {
                    Pos::Late => {
                        let v = self.fresh();
                        late.push(v);
                        v
                    }
                    Pos::Var(v) => v,
                });
            }
            k += rs.len();
            if !av.is_empty() && !self.relate(*at, av, *at, &pv, Variance::Co) {
                return false;
            }
        }
        if dv.is_empty() {
            return true;
        }
        let one = if let [one] = late[..] { Some(one) } else { None };
        let rv = pout
            .iter()
            .map(|&p| match p {
                Pos::Late => one,
                Pos::Var(v) => Some(v),
            })
            .collect::<Option<Vec<u32>>>();
        let Some(rv) = rv else { return false };
        self.relate(dt, &rv, dt, dv, Variance::Co)
    }

    /// The region of each slot of a type inside a fn pointer type:
    /// `'static` where written there (`Scope::static_refs`), else elided
    /// (`Erased`), so late-bound.
    fn sig_slot_regions(&mut self, t: Ty) -> Vec<Region> {
        let mut rs = Vec::new();
        regioned_slots(&mut self.sc, t, t, &mut rs);
        rs
    }

    /// A call of a fn pointer signature whose regions are all elided, so
    /// late-bound, or written `'static` (check rejects other written
    /// lifetimes there, L0203): each elided input slot is a fresh region
    /// of this call that the argument outlives, a `'static` one is
    /// `'static`, and each elided output slot is the one input slot's
    /// (elision; L0202 otherwise). Slots in `free` (`.0`, W-BORROW3) are
    /// the pointer's free region, var `.1`, in the inputs and the output.
    /// False when the shapes do not pair or the output is not the one
    /// input's (the caller's rule then).
    fn call_late_bound_free(&mut self, ins: &[Ty], out: Ty, free: Option<(u32, u32)>, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        if ins.len() != avs.len() {
            return false;
        }
        let mut j = 0u32;
        let is_free = |j: &mut u32| {
            let f = free.filter(|&(m, _)| m >> *j & 1 == 1).map(|(_, v)| v);
            *j += 1;
            f
        };
        let mut slots: Vec<u32> = Vec::new();
        for (i, &it) in ins.iter().enumerate() {
            let (at, av) = &avs[i];
            let mut pv: Vec<u32> = Vec::new();
            for r in self.sig_slot_regions(it) {
                pv.push(match is_free(&mut j) {
                    Some(v) => v,
                    None if r == Region::Static => 0,
                    None => self.fresh(),
                });
            }
            if !av.is_empty() && !self.relate(*at, av, it, &pv, Variance::Co) {
                return false;
            }
            slots.extend(pv);
        }
        if dv.is_empty() {
            return true;
        }
        let outs = self.sig_slot_regions(out);
        // Elision's one input lifetime: a `'static` slot is no elided one
        // (it comes from a substituted type: `fn(&(K, V)) -> &K` at `K =
        // &'static str`; check rejects a written one next to an elided output).
        let late: Vec<u32> = slots.iter().copied().filter(|&v| v != 0).collect();
        let one = if let [one] = late[..] { Some(one) } else { None };
        let rv = outs
            .iter()
            .map(|&r| match is_free(&mut j) {
                Some(v) => Some(v),
                None if r == Region::Static => Some(0),
                None => one,
            })
            .collect::<Option<Vec<u32>>>();
        let Some(rv) = rv else { return false };
        self.relate(out, &rv, dt, dv, Variance::Co)
    }

    /// An upcast between dyn types whose trait args hold slots (R11): the
    /// pointer's region carries over, and within one principal trait the
    /// two objects pair like any two dyn types (object lifetime
    /// covariant, trait args invariant); to another trait it is a cut.
    fn dyn_upcast(&mut self, ot: Ty, ov: &[u32], dt: Ty, dv: &[u32], refs: (bool, bool)) {
        let (Some((sd, sa)), Some((dd, da))) = (self.dyn_in(ot), self.dyn_in(dt)) else { return self.dyn_args_cut() };
        let same = crate::check::object::principal_of(&self.body.tys, sd).map(|p| p.def) == crate::check::object::principal_of(&self.body.tys, dd).map(|p| p.def);
        if !same || refs.0 != refs.1 {
            return self.dyn_args_cut();
        }
        if refs.0
            && let (Some(&x), Some(&y)) = (ov.first(), dv.first())
        {
            self.edge(x, y);
        }
        let (Some(sv), Some(tv)) = (ov.get(sa..), dv.get(da..)) else { return self.dyn_args_cut() };
        let (mut i, mut j) = (0usize, 0usize);
        if !self.walk(sd, sv, &mut i, dd, tv, &mut j, Variance::Co) || i != sv.len() || j != tv.len() {
            self.equate_all(ov, dv);
        }
    }

    /// L0203: an unsizing or upcast to a dyn type of a user trait whose
    /// trait args hold regions (`dyn Tr<&'a T>`, R11): which regions the
    /// impl puts there is not followed yet.
    fn dyn_args_cut(&mut self) {
        // A mono instance: its template's check covers every instance
        // (there the trait args are type params, with no slots).
        if self.p.gx.instances.contains_key(&self.body.fn_id) {
            return;
        }
        self.errs.push(Diag::new(
            "L0203",
            self.span,
            "a coercion to a `dyn` type whose trait arguments hold lifetimes is not supported yet for user traits",
            "Use owned trait arguments, or a generic `T: Tr<..>` parameter.",
        ));
    }

    /// A coercion to `dyn Fn*(I..) -> O` (`args`: the target's trait-arg
    /// slot vars, R11). Each late-bound input place takes any region, as
    /// rustc proves `for<'r> Fn(&'r I) -> &'r O` of the source; each other
    /// place is the target's slot. A closure with a free argument slot (a
    /// `let` closure, a named annotation) fits only a place of the
    /// target's own (L0735 at a late-bound one), and what it returns from
    /// its captures (`data`, the env's slots) or free arguments must
    /// outlive the output place (`'static` for a late-bound one); a type
    /// param or a fn item is checked by its signature (`entail_dyn`).
    fn dyn_fn_coercion(&mut self, src: Ty, dyn_ty: Ty, data: &[u32], args: &[u32]) {
        let p = self.p;
        let Some((ins, out)) = self.dyn_fn_sig(dyn_ty) else {
            if !args.is_empty() {
                self.dyn_args_cut();
            }
            return;
        };
        let Some((pin, pout)) = self.dyn_positions(&ins, out, args) else { return self.dyn_args_cut() };
        match self.body.tys.kind(src) {
            TyKind::Closure(def, cargs) => {
                let Some(c) = p.gx.closures.get(&def) else { return };
                let vars = self.closure_args.get(&def).cloned().unwrap_or_default();
                if let Ok(cs) = closure_arg_slots(&mut self.sc, c) {
                    for (i, (r, link)) in cs.iter().enumerate() {
                        if r.is_none() {
                            continue;
                        }
                        let target = if cs.len() == pin.len() { pin.get(i).copied() } else { None };
                        let Some(Pos::Var(y)) = target else {
                            self.not_general_enough();
                            return;
                        };
                        match *link {
                            None => {
                                if let Some(&v) = vars.get(i) {
                                    self.edge(v, y);
                                    self.edge(y, v);
                                }
                            }
                            Some(_) if y == 0 => {}
                            Some(Region::Static) => self.edge(y, 0),
                            Some(Region::Param(k)) if !self.own.closure => {
                                self.edge(y, k + 1);
                                self.edge(k + 1, y);
                            }
                            Some(_) => {
                                self.not_general_enough();
                                return;
                            }
                        }
                    }
                }
                if pout.is_empty() {
                    return;
                }
                if c.free_sig && pout.contains(&Pos::Late) && self.sc.slots(c.output) > 0 {
                    self.free_output_not_general();
                    return;
                }
                // The closure took its signature from the unbound sugar,
                // where a fixed output place looks elided from the input:
                // with a late-bound input, a fixed (not `'static`) output
                // place is a cut.
                if pin.contains(&Pos::Late) && pout.iter().any(|p| matches!(p, Pos::Var(v) if *v != 0)) {
                    self.not_general_enough();
                    return;
                }
                let target = |k: usize| match pout.get(k) {
                    Some(Pos::Var(v)) => Some(*v),
                    Some(Pos::Late) => Some(0),
                    None => None,
                };
                let mut roles = Vec::new();
                closure_roles(&mut self.sc, def, cargs, &mut roles);
                let fe = self.fn_ends(def);
                match self.closure_reqs(def, &roles) {
                    Some(reqs) => {
                        for &(x, y) in reqs.iter() {
                            let End::Out(k) = y else { continue };
                            let Some(u) = target(k as usize) else { continue };
                            // An argument place returned: a late-bound one
                            // only into a late-bound output (elision), a
                            // fixed one outlives the output place.
                            if let End::Arg(j) = x {
                                match (pin.get(j as usize), pout.get(k as usize)) {
                                    (Some(Pos::Late), Some(Pos::Var(_))) => {
                                        self.not_general_enough();
                                        return;
                                    }
                                    (Some(&Pos::Var(a)), _) => self.edge(a, u),
                                    _ => {}
                                }
                            }
                            let from = match x {
                                End::Cap(i) => data.get(i as usize),
                                End::Arg(j) => vars.get(j as usize),
                                End::Fn(k) => fe.get(k as usize).and_then(|u| u.as_ref()),
                                End::Static | End::Out(_) => None,
                            };
                            if let Some(&v) = from {
                                self.edge(v, u);
                            }
                        }
                    }
                    None => {
                        // Unknown flows: a late-bound input may reach a fixed
                        // output place (not general enough), a fixed one any.
                        // A `'static` output is the closure's own return type
                        // (its body proves it).
                        if pin.contains(&Pos::Late) && pout.iter().any(|p| matches!(p, Pos::Var(v) if *v != 0)) {
                            self.not_general_enough();
                            return;
                        }
                        let us: Vec<u32> = (0..pout.len()).filter_map(target).collect();
                        let ins: Vec<u32> = pin.iter().filter_map(|p| if let Pos::Var(a) = *p { Some(a) } else { None }).collect();
                        for &a in &ins {
                            for &u in &us {
                                self.edge(a, u);
                            }
                        }
                        for (i, &(src, _)) in roles.iter().enumerate() {
                            if src && let Some(&v) = data.get(i) {
                                for &u in &us {
                                    self.edge(v, u);
                                }
                            }
                        }
                    }
                }
            }
            TyKind::Param(_) | TyKind::FnDef(..) => self.entail_dyn(src, &ins, &pin, &pout),
            // A fn pointer implements `Fn*` with its own signature: it must
            // match the target's once its binders are picked (W-BORROW3).
            TyKind::FnPtr(_) => {
                let free = if ptr_free(&self.body.tys, src).is_some() { data.first().copied() } else { None };
                let ok = match self.dyn_nodes(&pin, &pout) {
                    Some(dst) => self.ptr_matches(src, free, &dst),
                    None => false,
                };
                if !ok {
                    self.not_general_enough_param();
                }
            }
            _ => {}
        }
    }

    /// A callee's region signature: its own, its template's, or its trait
    /// method's (a stub, or a trait default body and its instances).
    fn callee(&self, f: LocalDefId) -> Callee<'p> {
        let p = self.p;
        if p.gx.closure_fns.contains_key(&f) {
            return Callee::Closure;
        }
        match p.regions.body_sig(p, f) {
            Some(s) => Callee::Sig(s),
            None => Callee::Opaque,
        }
    }

    /// The closure arguments of a call to `f` (not a call through a
    /// bound) whose param is a type param (`F`, `&F`, `&mut F`) with only
    /// `Fn*` bounds whose output has no type param: what the closure
    /// returns has the bound's regions (`tie_bound_output`), which the
    /// signature relates to the result, as rustc checks a call by its
    /// signature alone. Also those whose bound output holds type params
    /// the signature binds (`-> U`, `-> Option<U>`), when the closure's
    /// body solves: its returns reach `U`'s slots one by one
    /// (`flow_closure_output`).
    fn output_tied(&mut self, f: LocalDefId, avs: &[(Ty, Vec<u32>)]) -> Vec<usize> {
        let p = self.p;
        if p.gx.fn_class.get(f.0 as usize) == Some(&crate::check::generics::FnClass::Stub) {
            return Vec::new();
        }
        let Callee::Sig(sig) = self.callee(f) else { return Vec::new() };
        let mut out = Vec::new();
        for (i, (t, _)) in avs.iter().enumerate() {
            let mut t = *t;
            while let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
                t = inner;
            }
            if !matches!(self.body.tys.kind(t), TyKind::Closure(..)) {
                continue;
            }
            let Some(mut pt) = sig.params.get(i).copied() else { continue };
            while let TyKind::Ref(_, _, inner) = p.tys.kind(pt) {
                pt = inner;
            }
            let TyKind::Param(j) = p.tys.kind(pt) else { continue };
            let bounds: Vec<Option<Ty>> = sig.fn_bounds.iter().filter(|b| b.param == j.0).map(|b| b.output).collect();
            // The params of `sig`'s inputs and return: `flow_closure_output`
            // finds their slots bound at the call.
            let mut bound_ps = Vec::new();
            for &t in sig.params.iter().chain([&sig.ret]) {
                params_in(&p.tys, t, &mut bound_ps);
            }
            let mut param_out = false;
            let ok = !bounds.is_empty()
                && bounds.iter().all(|o| match o {
                    Some(o) if p.tys.flags(*o).contains_param() => {
                        let mut ps = Vec::new();
                        params_in(&p.tys, *o, &mut ps);
                        param_out = true;
                        ps.iter().all(|q| bound_ps.contains(q))
                    }
                    _ => true,
                });
            if ok && param_out {
                let TyKind::Closure(def, args) = self.body.tys.kind(t) else { continue };
                let mut roles = Vec::new();
                closure_roles(&mut self.sc, def, args, &mut roles);
                if self.closure_reqs(def, &roles).is_none() {
                    continue;
                }
            }
            if ok {
                out.push(i);
            }
        }
        out
    }

    /// The trait method behind a vtable call. Lowering upcasts the
    /// receiver to the method's own trait first, so the receiver's
    /// principal owns the slot.
    fn dyn_method(&self, recv: Ty, slot: u32) -> Option<DefId> {
        let TyKind::Ref(_, _, obj) = self.body.tys.kind(recv) else { return None };
        let owner = crate::check::object::principal_of(&self.body.tys, obj)?;
        let info = self.p.gx.dyn_infos.get(&owner.def)?;
        let j = slot.checked_sub(crate::check::object::VT_HEADER + info.supers.len() as u32)?;
        Some(info.methods.get(j as usize)?.def)
    }

    /// A call of a trait impl method also takes the trait method's
    /// signature: rustc checks every call against the trait item, and an
    /// impl may refine it (take `&str` where the trait takes `&'static
    /// str`, return `&'static str` or its own `'a` where the trait borrows
    /// `self`). The trait's signature is instantiated over the called fn's
    /// erased types, on top of the impl's own constraints, which the
    /// trait's imply (`impl_contract`). A std trait has no region
    /// signature; its methods elide, so a returned reference borrows
    /// `self`.
    fn trait_view(&mut self, f: LocalDefId, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) {
        let p = self.p;
        let Some(tmeth) = impl_trait_method(p, f) else { return };
        if let Some(tsig) = p.regions.trait_methods.get(&tmeth) {
            let info = p.fn_info(f);
            self.proj = Some(FxMap::default());
            let preds = p.gx.trait_methods.get(&tmeth).map_or(&[][..], |t| &t.generics.predicates[..]);
            let ok = self.call_sig_with(tsig, &info.params, info.ret, avs, dt, dv, preds);
            self.proj = None;
            if !ok {
                self.call_opaque(avs, dt, dv);
            }
        } else if let Some(lm) = p.gx.lang_method_sigs.get(&tmeth)
            && matches!(lm.self_kind, Some(crate::ast::SelfKind::Ref | crate::ast::SelfKind::RefMut))
            && matches!(p.tys.kind(lm.ret), TyKind::Ref(..))
            && let Some((rt, rv)) = avs.first()
            && matches!(self.body.tys.kind(*rt), TyKind::Ref(..))
            && matches!(self.body.tys.kind(dt), TyKind::Ref(..))
            && let (Some(&s), Some(&d)) = (rv.first(), dv.first())
        {
            self.edge(s, d);
        }
    }

    /// True when a call target's declared return type is `!`.
    fn diverges(&self, target: CallTarget) -> bool {
        match target {
            CallTarget::Fn(f) => self.p.fn_info(f).ret == NEVER,
            CallTarget::Indirect(l) => match self.body.tys.kind(self.body.locals[l as usize].ty) {
                TyKind::FnPtr(sig) => self.body.tys.sig(sig).value.output == NEVER,
                _ => false,
            },
            _ => false,
        }
    }

    fn call(&mut self, target: CallTarget, args: &[Operand], dest: &Place) {
        let mut avs: Vec<(Ty, Vec<u32>)> = Vec::with_capacity(args.len());
        for o in args {
            let mut v = Vec::new();
            let t = self.operand(o, &mut v);
            avs.push((t, v));
        }
        let (mut dv, mut d) = (Vec::new(), Vec::new());
        let mut dt = self.place(dest, &mut dv, &mut d);
        // A callee that returns `!` never writes `dest`: nothing flows there.
        if self.diverges(target) {
            dv.clear();
            dt = NEVER;
        }
        // A call of an `impl Trait` fn: its value captures every argument
        // region. Any call carries the captures of the opaque values it
        // takes by value to an opaque result (`cap_var`). A callee that
        // takes a `&mut` (or a shared borrow of a cell) may store what it
        // takes in a borrowed opaque local (`v.push(f(&c))`,
        // `cap_reach`), and so may a call whose result is written through
        // a deref.
        // A template callee (`lust check` makes no instances) keeps its
        // opaque return in `FnInfo::ret`.
        let all: Vec<u32> = match target {
            CallTarget::Fn(f) if self.returns_opaque(f) => self.captured_vars(f, &avs),
            _ => Vec::new(),
        };
        let caps = self.caps_of(args.iter());
        if !self.borrowed_caps.is_empty() {
            let mut reach = Vec::new();
            let tys = &self.body.tys;
            if avs.iter().any(|&(t, _)| has_mut_ref(tys, t) || has_interior(tys, t)) {
                reach.extend(&caps);
            }
            if dest.proj.contains(&Proj::Deref) {
                reach.extend(&caps);
                reach.extend(&all);
            }
            self.cap_reach(&reach);
        }
        if let Some(&dc) = self.cap_var.get(&dest.local) {
            self.flow_all(&all, &[dc]);
            self.flow_all(&caps, &[dc]);
        }
        // Free closure arguments first: a closure with no captures has no
        // creating statement, so its argument vars are made here. A builtin
        // links them to its other arguments; a generic fn through its bound
        // (`call_sig_with`), or like a builtin when its signature cannot
        // pair (below).
        for (t, v) in &avs {
            if let TyKind::Closure(def, args) = self.body.tys.kind(*t) {
                let mut roles = Vec::new();
                closure_roles(&mut self.sc, def, args, &mut roles);
                self.closure_arg_vars(def, &roles, v);
            }
        }
        if let CallTarget::Builtin(b) = target {
            self.link_closure_args(&avs, Some(b), &[]);
        }
        // A closure argument that returns borrows: whatever the callee
        // returns may hold the closure's captured sources and free
        // argument regions (its output), unless the callee's bounds give
        // its output every region (`output_tied`; then the signature
        // says what reaches the result).
        // `Box::new(x)` and `Rc::new(x)` hold `x` itself: its slots are
        // the result's, one to one (a closure's captures included). So do
        // `RefCell::new(x)` and `Cell::new(x)` (the cell's `T` is chosen at
        // the call: `x` flows into it).
        let cell_inner = match target {
            CallTarget::Builtin(crate::check::Builtin::BoxNew | crate::check::Builtin::RcNew) => self.body.tys.smart_elem(dt),
            CallTarget::Builtin(crate::check::Builtin::RefCellNew) => self.body.tys.refcell_elem(dt),
            CallTarget::Builtin(crate::check::Builtin::CellNew) => self.body.tys.cell_elem(dt),
            _ => None,
        };
        if let Some(inner) = cell_inner
            && let [(at, av)] = &avs[..]
            && (av.is_empty() && dv.is_empty() || self.relate(*at, av, inner, &dv, Variance::Co))
        {
            return;
        }
        // `Rc::as_ptr(&rc)`, `Arc::as_ptr(&arc)` and `Box::as_ptr(&b)` give `*const T`: a raw
        // pointer holds no loan of the reference, so only the element's
        // slots (a `dyn Tr`'s object lifetime) reach the result (tf-front).
        if let CallTarget::Builtin(
            crate::check::Builtin::SmartAsPtr | crate::check::Builtin::BoxAsPtr | crate::check::Builtin::Sync(crate::check::sync::SyncOp::ArcAsPtr),
        ) = target
            && let [(at, av)] = &avs[..]
            && let TyKind::Ref(_, _, owner) = self.body.tys.kind(*at)
            && let Some(elem) = self.body.tys.adt_first_ty_arg(owner)
            && let TyKind::RawPtr(_, pointee) = self.body.tys.kind(dt)
        {
            let n = self.sc.slots(elem) as usize;
            if av.len() >= n && dv.len() == n {
                let inner = av[av.len() - n..].to_vec();
                if n == 0 || self.relate(elem, &inner, pointee, &dv, Variance::Co) {
                    return;
                }
            }
        }
        let tied = match target {
            CallTarget::Fn(f) => self.output_tied(f, &avs),
            _ => Vec::new(),
        };
        let mut srcs: Vec<u32> = Vec::new();
        for (i, (t, v)) in avs.iter().enumerate() {
            if !tied.contains(&i) {
                self.closure_sources(*t, v, &mut 0, &mut srcs);
            }
        }
        self.flow_all(&srcs, &dv);
        // `catch_unwind(f)` returns what `f` returns, or a `'static`
        // payload, and `b.then(f)` what `f` returns, or None: the
        // closure's borrows reach the result only through its output
        // (W-UNWIND; ts-rust compilerhost.rs `then(|| .. as Rc<dyn Fn()>)`).
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::CatchUnwind) | crate::check::Builtin::BoolThen) = target {
            return;
        }
        if matches!(target, CallTarget::Dyn(_)) && self.call_dyn_fn(&avs, dt, &dv) {
            return;
        }
        if let CallTarget::Indirect(l) = target
            && let TyKind::FnPtr(sig) = self.body.tys.kind(self.body.locals[l as usize].ty)
        {
            let s = self.body.tys.sig(sig).value;
            let ins: Vec<Ty> = self.body.tys.tys_of(s.inputs).to_vec();
            let mut lv = Vec::new();
            self.local_vars(l, &mut lv);
            let free = if s.free_slots != 0 { lv.first().map(|&v| (s.free_slots, v)) } else { None };
            if (s.free_slots == 0 || free.is_some()) && self.call_late_bound_free(&ins, s.output, free, &avs, dt, &dv) {
                return;
            }
        }
        // `scope.spawn(f)` on `&Scope<'s, _>`: `F: 's` and `T: 's`, and the
        // handle's own region is `'s` (W-THREADS). The scope closure's
        // `&Scope` argument is higher-ranked, so `'s` covers its whole
        // body: two spawned closures borrowing one place both hold it
        // to the end, as rustc's `'scope`.
        // `'s` is the `Scope`'s own `'scope` slot (behind the receiver's
        // reborrow, whose region may be shorter).
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::ScopeSpawn)) = target
            && let Some(&r) = avs.first().and_then(|(_, v)| v.get(1))
        {
            for &x in avs.iter().skip(1).flat_map(|(_, v)| v).chain(&srcs).chain(dv.iter().skip(1)) {
                self.edge(x, r);
            }
            if let Some(&h) = dv.first() {
                self.edge(h, r);
                self.edge(r, h);
            }
            // `spawn(&'scope self)`: the receiver's borrow outlives
            // `'scope` (rustc E0521-style "lifetime may not live long
            // enough" for `fn f(s: &Scope)` with two elided lifetimes).
            if let Some(&b) = avs.first().and_then(|(_, v)| v.first()) {
                self.edge(b, r);
            }
            return;
        }
        // `builder.spawn_scoped(scope, f)`: the `scope.spawn` rule with the
        // `&Scope` as the second argument; the `io::Result`'s `Ok` handle
        // has the `'s` slot first (its `Err` holds no borrows).
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::BuilderSpawnScoped)) = target
            && let Some(&r) = avs.get(1).and_then(|(_, v)| v.get(1))
        {
            for &x in avs.iter().skip(2).flat_map(|(_, v)| v).chain(&srcs).chain(dv.iter().skip(1)) {
                self.edge(x, r);
            }
            if let Some(&h) = dv.first() {
                self.edge(h, r);
                self.edge(r, h);
            }
            if let Some(&b) = avs.get(1).and_then(|(_, v)| v.first()) {
                self.edge(b, r);
            }
            return;
        }
        // `mpsc::channel()`: both ends carry one `T` (W-THREADS).
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::Channel | crate::check::sync::SyncOp::SyncChannel)) = target {
            let n = dv.len() / 2;
            for i in 0..n {
                self.edge(dv[i], dv[n + i]);
                self.edge(dv[n + i], dv[i]);
            }
            return;
        }
        // `send(&self, t: T)`: the value flows into the channel's `T`; a
        // failed send's `SendError<T>` gives that `T` back.
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::ChanSend | crate::check::sync::SyncOp::OnceSet)) = target
            && let [(st, sv), (vt, vv)] = avs.as_slice()
            && let TyKind::Ref(_, _, s) = self.body.tys.kind(*st)
            && let Some(el) = self.body.tys.adt_first_ty_arg(s)
            && let Some(tv) = sv.get(1..)
        {
            let tv = tv.to_vec();
            if !self.relate(*vt, vv, el, &tv, Variance::Co) {
                self.flow_all(vv, &tv);
            }
            self.equate_all(&tv, &dv);
            return;
        }
        // `handle.join()`: the result's `Ok` is the thread's `T`; its `Err`
        // payload is `'static` and borrows nothing (W-UNWIND).
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::JoinHandleJoin)) = target
            && let Some((ht, hv)) = avs.first()
            && let Some(t) = self.body.tys.adt_first_ty_arg(*ht)
        {
            let k = self.sc.slots(t) as usize;
            if k <= hv.len() && k <= dv.len() {
                let hv = hv[hv.len() - k..].to_vec();
                self.equate_all(&hv, &dv[..k]);
            }
            return;
        }
        // `once.get_or_init(f)`: what `f` returns is the cell's `T`; the
        // result `&T` borrows the cell.
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::OnceGetOrInit)) = target
            && let Some((_, sv)) = avs.first()
            && let Some((&r, tv)) = sv.split_first()
            && dv.len() == sv.len()
        {
            let tv = tv.to_vec();
            self.flow_all(&srcs, &tv);
            self.edge(r, dv[0]);
            self.equate_all(&tv, &dv[1..]);
            return;
        }
        // `cv.wait(guard)` and `wait_while`: the guard comes back as is.
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::CondvarWait | crate::check::sync::SyncOp::CondvarWaitWhile | crate::check::sync::SyncOp::CondvarWaitTimeoutWhile)) = target
            && let Some((_, gv)) = avs.get(1)
            && dv.len() == 2 * gv.len()
        {
            let gv = gv.clone();
            self.equate_all(&gv, &dv[..gv.len()]);
            self.equate_all(&gv, &dv[gv.len()..]);
            return;
        }
        // `thread::spawn(f)` and `Builder::spawn(self, f)`: `F: 'static`
        // and `T: 'static` (W-THREADS). Every region of the closure (its
        // captured borrows) and of the handle must be `'static` (a
        // `Builder` holds no borrows).
        if let CallTarget::Builtin(crate::check::Builtin::Sync(
            crate::check::sync::SyncOp::ThreadSpawn | crate::check::sync::SyncOp::BuilderSpawn,
        )) = target
        {
            for &x in avs.iter().flat_map(|(_, v)| v).chain(&srcs).chain(&dv) {
                self.edge(x, 0);
            }
            return;
        }
        // A vtable call takes the trait method's signature, which every
        // impl satisfies (`impl_contract`). The object's hidden regions
        // stay alive through the pointer's region (`MakeDyn`), so a
        // `-> &'static str` method borrows nothing and a `&'static str`
        // argument must be `'static`.
        if let CallTarget::Dyn(slot) = target
            && let Some(def) = avs.first().and_then(|(rt, _)| self.dyn_method(*rt, slot))
            && let Some(sig) = self.p.regions.trait_methods.get(&def)
            && let Some(t) = self.p.gx.trait_methods.get(&def)
        {
            // The trait's type params are the object's trait args (R11):
            // their regions are the object's slots.
            self.seed_binds.clear();
            if let Some((rt, rv)) = avs.first()
                && let Some((d, _)) = self.dyn_in(*rt)
                && let Some(args) = self.dyn_arg_vars(*rt, rv)
            {
                let mut at = 0usize;
                for (j, e) in dyn_arg_tys(&self.body.tys, d).into_iter().enumerate() {
                    let n = self.sc.slots(e) as usize;
                    if let Some(vs) = args.get(at..at + n) {
                        self.seed_binds.push((j as u32 + 1, vs.to_vec(), e));
                    }
                    at += n;
                }
            }
            if !self.call_sig_with(sig, &t.params, t.ret, &avs, dt, &dv, &[]) {
                self.call_opaque(&avs, dt, &dv);
            }
            return;
        }
        if let CallTarget::Fn(f) = target
            && (self.call_fn_bound(f, &avs, dt, &dv) || self.call_param_item(f, &avs, dt, &dv))
        {
            return;
        }
        let callee = match target {
            CallTarget::Fn(f) => Some((f, self.callee(f))),
            _ => None,
        };
        match callee {
            Some((f, Callee::Sig(sig))) => {
                self.bound_linked.clear();
                self.seed_univ = self.trait_lifetime_seeds(f, &avs);
                let ok = self.call_sig(f, sig, &avs, dt, &dv);
                self.seed_univ.clear();
                // An `Item = T` bound (`I: Iterator<Item = T>`, `I:
                // IntoIterator<Item = T>`) ties `T`'s regions to the
                // iterator's, which the signature pairing does not see:
                // `mk(v.iter())` returning `Vec<T>` borrows `v` (rustc
                // E0505 on a later move; this was a false accept, also
                // behind `collect` into a BTreeSet). Over-approximate:
                // every argument region may reach the result, except a
                // slot the signature writes `'static` (it holds no borrow:
                // `-> Result<Vec<T>, &'static str>`).
                if ok && self.item_bound(f) && !std::mem::take(&mut self.item_bound_exact) {
                    let all: Vec<u32> = avs.iter().flat_map(|(_, v)| v.iter().copied()).collect();
                    let mut named: Vec<Region> = Vec::new();
                    let targets: Vec<u32> = if regioned_slots(&mut self.sc, sig.ret, dt, &mut named) && named.len() == dv.len() {
                        dv.iter().zip(&named).filter(|(_, r)| **r != Region::Static).map(|(&v, _)| v).collect()
                    } else {
                        dv.clone()
                    };
                    self.flow_all(&all, &targets);
                }
                if ok {
                    // Closures no bound paired: like the opaque rule.
                    let linked = std::mem::take(&mut self.bound_linked);
                    self.link_closure_args(&avs, None, &linked);
                } else {
                    if self.has_type_outlives(f) {
                        self.type_outlives_unproved();
                    }
                    let mut srcs: Vec<u32> = Vec::new();
                    for &i in &tied {
                        let (t, v) = &avs[i];
                        self.closure_sources(*t, v, &mut 0, &mut srcs);
                    }
                    self.flow_all(&srcs, &dv);
                    if self.returns_opaque(f) {
                        self.call_opaque_from(&avs, &all, dt, &dv);
                    } else {
                        self.call_opaque(&avs, dt, &dv);
                    }
                    self.link_closure_args(&avs, None, &[]);
                }
                self.trait_view(f, &avs, dt, &dv);
            }
            Some((_, Callee::Closure)) => {
                // The result holds what the body returns: per output slot,
                // the captured and free argument slots its requirements
                // name (`closure_reqs`), else every captured source (the
                // contract). Higher-ranked inputs reach only the output
                // slots its bound ties to them.
                if let Some((et, ev)) = avs.first() {
                    let (ct, skip) = match self.body.tys.kind(*et) {
                        TyKind::Ref(_, _, inner) => (inner, 1),
                        _ => (*et, 0),
                    };
                    if let TyKind::Closure(def, args) = self.body.tys.kind(ct) {
                        let mut roles = Vec::new();
                        closure_roles(&mut self.sc, def, args, &mut roles);
                        let caps: Vec<u32> = ev.iter().skip(skip).copied().collect();
                        let vars = self.closure_arg_vars(def, &roles, &caps);
                        let n_out = self.p.gx.closures.get(&def).map(|c| c.output).map(|t| self.sc.slots(t) as usize);
                        let fe = self.fn_ends(def);
                        match self.closure_reqs(def, &roles) {
                            Some(reqs) if n_out == Some(dv.len()) => {
                                for &(x, y) in reqs.iter() {
                                    let End::Out(k) = y else { continue };
                                    let from = match x {
                                        End::Cap(i) => caps.get(i as usize).copied(),
                                        End::Arg(j) => vars.as_ref().and_then(|v| v.get(j as usize)).copied(),
                                        End::Fn(k) => fe.get(k as usize).copied().flatten(),
                                        End::Static | End::Out(_) => None,
                                    };
                                    if let (Some(from), Some(&d)) = (from, dv.get(k as usize)) {
                                        self.edge(from, d);
                                    }
                                }
                            }
                            _ => {
                                for (i, &(src, _)) in roles.iter().enumerate() {
                                    if src && let Some(&x) = caps.get(i) {
                                        for &y in &dv {
                                            self.edge(x, y);
                                        }
                                    }
                                }
                            }
                        }
                        // A higher-ranked output slot of the closure's bound
                        // (`ClosureEntry::bound_output`, a returned `impl
                        // Fn(&u8) -> &u8`) holds what the call passes.
                        let bo = self.p.gx.closures.get(&def).and_then(|c| c.bound_output.map(|b| (b, c.output)));
                        if let Some((bo, out_t)) = bo {
                            let mut named: Vec<Region> = Vec::new();
                            let tied = regioned_slots(&mut self.sc, bo, out_t, &mut named) && named.len() == dv.len();
                            let from: Vec<u32> = avs.iter().skip(1).flat_map(|(_, v)| v.iter().copied()).collect();
                            for (k, &d) in dv.iter().enumerate() {
                                if !tied || matches!(named[k], Region::Bound(_)) {
                                    for &x in &from {
                                        self.edge(x, d);
                                    }
                                }
                            }
                        }
                        // Free argument slots (a named annotation): the
                        // call's arguments flow into them.
                        if let Some(vars) = vars
                            && let Some(inputs) = self.p.gx.closures.get(&def).map(|c| c.inputs.clone())
                        {
                            let mut at = 0usize;
                            for (k, it) in inputs.into_iter().enumerate() {
                                let n = self.sc.slots(it) as usize;
                                if let (Some((at_ty, av)), Some(pv)) = (avs.get(1 + k), vars.get(at..at + n)) {
                                    let pv = pv.to_vec();
                                    if !av.is_empty() {
                                        self.relate(*at_ty, av, it, &pv, Variance::Co);
                                    }
                                }
                                at += n;
                            }
                        }
                    }
                }
            }
            _ if matches!(target, CallTarget::Builtin(b) if fmt_builder_builtin(b)) => {
                // A Debug builder (W-STD-B) borrows only what its receiver
                // does: `debug_struct(&mut self, &str)` and `entry(&mut
                // self, &dyn Debug) -> &mut Self` format their other
                // arguments at once and never store them.
                if let Some((rt, rv)) = avs.first() {
                    let (rt, rv) = (*rt, rv.clone());
                    // `&mut Self` back: the receiver's own regions, slot
                    // by slot; a new builder: what the `&mut Formatter`
                    // borrow allows.
                    if !self.relate(rt, &rv, dt, &dv, Variance::Co) {
                        self.flow_all(&rv, &dv);
                    }
                }
            }
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::IterPeek)) && self.call_peek(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(b) if item_builtin(b) && self.call_item(b, &avs, dt, &dv)) => {}
            // `Type::from_iter(src)` whose items `call_item` cannot name
            // slot by slot (fx-fromiter): the conservative rule over the
            // whole source, its borrow region included, never the
            // receiver-stripping item rule below (the source is an
            // argument, not a `&mut` iterator receiver).
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::FromIter)) => {
                self.call_opaque(&avs, dt, &dv);
            }
            _ if matches!(target, CallTarget::Builtin(b) if item_builtin(b)) => {
                // Items the receiver cannot name slot by slot (a `map`
                // closure makes them): an item (or a collection of items)
                // borrows what the iterator's sources borrow, not the
                // temporary `&mut` of the iterator; a closure that returns
                // borrows adds its sources. W-STD-A, ty/iter.rs.
                // An item that holds `&mut` (`iter_mut`) is invariant in
                // what it points to: the element regions equal the
                // iterator's, and only the loan regions flow into the
                // item's top-level references (else a write through the
                // item could store a shorter borrow, rustc E0597).
                let mutable = has_mut_ref(&self.body.tys, dt);
                let (mut from, mut loans): (Vec<u32>, Vec<u32>) = (Vec::new(), Vec::new());
                for (t, v) in &avs {
                    let (inner, vars) = match self.body.tys.kind(*t) {
                        TyKind::Ref(_, _, inner) if !v.is_empty() => (inner, &v[1..]),
                        _ => (*t, &v[..]),
                    };
                    if mutable {
                        self.iter_slot_split(inner, vars, &mut 0, &mut loans, &mut from);
                    } else {
                        self.non_closure_slots(inner, vars, &mut 0, &mut from);
                    }
                }
                if mutable {
                    let (mut tops, mut rest) = (Vec::new(), Vec::new());
                    self.item_slot_split(dt, &dv, &mut 0, &mut tops, &mut rest);
                    loans.extend(from.iter().copied());
                    self.flow_all(&loans, &tops);
                    from.append(&mut rest);
                    self.equate_all(&from, &[]);
                } else {
                    // The item's parts that are parts of the iterator relate
                    // at their variance in the iterator's type (an invariant
                    // `T` stays equal; the `&mut` the call takes is only the
                    // borrow `next` needs); the sources reach the other slots.
                    // The sources (`from`, no closure captures) reach the
                    // other slots, at each slot's variance.
                    let mut filled = vec![false; dv.len()];
                    for (t, v) in &avs {
                        let f = match self.body.tys.kind(*t) {
                            TyKind::Ref(_, _, inner) if !v.is_empty() => self.store_parts(inner, &v[1..], dt, &dv, false),
                            _ => self.store_parts(*t, v, dt, &dv, false),
                        };
                        for (x, y) in filled.iter_mut().zip(f) {
                            *x |= y;
                        }
                    }
                    let rest: Vec<u32> = dv.iter().zip(&filled).filter(|(_, f)| !**f).map(|(&x, _)| x).collect();
                    self.flow_all(&from, &rest);
                    self.store_flat_in(&from, dt, &dv, &filled);
                }
                // An item that can write through shared memory (`&RefCell`)
                // is its source's own regions, both ways.
                if has_interior(&self.body.tys, dt) {
                    self.flow_all(&dv, &from);
                }
            }
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::Clone)) && self.call_clone(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::CloneFrom)) && self.call_clone_from(&avs) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::ConvDeref | crate::check::Builtin::ConvRcInner))
                && self.call_conv_deref(&avs, dt, &dv) => {}
            _ if let CallTarget::Builtin(b @ (crate::check::Builtin::MemReplace | crate::check::Builtin::MemSwap)) = target
                && self.call_mem(b == crate::check::Builtin::MemSwap, &avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::IterFold)) && self.call_fold(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::IterTryFold)) && self.call_try_fold(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(b) if own_region_builtin(b)) && self.call_own_region(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(b) if receiver_builtin(b)) && self.call_receiver(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::Clone))
                && let [(at, av)] = avs.as_slice()
                && let TyKind::Ref(_, _, inner) = self.body.tys.kind(*at)
                && inner == dt
                && !av.is_empty()
                && self.relate(inner, &av[1..], dt, &dv, Variance::Co) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::HashIterNew)) && self.call_hash_iter(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::IterOptRes)) && self.call_opt_res(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::SliceFromRef)) && self.call_from_ref(&avs, dt, &dv) => {}
            _ if let CallTarget::Builtin(b) = target
                && entry_builtin(b)
                && self.call_hash_entry(b, &avs, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::HashExtend)) && self.call_hash_extend(&avs) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::VecExtend)) && self.call_vec_extend(&avs) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::CowToMut)) && self.call_cow_to_mut(&avs, &dv) => {}
            // Cow addition copies the right side's bytes into an
            // Owned result (in place for `add_assign`): the right
            // side's regions reach neither the result nor the
            // receiver, as with `push_str`; the by-value form's
            // result keeps the left Cow's lifetime slot.
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::CowAddAssignStr)) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::CowAddStr))
                && avs.first().is_some_and(|(t0, v0)| !v0.is_empty() && self.relate(*t0, v0, dt, &dv, Variance::Co)) => {}
            // A sort's comparator or key fn runs during the call only:
            // its captures reach neither the slice nor the unit result,
            // and `link_closure_args` gave its args the elements.
            _ if matches!(target, CallTarget::Builtin(b) if sort_by_builtin(b)) => {}
            // `any(f)` and kin take `f` by value and run it during the call
            // only: its captures reach neither the iterator nor a result
            // with no regions (`link_closure_args` gave its args the items).
            _ if matches!(target, CallTarget::Builtin(b) if consume_closure_builtin(b)) && dv.is_empty() => {}
            // So does `retain`'s predicate, which takes `&T`: its captures
            // reach neither the Vec (or set) nor the unit result
            // (`retain_mut` and a map's `retain` hand out `&mut T` and
            // `&mut V`, and keep the conservative rule; so does an
            // element with a `Cell` inside, which `&T` can write).
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::VecRetain | crate::check::Builtin::SetRetain))
                && avs.first().is_some_and(|(t0, _)| plain_shared(self.p, &self.body.tys, *t0)) => {}
            // A map or set lookup (W-STD-B) reads its `&Q` key during the
            // call only: the opaque rule over the receiver alone.
            _ if let CallTarget::Builtin(
                b @ (crate::check::Builtin::MapInsert | crate::check::Builtin::MapRemove | crate::check::Builtin::MapRemoveEntry),
            ) = target
                && self.call_map_value(b, &avs, dt, &dv) => {}
            _ if let CallTarget::Builtin(crate::check::Builtin::MapGet | crate::check::Builtin::MapGetMut) = target
                && self.call_map_get(&avs, dt, &dv) => {}
            _ if let CallTarget::Builtin(crate::check::Builtin::SetGet) = target
                && self.call_set_get(&avs, dt, &dv) => {}
            _ if let CallTarget::Builtin(crate::check::Builtin::MapGetKeyValue) = target
                && self.call_map_key_value(&avs, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(b) if hash_lookup_builtin(b)) && !avs.is_empty() => {
                self.call_opaque(&avs[..1], dt, &dv)
            }
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::IterFlatMap)) && self.call_flat_map(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(_)) && matches!(self.body.tys.builtin_of(dt), Some(BuiltinTy::Iter(_))) => {
                self.call_adapter(&avs, dt, &dv);
            }
            // `Rc::downgrade(&Rc<T>) -> Weak<T>` and `Weak::upgrade(&Weak<T>)
            // -> Option<Rc<T>>` share `T`; the borrow of the argument is
            // not part of the result (rustc's signatures).
            _ if let CallTarget::Builtin(
                crate::check::Builtin::RcDowngrade
                | crate::check::Builtin::WeakUpgrade
                | crate::check::Builtin::Sync(crate::check::sync::SyncOp::ArcDowngrade | crate::check::sync::SyncOp::ArcWeakUpgrade),
            ) = target
                && let [(at, av)] = avs.as_slice()
                && let TyKind::Ref(_, _, inner) = self.body.tys.kind(*at)
                && let Some(el) = self.body.tys.rc_elem(inner).or_else(|| self.body.tys.weak_elem(inner)).or_else(|| self.body.tys.arc_weak_elem(inner))
                && let Some(rl) = self
                    .body
                    .tys
                    .weak_elem(dt)
                    .or_else(|| self.body.tys.arc_weak_elem(dt))
                    .or_else(|| self.body.tys.option_elem(dt).and_then(|o| self.body.tys.rc_elem(o)))
                && rl == el
                && !av.is_empty()
                && self.relate(el, &av[1..], rl, &dv, Variance::Co) => {}
            _ if let CallTarget::Builtin(b) = target
                && {
                    self.guard_coerce = dest.local == 0 && dest.proj.is_empty();
                    let done = self.call_cell(b, &avs, dt, &dv);
                    self.guard_coerce = false;
                    done
                } => {}
            _ if let CallTarget::Builtin(b) = target
                && self.call_poison(b, &avs, dt, &dv) => {}
            _ if let CallTarget::Builtin(b) = target
                && self.call_tls(b, &avs, dt, &dv) => {}
            // A builtin whose only regioned arguments are closures, and whose
            // result does not hold a closure (`cond.then(|| ..)`): the result
            // holds what the closures return, which `closure_sources` gave it
            // above, not every region they capture.
            _ if matches!(target, CallTarget::Builtin(_)) && self.closure_only_call(&avs, dt) => {}
            _ => {
                match target {
                    CallTarget::Fn(f) if self.returns_opaque(f) => {
                        let mut fixed = self.opaque_static_items(f, dt, &dv);
                        // A `'static` written in the value's type (a captured
                        // `Rc<dyn Fn()>`'s object lifetime) is no captured
                        // lifetime of the call.
                        let mut rs = Vec::new();
                        self.sc.slot_regions(dt, &mut rs);
                        if rs.len() == dv.len() {
                            fixed.extend(dv.iter().zip(&rs).filter(|(_, r)| **r == Region::Static).map(|(&v, _)| v));
                        }
                        let dv: Vec<u32> = dv.iter().copied().filter(|v| !fixed.contains(v)).collect();
                        self.call_opaque_from(&avs, &all, dt, &dv)
                    }
                    _ => self.call_opaque(&avs, dt, &dv),
                }
                if matches!(target, CallTarget::Fn(_)) {
                    self.link_closure_args(&avs, None, &[]);
                }
            }
        }
    }

    /// The item slots of a `ByNext` wrapper through its iterator's own
    /// `fn next(&mut self) -> Option<Item>` signature: the iterator's
    /// regions (`src`) reach the item only where the signature puts them,
    /// so `btree_map::Iter<'a, K, V>`'s `(&'a K, &'a V)` keeps `K`'s own
    /// regions. False (nothing paired) when the signature does not pair,
    /// for example a `-> Option<Self::Item>` written with the projection.
    fn by_next_item(&mut self, it: Ty, src: &[u32], item_ty: Ty, item: &[u32]) -> bool {
        let p = self.p;
        // A type param of this body: its own `Item = X` bound gives the
        // item exactly (`own_param_items`).
        if let Some(x) = self.own_param_items(it) {
            if x.len() != item.len() {
                return false;
            }
            self.tie_fixed(&x, item);
            return true;
        }
        // `&mut I` over a builtin iterator (core's `impl Iterator for
        // &mut I`): the item is `I`'s, so its slots follow `I`'s own
        // (`item_slots`), not the reborrow's region.
        if let TyKind::Ref(_, Mut::Mut, inner) = self.body.tys.kind(it)
            && (crate::ty::iter::iter_parts(&self.body.tys, inner).is_some() || self.body.tys.is_chars_ty(inner))
        {
            let Some(inner_items) = self.item_slots(inner, src.get(1..).unwrap_or(&[])) else { return false };
            if inner_items.len() != item.len() {
                return false;
            }
            for (&x, &y) in inner_items.iter().zip(item) {
                self.edge(x, y);
            }
            return true;
        }
        // `&mut U` over a user iterator: `U`'s own `next` signature.
        if let TyKind::Ref(_, Mut::Mut, inner) = self.body.tys.kind(it) {
            return self.by_next_item(inner, src.get(1..).unwrap_or(&[]), item_ty, item);
        }
        let Ok(fns) = crate::check::iter::by_next_fns(p, &self.body.tys, it) else { return false };
        let Some(sig) = p.regions.body_sig(p, fns.next) else { return false };
        let Some(&self_r) = sig.params.first() else { return false };
        let TyKind::Ref(_, Mut::Mut, self_inner) = p.tys.kind(self_r) else { return false };
        let Some(item_r) = p.tys.option_elem(sig.ret) else { return false };
        let univ: Vec<u32> = (0..sig.n_univ).map(|_| self.fresh()).collect();
        let mut binds: FxMap<u32, Vec<u32>> = FxMap::default();
        self.bind_tys.clear();
        let (mut sv, mut rv) = (Vec::new(), Vec::new());
        if !(self.inst(self_inner, it, &univ, &mut binds, &mut sv)
            && self.inst(item_r, item_ty, &univ, &mut binds, &mut rv)
            && sv.len() == src.len()
            && rv.len() == item.len())
        {
            return false;
        }
        for &(a, b) in &sig.facts {
            let (x, y) = (self.inst_region(a, &univ), self.inst_region(b, &univ));
            self.edge(x, y);
        }
        self.relate(it, src, it, &sv, Variance::Inv) && self.relate(item_ty, &rv, item_ty, item, Variance::Co)
    }

    /// `call_adapter` for iterator `it` (vars `v`) stored as `ByNext`
    /// wrapper type `w` (its slot vars `part`): `v` flows into the inner
    /// iterator's slots, and `next_sig_item`'s item into the item slots.
    /// False when the shapes or the signature do not pair.
    fn by_next_part(&mut self, it: Ty, v: &[u32], w: Ty, part: &[u32]) -> bool {
        let Some((_, a)) = crate::ty::iter::iter_parts(&self.body.tys, w) else { return false };
        let (Some(&inner), Some(&item_ty)) = (a.first(), a.get(1)) else { return false };
        let own = adt_regions(self.p, &self.body.tys, w) as usize;
        let (n0, n1) = (self.sc.slots(inner) as usize, self.sc.slots(item_ty) as usize);
        let (Some(ip), Some(tp)) = (part.get(own..own + n0), part.get(own + n0..own + n0 + n1)) else { return false };
        let (ip, tp) = (ip.to_vec(), tp.to_vec());
        if !self.relate(it, v, inner, &ip, Variance::Co) {
            return false;
        }
        // A type param of this body (or `&mut` of one): its own bound.
        let base = match self.body.tys.kind(it) {
            TyKind::Ref(_, Mut::Mut, x) => x,
            _ => it,
        };
        if let Some(x) = self.own_param_items(base) {
            if x.len() != n1 {
                return false;
            }
            self.tie_fixed(&x, &tp);
            return true;
        }
        match self.next_sig_item(it, v) {
            Some(item) if item.len() == n1 => self.relate(item_ty, &item, item_ty, &tp, Variance::Co),
            _ => false,
        }
    }

    /// The item slot vars of library or user iterator type `t` (its slot
    /// vars `vars`) through its `fn next(&mut self) -> Option<Item>`
    /// signature: the impl's params bind from `t`'s slots, and the item's
    /// slots are the signature's (`(&'a K, &'a V)` of `btree_map::Iter`:
    /// the own region, `K`'s slots, the own region). None when the
    /// signature does not pair (an `Option<Self::Item>` return).
    fn next_sig_item(&mut self, t: Ty, vars: &[u32]) -> Option<Vec<u32>> {
        let p = self.p;
        let fns = crate::check::iter::by_next_fns(p, &self.body.tys, t).ok()?;
        let sig = p.regions.body_sig(p, fns.next)?;
        let &self_r = sig.params.first()?;
        let TyKind::Ref(_, Mut::Mut, self_inner) = p.tys.kind(self_r) else { return None };
        let item_r = p.tys.option_elem(sig.ret)?;
        let univ: Vec<u32> = (0..sig.n_univ).map(|_| self.fresh()).collect();
        let mut binds: FxMap<u32, Vec<u32>> = FxMap::default();
        self.bind_tys.clear();
        let mut sv = Vec::new();
        if !self.inst(self_inner, t, &univ, &mut binds, &mut sv) || sv.len() != vars.len() || !self.relate(t, vars, t, &sv, Variance::Inv) {
            return None;
        }
        for &(a, b) in &sig.facts {
            let (x, y) = (self.inst_region(a, &univ), self.inst_region(b, &univ));
            self.edge(x, y);
        }
        let mut item = Vec::new();
        self.vars_from_binds(item_r, &univ, &binds, &mut item).then_some(item)
    }

    /// The slot vars of regioned signature type `r` when every type param
    /// in it is already bound (`binds`) and its regions map through `univ`
    /// (`next_sig_item`). False for a projection, a dyn type, or an
    /// unbound param.
    fn vars_from_binds(&mut self, r: Ty, univ: &[u32], binds: &FxMap<u32, Vec<u32>>, out: &mut Vec<u32>) -> bool {
        let p = self.p;
        match p.tys.kind(r) {
            TyKind::Param(j) => match binds.get(&j.0) {
                Some(v) => {
                    out.extend_from_slice(v);
                    true
                }
                None => false,
            },
            TyKind::Ref(rr, _, ri) => {
                let v = self.inst_region(rr, univ);
                out.push(v);
                self.vars_from_binds(ri, univ, binds, out)
            }
            TyKind::Tuple(ts) => p.tys.tys_of(ts).to_vec().into_iter().all(|e| self.vars_from_binds(e, univ, binds, out)),
            TyKind::Array(e, _) | TyKind::Slice(e) => self.vars_from_binds(e, univ, binds, out),
            TyKind::Adt(_, a) => {
                let lts: Vec<Region> = p.tys.args(a).iter().filter_map(|g| if let GenericArg::Lifetime(x) = g { Some(*x) } else { None }).collect();
                let n = adt_regions(p, &p.tys, r) as usize;
                if lts.len() != n {
                    return false;
                }
                for x in lts {
                    let v = self.inst_region(x, univ);
                    out.push(v);
                }
                p.tys.args(a).to_vec().into_iter().filter_map(|g| g.as_ty()).all(|e| self.vars_from_binds(e, univ, binds, out))
            }
            TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Str | TyKind::Never => true,
            _ if r == UNIT => true,
            _ => false,
        }
    }

    /// True when every argument with regions is a closure value, there is
    /// one, and `dt` holds no closure type (`closure_only` builtins).
    fn closure_only_call(&self, avs: &[(Ty, Vec<u32>)], dt: Ty) -> bool {
        let tys = &self.body.tys;
        let is_closure = |t: Ty| matches!(tys.kind(t), TyKind::Closure(..));
        avs.iter().any(|(t, _)| is_closure(*t)) && avs.iter().all(|(t, v)| v.is_empty() || is_closure(*t)) && !holds_closure(tys, dt)
    }

    /// `fold(init, f)`: the result is the initial value or what the body
    /// returns (the closure's sources, which `call` added from its
    /// requirements); the iterator's own borrow reaches it only through
    /// the body. False when the closure's body does not solve.
    fn call_fold(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let [_, (it, iv), (ct, _)] = avs else { return false };
        let TyKind::Closure(def, args) = self.body.tys.kind(*ct) else { return false };
        let mut roles = Vec::new();
        closure_roles(&mut self.sc, def, args, &mut roles);
        self.closure_reqs(def, &roles).is_some() && (iv.is_empty() || self.relate(*it, iv, dt, dv, Variance::Co))
    }

    /// `try_fold(init, f)` into `Option<B>`, `Result<B, E>` or
    /// `ControlFlow<X, B>`: as `fold`, the accumulator `B` (the result's
    /// leading slots, after `X`'s for a ControlFlow) is the initial value
    /// or what the body returns, and `E` (`X`) only what the body returns;
    /// the `&mut` borrow of the iterator reaches neither. False when the
    /// shapes differ or the closure's body does not solve.
    fn call_try_fold(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let [_, (it, iv), (ct, _)] = avs else { return false };
        let TyKind::Closure(def, args) = self.body.tys.kind(*ct) else { return false };
        let flow = self.body.tys.local_adt(dt).is_some_and(|a| self.p.is_control_flow_adt(a));
        let (acc, skip) = match self.body.tys.adt_parts(dt).map(|(_, a)| self.body.tys.args(a).iter().filter_map(|g| g.as_ty()).collect::<Vec<Ty>>()) {
            Some(xs) if flow && xs.len() == 2 => (xs[1], self.sc.slots(xs[0]) as usize),
            _ => match self.body.tys.option_elem(dt).or_else(|| self.body.tys.result_args(dt).map(|(t, _)| t)) {
                Some(t) => (t, 0),
                None => return false,
            },
        };
        let Some(av) = dv.get(skip..skip + self.sc.slots(acc) as usize) else { return false };
        let mut roles = Vec::new();
        closure_roles(&mut self.sc, def, args, &mut roles);
        self.closure_reqs(def, &roles).is_some() && (iv.is_empty() || self.relate(*it, iv, acc, av, Variance::Co))
    }

    /// `as_ref`, `borrow`, and `deref` to a pointee (`ConvDeref`,
    /// `ConvRcInner`): `&'r C` to `&T`, where `C` is a `Box<T>`, an
    /// `Rc<T>`, or a `&'c T`. The result borrows the receiver for `'r`
    /// (and `'c`), and `T`'s own regions carry over; the opaque rule would
    /// tie the receiver's borrow to all of them, a box's `'static` object
    /// lifetime included. False when the shapes differ.
    fn call_conv_deref(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let [(t0, v0)] = avs else { return false };
        let (TyKind::Ref(_, _, c), TyKind::Ref(_, _, di)) = (self.body.tys.kind(*t0), self.body.tys.kind(dt)) else { return false };
        let (Some((&r, cv)), Some((&d0, dvi))) = (v0.split_first(), dv.split_first()) else { return false };
        let (inner, iv) = match self.body.tys.kind(c) {
            TyKind::Ref(_, _, i) => {
                let Some((&cr, rest)) = cv.split_first() else { return false };
                self.edge(cr, d0);
                (i, rest)
            }
            _ => match self.body.tys.smart_elem(c) {
                Some(i) if adt_regions(self.p, &self.body.tys, c) == 0 => (i, cv),
                _ => return false,
            },
        };
        self.edge(r, d0);
        (iv.is_empty() && dvi.is_empty()) || self.relate(inner, iv, di, dvi, Variance::Co)
    }

    /// `mem::replace(dest, src)` (also `mem::take`, which lowers to it)
    /// and `mem::swap(a, b)`: values trade places through the `&mut`,
    /// whose own region reaches neither. The old value (the pointee's
    /// regions) is the result, and the new one takes the pointee's
    /// regions. `swap` is the builtin's, not the argument shape's: a
    /// replace of a `&mut U` place has a `&mut` second argument too.
    /// False when the shapes differ.
    fn call_mem(&mut self, swap: bool, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        match avs {
            [(rt, rv), (st, sv)] if swap => {
                // swap
                let (TyKind::Ref(_, _, a), TyKind::Ref(_, _, b)) = (self.body.tys.kind(*rt), self.body.tys.kind(*st)) else { return false };
                let (Some((_, av)), Some((_, bv))) = (rv.split_first(), sv.split_first()) else { return false };
                let (av, bv) = (av.to_vec(), bv.to_vec());
                (av.is_empty() && bv.is_empty()) || (self.relate(a, &av, b, &bv, Variance::Co) && self.relate(b, &bv, a, &av, Variance::Co))
            }
            [(rt, rv), (st, sv)] => {
                let TyKind::Ref(_, _, inner) = self.body.tys.kind(*rt) else { return false };
                let Some((_, pv)) = rv.split_first() else { return false };
                let pv = pv.to_vec();
                (sv.is_empty() || self.relate(*st, sv, inner, &pv, Variance::Co)) && (dv.is_empty() || self.relate(inner, &pv, dt, dv, Variance::Co))
            }
            _ => false,
        }
    }

    /// `Clone::clone(&self) -> Self` (derived and builtin clones): the
    /// result has the receiver's pointee type and its regions; the borrow
    /// of the receiver ends with the call. False when the shapes differ.
    fn call_clone(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let [(t0, v0)] = avs else { return false };
        let TyKind::Ref(_, _, x) = self.body.tys.kind(*t0) else { return false };
        !v0.is_empty() && self.relate(x, &v0[1..], dt, dv, Variance::Co)
    }

    /// `Clone::clone_from(&mut self, source: &Self)`: the two `Self`
    /// region slots are one instantiation, so they equate (a Cow
    /// that becomes `Borrowed` keeps the source's lifetime); the
    /// two borrows themselves reach nothing past the call.
    fn call_clone_from(&mut self, avs: &[(Ty, Vec<u32>)]) -> bool {
        let [(dt0, dv), (st0, sv)] = avs else { return false };
        let TyKind::Ref(_, Mut::Mut, dx) = self.body.tys.kind(*dt0) else { return false };
        let TyKind::Ref(_, _, sx) = self.body.tys.kind(*st0) else { return false };
        dx == sx && !dv.is_empty() && !sv.is_empty() && self.relate(dx, &dv[1..], sx, &sv[1..], Variance::Inv)
    }

    /// A builtin that borrows into its receiver (`v.get(i)`, `v.last_mut()`,
    /// `s.trim()`, `v.iter()`): Rust's `fn f<'r>(&'r self, ..) -> R<'r>`.
    /// Each part of the result whose type is one of the receiver's
    /// components (a `Vec`'s element type, a slice's) is a subtype of that
    /// component (equal behind `&mut`); every other region of the result is outlived
    /// by the receiver borrow's region. The other arguments do not flow
    /// into the result. False (nothing added) when the receiver is not a
    /// reference.
    /// Like `call_receiver`, for the builtins whose result borrows
    /// the receiver type's own region (its `'a`), not the `&self`
    /// loan: `ChunksExact::remainder` and the `Utf8Chunk` views
    /// (tf-slice). The result walk takes the pointee's first slot
    /// (its region param) as the borrowed region.
    fn call_own_region(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let Some((t0, v0)) = avs.first() else { return false };
        let TyKind::Ref(_, _, x) = self.body.tys.kind(*t0) else { return false };
        let Some((_, xv)) = v0.split_first() else { return false };
        let Some(&own) = xv.first() else { return false };
        let tys = &self.body.tys;
        let comp = crate::ty::iter::iter_parts(tys, x).and_then(|(_, a)| a.first().copied());
        let comp_vars: Vec<u32> = match comp {
            Some(e) => {
                let n = self.sc.slots(e) as usize;
                if n > xv.len() {
                    return false;
                }
                xv[xv.len() - n..].to_vec()
            }
            None => Vec::new(),
        };
        let mut at = 0usize;
        self.receiver_walk(dt, dv, &mut at, own, comp, &comp_vars, Variance::Co);
        true
    }

    fn call_receiver(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let Some((t0, v0)) = avs.first() else { return false };
        let TyKind::Ref(_, _, x) = self.body.tys.kind(*t0) else { return false };
        let Some((&r, xv)) = v0.split_first() else { return false };
        let tys = &self.body.tys;
        let comp: Option<Ty> = match tys.kind(x) {
            TyKind::Slice(e) | TyKind::Array(e, _) => Some(e),
            _ => tys
                .vec_elem(x)
                .or_else(|| tys.lock_elem(x).map(|l| l.1))
                .or_else(|| tys.poison_elem(x))
                .or_else(|| {
                    matches!(crate::ty::sync::sync_kind(tys, x), Some(crate::ty::sync::SyncTy::Receiver | crate::ty::sync::SyncTy::OnceLock))
                        .then(|| tys.adt_first_ty_arg(x))
                        .flatten()
                })
                .or_else(|| {
                    let (k, a) = crate::ty::iter::iter_parts(tys, x)?;
                    (k == crate::ty::iter::IterKind::VecDrain).then(|| a[0])
                }),
        };
        // The element type sits at the end of the receiver's slots (after
        // any region params of the container, which these builtins lack).
        let comp_vars: Vec<u32> = match comp {
            Some(e) => {
                let n = self.sc.slots(e) as usize;
                if n > xv.len() {
                    return false;
                }
                xv[xv.len() - n..].to_vec()
            }
            None => Vec::new(),
        };
        let mut at = 0usize;
        self.receiver_walk(dt, dv, &mut at, r, comp, &comp_vars, Variance::Co);
        true
    }

    /// The result slots of a `receiver_builtin` call (`call_receiver`): an
    /// element of the receiver's component type takes the component's
    /// vars by subtyping at the variance of its position (`v`; equal behind
    /// `&mut`), as rustc's assignment of the call's value; any other slot
    /// is outlived by the receiver's borrow `r`.
    #[allow(clippy::too_many_arguments)]
    fn receiver_walk(&mut self, t: Ty, dv: &[u32], at: &mut usize, r: u32, comp: Option<Ty>, comp_vars: &[u32], v: Variance) {
        if comp == Some(t) && self.sc.slots(t) as usize == comp_vars.len() {
            let n = comp_vars.len();
            if let Some(d) = dv.get(*at..*at + n) {
                let d = d.to_vec();
                self.relate(t, comp_vars, t, &d, v);
            }
            *at += n;
            return;
        }
        let tys = &self.body.tys;
        match tys.kind(t) {
            TyKind::Ref(_, m, inner) => {
                if let Some(&d) = dv.get(*at) {
                    self.edge(r, d);
                }
                *at += 1;
                let iv = if m.is_mut() { Variance::Inv } else { Variance::Co };
                self.receiver_walk(inner, dv, at, r, comp, comp_vars, v.then(iv));
            }
            TyKind::Adt(def, args) => {
                for _ in 0..adt_regions(self.p, tys, t) {
                    if let Some(&d) = dv.get(*at) {
                        self.edge(r, d);
                    }
                    *at += 1;
                }
                let tys_args: Vec<Ty> = tys.args(args).iter().filter_map(|g| g.as_ty()).collect();
                for (j, e) in tys_args.into_iter().enumerate() {
                    let (pv, _) = self.p.regions.adts(self.p).arg_modes(self.p, def, j);
                    self.receiver_walk(e, dv, at, r, comp, comp_vars, v.then(pv));
                }
            }
            TyKind::Tuple(ts) => {
                for e in tys.tys_of(ts).to_vec() {
                    self.receiver_walk(e, dv, at, r, comp, comp_vars, v);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) => self.receiver_walk(e, dv, at, r, comp, comp_vars, v),
            TyKind::RawPtr(m, e) => {
                let iv = if m.is_mut() { Variance::Inv } else { Variance::Co };
                self.receiver_walk(e, dv, at, r, comp, comp_vars, v.then(iv))
            }
            _ => {
                let n = self.sc.slots(t) as usize;
                for i in 0..n {
                    if let Some(&d) = dv.get(*at + i) {
                        self.edge(r, d);
                    }
                }
                *at += n;
            }
        }
    }

    /// The `Cell` and `RefCell` builtins on a `&Cell<T>` or `&RefCell<T>`
    /// receiver (W-STD-A). Interior mutability stores through a shared
    /// reference, so a stored value flows into the cell's `T` slots as
    /// through `&mut`; a read flows out of them; a guard's `T` is the
    /// cell's (`RefMut` invariantly) behind the guard's own region, which
    /// the borrow of the cell outlives. False for any other call (the
    /// caller goes on).
    /// `PoisonError::into_inner` (and `get_ref`, `get_mut`): the result
    /// is the error's value (or a borrow of it) with exactly its slots,
    /// so a guard's borrow does not reach the `'static` object lifetime
    /// of what it guards (`lock().unwrap_or_else(PoisonError::into_inner)`).
    fn call_poison(&mut self, b: crate::check::Builtin, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        use crate::check::sync::SyncOp as S;
        let crate::check::Builtin::Sync(op @ (S::PoisonIntoInner | S::PoisonGetRef | S::PoisonGetMut)) = b else { return false };
        let Some((at, av)) = avs.first() else { return false };
        let tys = &self.body.tys;
        let (err, ev, outer) = match tys.kind(*at) {
            TyKind::Ref(_, _, inner) if !av.is_empty() => (inner, av[1..].to_vec(), Some(av[0])),
            _ => (*at, av.clone(), None),
        };
        let Some(g) = tys.adt_first_ty_arg(err) else { return false };
        if adt_regions(self.p, tys, err) != 0 || ev.len() != self.sc.slots(g) as usize {
            return false;
        }
        match (op, outer, self.body.tys.kind(dt)) {
            (S::PoisonIntoInner, None, _) => self.relate(g, &ev, dt, dv, Variance::Co),
            (S::PoisonGetRef | S::PoisonGetMut, Some(o), TyKind::Ref(_, m, inner)) if !dv.is_empty() => {
                self.edge(o, dv[0]);
                let v = if m.is_mut() { Variance::Inv } else { Variance::Co };
                self.relate(g, &ev, inner, &dv[1..], v)
            }
            _ => false,
        }
    }

    fn call_cell(&mut self, b: crate::check::Builtin, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        use crate::check::Builtin as B;
        if !matches!(
            b,
            B::RefCellBorrow
                | B::RefCellBorrowMut
                | B::RefCellTryBorrow
                | B::RefCellTryBorrowMut
                | B::CellGet
                | B::CellSet
                | B::CellReplace
                | B::RefCellReplace
                | B::CellSwap
                | B::RefCellSwap
                | B::CellTake
                | B::RefCellTake
        ) {
            return false;
        }
        let tys = &self.body.tys;
        let Some((rt, rv)) = avs.first() else { return false };
        let TyKind::Ref(_, _, cell) = tys.kind(*rt) else { return false };
        let Some(elem) = tys.cell_elem(cell).or_else(|| tys.refcell_elem(cell)) else { return false };
        if rv.is_empty() {
            return false;
        }
        let tv = rv[1..].to_vec();
        match b {
            // A try form's `Result<Ref<T>, E>` starts with the guard's
            // slots; the error type has none.
            B::RefCellBorrow | B::RefCellBorrowMut | B::RefCellTryBorrow | B::RefCellTryBorrowMut => {
                let Some(&g) = dv.first() else { return true };
                self.edge(rv[0], g);
                // A `RefMut` over `dyn Tr` returned at once coerces into the
                // return place (`guard_coerce`): its object lifetime may
                // shorten there.
                let to_dyn = self.guard_coerce && b == B::RefCellBorrowMut && matches!(self.body.tys.kind(elem), TyKind::Dyn(..));
                let v = if matches!(b, B::RefCellBorrowMut | B::RefCellTryBorrowMut) && !to_dyn { Variance::Inv } else { Variance::Co };
                if !self.relate(elem, &tv, elem, &dv[1..], v) {
                    self.equate_all(&tv, &dv[1..]);
                }
            }
            B::CellSwap | B::RefCellSwap => {
                if let Some((_, ov)) = avs.get(1)
                    && ov.len() == rv.len()
                    && !self.relate(elem, &tv, elem, &ov[1..], Variance::Inv)
                {
                    self.equate_all(&tv, &ov[1..]);
                }
            }
            _ => {
                // `set` and `replace` store their argument; `get`,
                // `replace`, and `take` hand back a value out of the cell.
                if let Some((xt, xv)) = avs.get(1)
                    && !self.relate(*xt, xv, elem, &tv, Variance::Co)
                {
                    self.flow_all(xv, &tv);
                }
                if !self.relate(elem, &tv, dt, dv, Variance::Co) {
                    self.flow_all(&tv, dv);
                }
            }
        }
        true
    }

    /// The `LocalKey` method builtins (W-TLS, check/tls.rs). A key's
    /// value type is a static's type, so each of its regions is
    /// `'static` (the erased type does not say so: pin them here). `set`
    /// and `replace` on a `Cell` or `RefCell` key move their argument
    /// into the thread's value, so it flows into those slots, as a store
    /// through `Cell::set` does (`call_cell`). The rest is the opaque
    /// rule. False for any other call (the caller goes on).
    fn call_tls(&mut self, b: crate::check::Builtin, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        use crate::check::Builtin as B;
        if !crate::lower::tls::is_key_method(b) {
            return false;
        }
        let tys = &self.body.tys;
        let Some((kt, kv)) = avs.first() else { return false };
        let TyKind::Ref(_, _, key) = tys.kind(*kt) else { return false };
        let Some(t) = tys.local_key_elem(key) else { return false };
        let u = tys.cell_elem(t).or_else(|| tys.refcell_elem(t));
        let tv = kv.get(1..).unwrap_or_default().to_vec();
        for &v in &tv {
            self.edge(v, 0);
        }
        // `Cell<U>` and `RefCell<U>` carry no regions of their own.
        if matches!(b, B::TlsSet | B::TlsReplace)
            && let Some(u) = u
            && let Some((xt, xv)) = avs.get(1)
            && !self.relate(*xt, xv, u, &tv, Variance::Co)
        {
            self.flow_all(xv, &tv);
        }
        // `with(f)` and kin return what `f` returns (`F: FnOnce(&T) -> R`):
        // `call` already flowed the closure's output sources
        // (`closure_sources`) into the result, and its `&T` argument is
        // higher-ranked. Its captures do not reach the result otherwise.
        // Any other `f` (a fn item) takes the conservative rule.
        let closure_f = avs.get(1).is_some_and(|(ft, _)| matches!(self.body.tys.kind(*ft), TyKind::Closure(..)));
        if !(closure_f && matches!(b, B::TlsWith | B::TlsTryWith | B::TlsWithBorrow | B::TlsWithBorrowMut)) {
            self.call_opaque(avs, dt, dv);
        }
        true
    }

    /// `it.flat_map(f)`, typed `Flatten<Map<I, F, B>, U>` (check/iter.rs):
    /// the arguments make the inner `Map` as `it.map(f)` does
    /// (`call_adapter`), and the front and back iterators `U` hold what
    /// the map's parts hold. A `&mut` capture of `f` then stays apart from
    /// the regions it points to (else a `RefMut` it borrows would stay
    /// borrowed for the guard's whole life). False for another shape.
    fn call_flat_map(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        use crate::ty::iter::IterKind as K;
        let Some((K::Flatten, a)) = crate::ty::iter::iter_parts(&self.body.tys, dt) else { return false };
        let [m, u] = a[..] else { return false };
        if !matches!(crate::ty::iter::iter_parts(&self.body.tys, m), Some((K::Map, _))) || avs.len() != 2 {
            return false;
        }
        let own = adt_regions(self.p, &self.body.tys, dt) as usize;
        let (nm, nu) = (self.sc.slots(m) as usize, self.sc.slots(u) as usize);
        if own != 0 || nm + nu != dv.len() {
            return false;
        }
        let (mv, uv) = (dv[..nm].to_vec(), dv[nm..].to_vec());
        self.call_adapter(avs, m, &mv);
        self.flow_all(&mv, &uv);
        if has_interior(&self.body.tys, u) {
            self.flow_all(&uv, &mv);
        }
        true
    }

    /// A builtin that builds an iterator adapter (`map`, `filter`,
    /// `inspect`, ...): the adapter stores its arguments as its type args,
    /// so an argument whose type is one of those args flows into that part
    /// only (a closure's captures do not reach the source iterator's
    /// regions). Any other argument flows into every part.
    fn call_adapter(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) {
        let Some((_, args)) = self.body.tys.adt_parts(dt) else { return self.call_opaque(avs, dt, dv) };
        let comps: Vec<Ty> = self.body.tys.args(args).iter().filter_map(|g| g.as_ty()).collect();
        let mut ranges: Vec<(usize, usize)> = Vec::with_capacity(comps.len());
        let mut at = adt_regions(self.p, &self.body.tys, dt) as usize;
        for &c in &comps {
            let n = self.sc.slots(c) as usize;
            ranges.push((at, n));
            at += n;
        }
        if at != dv.len() {
            return self.call_opaque(avs, dt, dv);
        }
        let mut used = vec![false; comps.len()];
        // A fallback flow into an adapter that can write through shared
        // memory goes both ways (see `has_interior`).
        let interior = has_interior(&self.body.tys, dt);
        // Parts a source fills exactly. A source with no exact part relates
        // the parts of it the adapter holds at their variance (`store_into`:
        // `vec.into_iter()` of an invariant `T`), and its other regions flow
        // only into the slots no source fills, after every source is paired
        // (two chained closures keep their captures apart).
        let mut taken = vec![false; dv.len()];
        let mut pending: Vec<(Ty, &[u32])> = Vec::new();
        for (t, v) in avs {
            if v.is_empty() {
                continue;
            }
            // A library or user iterator passed where the adapter's type
            // holds its `ByNext` wrapper: the iterator is the wrapper's
            // inner part, and the item part is what its `next` returns.
            let wrapped = (0..comps.len()).find(|&j| {
                !used[j] && matches!(crate::ty::iter::iter_parts(&self.body.tys, comps[j]), Some((crate::ty::iter::IterKind::ByNext, a)) if a.first() == Some(t))
            });
            if let Some(j) = wrapped {
                used[j] = true;
                let (s0, n) = ranges[j];
                let part = dv[s0..s0 + n].to_vec();
                if self.by_next_part(*t, v, comps[j], &part) {
                    taken[s0..s0 + n].fill(true);
                } else {
                    pending.push((*t, v));
                }
                continue;
            }
            match (0..comps.len()).find(|&j| !used[j] && comps[j] == *t && ranges[j].1 == v.len()) {
                Some(j) => {
                    used[j] = true;
                    let (s0, n) = ranges[j];
                    let part = dv[s0..s0 + n].to_vec();
                    if self.relate(*t, v, comps[j], &part, Variance::Co) {
                        taken[s0..s0 + n].fill(true);
                    } else {
                        pending.push((*t, v));
                    }
                }
                None => pending.push((*t, v)),
            }
        }
        // The parts of each unpaired source the adapter holds, first, then
        // the rest of their regions into what no source fills.
        for &(t, v) in &pending {
            let filled = self.store_into(t, v, dt, dv);
            for (k, f) in taken.iter_mut().zip(filled) {
                *k |= f;
            }
        }
        let rest: Vec<u32> = dv.iter().zip(&taken).filter(|(_, k)| !**k).map(|(&x, _)| x).collect();
        for (_, v) in pending {
            self.flow_all(v, &rest);
            if interior {
                self.flow_all(&rest, v);
            }
        }
        self.map_output_part(dt, dv, &ranges);
    }

    /// A `map`-family adapter `dt` (vars `dv`, parts at `ranges`) whose
    /// callable is a fn item or a `dyn Fn` (behind references and boxes):
    /// its output part `B` holds what the callable returns for the inner
    /// items (`callable_out`), so a reader of `B` sees the items' borrows.
    /// A closure ties `B` through `closure_reqs`. A fn pointer is left
    /// alone: a library field type writes `Map<I, fn(&(K, V)) -> &K>`, whose
    /// `B` is no place of this call; its readers go through `iter_items`.
    /// An unpaired callable lets every item and callable region reach `B`.
    fn map_output_part(&mut self, dt: Ty, dv: &[u32], ranges: &[(usize, usize)]) {
        use crate::ty::iter::IterKind as K;
        let Some((K::Map | K::FilterMap | K::MapWhile, a)) = crate::ty::iter::iter_parts(&self.body.tys, dt) else { return };
        let (Some(&a0), Some(&f), Some(&bt)) = (a.first(), a.get(1), a.get(2)) else { return };
        if matches!(self.body.tys.kind(f), TyKind::Closure(..) | TyKind::FnPtr(_)) {
            return;
        }
        let (Some(&(s0, n0)), Some(&(s1, n1)), Some(&(s2, n2))) = (ranges.first(), ranges.get(1), ranges.get(2)) else { return };
        let (iv, fv, out) = (dv[s0..s0 + n0].to_vec(), dv[s1..s1 + n1].to_vec(), dv[s2..s2 + n2].to_vec());
        let mut xs = Vec::new();
        if !self.iter_items(a0, &iv, &mut xs) {
            xs = vec![iv.clone()];
        }
        for x in xs {
            if !self.callable_out(f, &fv, &x, bt, &out) {
                let srcs: Vec<u32> = x.iter().chain(&fv).copied().collect();
                self.flow_all(&srcs, &out);
            }
        }
    }
    /// The vars of the slots of `t` (laid out from `*at` in `vars`) that do
    /// not sit inside a closure type, plus the captured sources of the
    /// closures that return borrows.
    fn non_closure_slots(&mut self, t: Ty, vars: &[u32], at: &mut usize, out: &mut Vec<u32>) {
        let n = self.sc.slots(t) as usize;
        if let TyKind::Closure(..) = self.body.tys.kind(t) {
            // A closure that returns borrows: the items may hold its
            // captured sources (`map(|i| &v[i])`).
            self.closure_sources(t, vars, at, out);
            return;
        }
        match self.body.tys.kind(t) {
            TyKind::Ref(_, _, inner) => {
                if let Some(&v) = vars.get(*at) {
                    out.push(v);
                }
                *at += 1;
                self.non_closure_slots(inner, vars, at, out);
            }
            TyKind::Adt(_, args) => {
                for _ in 0..adt_regions(self.p, &self.body.tys, t) {
                    if let Some(&v) = vars.get(*at) {
                        out.push(v);
                    }
                    *at += 1;
                }
                for g in self.body.tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.non_closure_slots(e, vars, at, out);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in self.body.tys.tys_of(ts).to_vec() {
                    self.non_closure_slots(e, vars, at, out);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.non_closure_slots(e, vars, at, out),
            _ => {
                out.extend(vars.iter().skip(*at).take(n).copied());
                *at += n;
            }
        }
    }

    /// Closure `def` at its creating statement (`force`), or at its first
    /// use (a closure with no captures has no creating statement): makes
    /// its argument vars once, and adds its body's requirements over the
    /// captured slots `caps` (`closure_reqs`), else the contract edges.
    fn closure_created(&mut self, def: DefId, roles: &[(bool, bool)], caps: &[u32], force: bool) -> Option<Vec<u32>> {
        let first = self.created.insert(def, ()).is_none();
        if !first && !force {
            return self.closure_args.get(&def).cloned();
        }
        let fe = self.fn_ends(def);
        let reqs = self.closure_reqs(def, roles);
        if reqs.is_none() {
            self.contract_edges(roles, caps);
        }
        let vars = self.make_arg_vars(def, roles, caps, reqs.is_none());
        let hr_out = self.bound_hr_out_slots(def);
        for &(a, b) in reqs.iter().flat_map(|r| r.iter()) {
            let var = |e: End| match e {
                End::Static => Some(0),
                End::Cap(i) => caps.get(i as usize).copied(),
                End::Arg(j) => vars.as_ref().and_then(|v| v.get(j as usize)).copied(),
                End::Fn(k) => fe.get(k as usize).copied().flatten(),
                // What a call's result holds: the call's rule, except an
                // output slot the closure's bound makes its input's
                // (`ClosureEntry::bound_output`): that is any region a
                // caller passes, so what it holds outlives `'static`.
                End::Out(k) if hr_out.contains(&k) => Some(0),
                End::Out(_) => None,
            };
            if let (Some(x), Some(y)) = (var(a), var(b)) {
                self.edge(x, y);
            }
        }
        vars
    }

    /// The returned iterator's items outlive the regions its `Iterator<Item
    /// = T>` bound writes in `T` (`OwnSig::ret_vars`): for a returned
    /// `Map` (or `FilterMap`), whose `B` slots hold what its closure
    /// returns and pair with `T`'s, each slot of a named lifetime or
    /// `'static` outlives that universal.
    fn rpit_item_edges(&mut self, item: Ty) {
        let t = self.body.locals[0].ty;
        let n = self.sc.slots(t) as usize;
        let base = self.local_base[0];
        let vars: Vec<u32> = (0..n as u32).map(|i| base + i).collect();
        let mut rs = Vec::new();
        regions_of(&self.p.tys, item, &mut rs);
        let mut cands: Vec<Vec<u32>> = Vec::new();
        // `Map<I, F, B>`'s items are its `B` slots, which the closure's
        // output flows into at the `map` call.
        let parts = crate::ty::iter::iter_parts(&self.body.tys, t);
        if let Some((crate::ty::iter::IterKind::Map | crate::ty::iter::IterKind::FilterMap | crate::ty::iter::IterKind::MapWhile, a)) = parts
            && let [i, f, b, ..] = a[..]
        {
            let (ni, nf, nb) = (self.sc.slots(i) as usize, self.sc.slots(f) as usize, self.sc.slots(b) as usize);
            let at = adt_regions(self.p, &self.body.tys, t) as usize + ni + nf;
            match vars.get(at..at + nb) {
                Some(v) => cands.push(v.to_vec()),
                None => return,
            }
        } else if !self.iter_items(t, &vars, &mut cands) {
            // A library or user iterator's items come through flows lust
            // keeps coarse (a generic method's result holds its receiver's
            // loan): not checked.
            return;
        }
        for c in cands {
            if c.len() != rs.len() {
                continue;
            }
            for (&v, &r) in c.iter().zip(&rs) {
                let mut none = || u32::MAX;
                let u = if r == Region::Erased { self.own.ret_elided.unwrap_or(u32::MAX) } else { univ_of(r, &mut none) };
                if u != u32::MAX {
                    self.edge(v, u);
                }
            }
        }
    }

    /// The output slots of closure `def` that its bound output makes the
    /// one higher-ranked input's (`ClosureEntry::bound_output`, `Bound(0)`;
    /// a dyn's named lifetime is `Bound(1)`, `rebind_bound`).
    fn bound_hr_out_slots(&mut self, def: DefId) -> Vec<u32> {
        let Some((bo, out_t)) = self.p.gx.closures.get(&def).and_then(|c| c.bound_output.map(|b| (b, c.output))) else { return Vec::new() };
        let mut named: Vec<Region> = Vec::new();
        if !regioned_slots(&mut self.sc, bo, out_t, &mut named) {
            return Vec::new();
        }
        named.iter().enumerate().filter(|(_, r)| matches!(r, Region::Bound(0))).map(|(k, _)| k as u32).collect()
    }

    /// The argument slot vars of closure `def` (`closure_created` at its
    /// first sight). None for a closure whose arguments are higher-ranked.
    fn closure_arg_vars(&mut self, def: DefId, roles: &[(bool, bool)], caps: &[u32]) -> Option<Vec<u32>> {
        self.closure_created(def, roles, caps, false)
    }

    /// What the body of closure `def` needs between its captured and free
    /// argument regions and `'static` (rustc's closure requirements): the
    /// body solves on its own and does not report those relations; its
    /// creator adds them. None for a closure with no such region, or when
    /// the body does not check or lower (its own check reports that).
    fn closure_reqs(&mut self, def: DefId, roles: &[(bool, bool)]) -> Option<std::rc::Rc<Vec<(End, End)>>> {
        if let Some(r) = self.closure_reqs.get(&def) {
            return r.clone();
        }
        let c = self.p.gx.closures.get(&def)?;
        let free = matches!(closure_arg_slots(&mut self.sc, c), Ok(v) if v.iter().any(|(r, _)| r.is_some()));
        let fn_lts = !root_bound_lifetimes(self.p, c.body_fn).is_empty();
        let r = if free || !roles.is_empty() || c.call_out || fn_lts {
            // `check_fn` of a closure is its enclosing fn's check.
            let cf = c.body_fn;
            let mut root = c.parent;
            while let Some(e) = self.p.gx.closure_fns.get(&root).and_then(|d| self.p.gx.closures.get(d)) {
                root = e.parent;
            }
            if self.root_check.as_ref().is_none_or(|(r, _)| *r != root) {
                let (checked, errs) = crate::check::check_fn(self.p, root);
                self.root_check = Some((root, (errs.is_empty() && !checked.poisoned).then_some(checked)));
            }
            match self.root_check.as_ref().and_then(|(_, c)| c.clone()) {
                Some(checked) => {
                    let body = crate::lower::lower(self.p, cf, checked);
                    super::closure_requirements(self.p, &body).map(std::rc::Rc::new)
                }
                None => None,
            }
        } else {
            None
        };
        // A requirement on a lifetime of the enclosing fn needs this body's
        // universal for it (none outside that fn): else the caller's
        // conservative rule.
        let fe = self.fn_ends(def);
        let r = r.filter(|reqs| reqs.iter().all(|&(a, b)| [a, b].iter().all(|e| !matches!(e, End::Fn(k) if fe.get(*k as usize).copied().flatten().is_none()))));
        self.closure_reqs.insert(def, r.clone());
        r
    }

    /// This body's universal for lifetime `k` of its root fn: `k + 1` in the
    /// fn itself, the `OwnSig::fn_lts` universal in a closure body (None
    /// when the closure has none for it).
    fn root_univ(&self, k: u32) -> Option<u32> {
        if self.own.closure { self.own.fn_lts.get(k as usize).copied().flatten() } else { Some(k + 1) }
    }

    /// Per lifetime `k` of the fn that encloses closure `def`: this body's
    /// universal for `'k` (`End::Fn(k)`). The fn's own body has `k + 1`; a
    /// closure body of the same fn its `OwnSig::fn_lts`; a body outside
    /// that fn none.
    fn fn_ends(&self, def: DefId) -> Vec<Option<u32>> {
        let p = self.p;
        let Some(c) = p.gx.closures.get(&def) else { return Vec::new() };
        if root_fn(p, c.parent) != root_fn(p, self.body.fn_id) {
            return Vec::new();
        }
        if self.own.closure {
            return self.own.fn_lts.clone();
        }
        let n = p.regions.own_body_sig(p, self.body.fn_id).map_or(0, |s| s.n_univ);
        (0..n).map(|k| Some(k + 1)).collect()
    }

    /// `map.iter()` and kin (W-STD-B): the iterator's own region is
    /// outlived by the map borrow, and its key and value regions follow
    /// the map's (the values invariantly for `iter_mut` and
    /// `values_mut`, which hand out `&mut V`). False (nothing added) for
    /// the by-value forms, which take the opaque rule.
    /// An `option` or `result` iterator construction (fx-option-rest):
    /// from `&'a Option<T>` or `&'a Result<T, E>` the `Iter` holds the
    /// loan and `T`'s regions (invariantly for `IterMut`, whose items
    /// can write through); by value the `IntoIter` owns `T`'s regions
    /// and an `Err`'s regions end at the call.
    fn call_opt_res(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        use crate::ty::iter::IterKind as K;
        let Some((t0, v0)) = avs.first() else { return false };
        let Some((ik, iargs)) = crate::ty::iter::iter_parts(&self.body.tys, dt) else { return false };
        let t = iargs[0];
        let n = self.sc.slots(t) as usize;
        match self.body.tys.kind(*t0) {
            TyKind::Ref(_, _, _) => {
                let (Some((&r, mv)), Some((&i, iv))) = (v0.split_first(), dv.split_first()) else { return false };
                if mv.len() < n || iv.len() < n {
                    return false;
                }
                self.edge(r, i);
                let var = if matches!(ik, K::OptionIterMut | K::ResultIterMut) { Variance::Inv } else { Variance::Co };
                let (a, b) = (mv[..n].to_vec(), iv[..n].to_vec());
                self.relate(t, &a, t, &b, var);
                true
            }
            _ => {
                if v0.len() < n || dv.len() < n {
                    return false;
                }
                let (a, b) = (v0[..n].to_vec(), dv[..n].to_vec());
                self.relate(t, &a, t, &b, Variance::Co);
                true
            }
        }
    }

    /// `slice::from_ref(&'a T) -> &'a [T]` and `from_mut`
    /// (fx-option-rest): the slice's region is the argument's, and
    /// `T`'s own regions flow through (invariantly for `from_mut`,
    /// which can write a `T` back).
    fn call_from_ref(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let Some((t0, v0)) = avs.first() else { return false };
        let TyKind::Ref(_, m, t) = self.body.tys.kind(*t0) else { return false };
        let (Some((&r, av)), Some((&d, rest))) = (v0.split_first(), dv.split_first()) else { return false };
        let n = self.sc.slots(t) as usize;
        if av.len() < n || rest.len() < n {
            return false;
        }
        self.edge(r, d);
        let var = if m.is_mut() { Variance::Inv } else { Variance::Co };
        let (a, b) = (av[..n].to_vec(), rest[..n].to_vec());
        self.relate(t, &a, t, &b, var);
        true
    }

    fn call_hash_iter(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        use crate::ty::iter::IterKind as K;
        let Some((t0, v0)) = avs.first() else { return false };
        let TyKind::Ref(_, _, map) = self.body.tys.kind(*t0) else { return false };
        let Some((ik, _)) = crate::ty::iter::iter_parts(&self.body.tys, dt) else { return false };
        let Some((_, margs)) = crate::ty::hash::hash_parts(&self.body.tys, map) else { return false };
        let (Some((&r, mv)), Some((&i, iv))) = (v0.split_first(), dv.split_first()) else { return false };
        let parts: Vec<(Ty, usize)> =
            margs.iter().take(if matches!(ik, K::SetIter | K::SetDrain) { 1 } else { 2 }).map(|&t| (t, self.sc.slots(t) as usize)).collect();
        let n: usize = parts.iter().map(|p| p.1).sum();
        if mv.len() < n || iv.len() < n {
            return false;
        }
        self.edge(r, i);
        let mut at = 0;
        for (j, (t, n)) in parts.into_iter().enumerate() {
            // A drain holds the map's table under its `&'a mut` loan.
            let var = if (j == 1 && matches!(ik, K::MapIterMut | K::MapValuesMut)) || ik.is_hash_drain() { Variance::Inv } else { Variance::Co };
            let (a, b) = (mv[at..at + n].to_vec(), iv[at..at + n].to_vec());
            self.relate(t, &a, t, &b, var);
            at += n;
        }
        true
    }

    /// `map.insert(k, v)` and `map.remove(&q)`: rustc's `-> Option<V>`
    /// holds the map's V (a subtype of it), not the `&mut` loan of the
    /// map. `insert` stores its arguments: every argument region flows
    /// into the map's slots, as `call_opaque`'s `&mut` rule. False when
    /// the types do not pair (the caller takes the conservative rule).
    fn call_map_value(&mut self, b: crate::check::Builtin, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let Some((t0, v0)) = avs.first() else { return false };
        let TyKind::Ref(_, Mut::Mut, map) = self.body.tys.kind(*t0) else { return false };
        let Some((crate::ty::hash::HashTy::HashMap, margs)) = crate::ty::hash::hash_parts(&self.body.tys, map) else { return false };
        let (&[k, v, ..], Some(out)) = (&margs[..], self.body.tys.option_elem(dt)) else { return false };
        let (nk, nv) = (self.sc.slots(k) as usize, self.sc.slots(v) as usize);
        // `remove_entry` hands back the stored `(K, V)`: the map's own key
        // and value regions, not the receiver's loan.
        if b == crate::check::Builtin::MapRemoveEntry {
            let pair = matches!(self.body.tys.kind(out), TyKind::Tuple(ts) if self.body.tys.tys_of(ts) == [k, v]);
            if !pair || dv.len() != nk + nv || v0.len() < 1 + nk + nv {
                return false;
            }
            let (kv, vv) = (v0[1..1 + nk].to_vec(), v0[1 + nk..1 + nk + nv].to_vec());
            self.relate(k, &kv, k, &dv[..nk], Variance::Co);
            self.relate(v, &vv, v, &dv[nk..], Variance::Co);
            return true;
        }
        if out != v || dv.len() != nv || v0.len() < 1 + nk + nv {
            return false;
        }
        let vv = v0[1 + nk..1 + nk + nv].to_vec();
        self.relate(v, &vv, v, dv, Variance::Co);
        if b == crate::check::Builtin::MapInsert {
            // The key flows into the map's K slots and the value into its
            // V slots (`HashMap<&'a str, &'static str>::insert(k, v)`: `k`
            // need not be `'static`).
            let (kmap, vmap) = (v0[1..1 + nk].to_vec(), v0[1 + nk..1 + nk + nv].to_vec());
            let paired = match &avs[1..] {
                [(kt, kv), (vt, vv)] => {
                    let (kt, kv, vt, vv) = (*kt, kv.clone(), *vt, vv.clone());
                    (kv.is_empty() || self.relate(kt, &kv, k, &kmap, Variance::Co)) && (vv.is_empty() || self.relate(vt, &vv, v, &vmap, Variance::Co))
                }
                _ => false,
            };
            if !paired {
                let others: Vec<u32> = avs[1..].iter().flat_map(|(_, v)| v.iter().copied()).collect();
                self.flow_all(&others, &v0[1..]);
            }
        }
        true
    }

    /// `map.get(&q)` and `map.get_mut(&q)` (rustc `-> Option<&'r V>`):
    /// the reference is the receiver's loan, and `V` is the map's V (a
    /// subtype behind `&`, equal behind `&mut`), as `call_receiver` does for
    /// a Vec. The key is only read. False when the types do not pair.
    fn call_map_get(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let Some((t0, v0)) = avs.first() else { return false };
        let TyKind::Ref(_, _, map) = self.body.tys.kind(*t0) else { return false };
        let Some((crate::ty::hash::HashTy::HashMap, margs)) = crate::ty::hash::hash_parts(&self.body.tys, map) else { return false };
        let &[k, v, ..] = &margs[..] else { return false };
        let (nk, nv) = (self.sc.slots(k) as usize, self.sc.slots(v) as usize);
        if v0.len() < 1 + nk + nv || dv.len() != nv + 1 {
            return false;
        }
        let vv = v0[1 + nk..1 + nk + nv].to_vec();
        let mut at = 0usize;
        self.receiver_walk(dt, dv, &mut at, v0[0], Some(v), &vv, Variance::Co);
        true
    }

    /// `map.get_key_value(&q)` (rustc `-> Option<(&'r K, &'r V)>`): both
    /// references are the receiver's loan, and K and V are the map's own
    /// (subtypes behind the `&`). False when the types do not pair.
    fn call_map_key_value(&mut self, avs: &[(Ty, Vec<u32>)], dv: &[u32]) -> bool {
        let Some((t0, v0)) = avs.first() else { return false };
        let TyKind::Ref(_, _, map) = self.body.tys.kind(*t0) else { return false };
        let Some((crate::ty::hash::HashTy::HashMap, margs)) = crate::ty::hash::hash_parts(&self.body.tys, map) else { return false };
        let &[k, v, ..] = &margs[..] else { return false };
        let (nk, nv) = (self.sc.slots(k) as usize, self.sc.slots(v) as usize);
        if v0.len() < 1 + nk + nv || dv.len() != nk + nv + 2 {
            return false;
        }
        let (kv, vv) = (v0[1..1 + nk].to_vec(), v0[1 + nk..1 + nk + nv].to_vec());
        let (rk, dk, rv, dvv) = (dv[0], dv[1..1 + nk].to_vec(), dv[1 + nk], dv[2 + nk..].to_vec());
        self.edge(v0[0], rk);
        self.edge(v0[0], rv);
        self.relate(k, &kv, k, &dk, Variance::Co) && self.relate(v, &vv, v, &dvv, Variance::Co)
    }

    /// `set.get(&q)` (rustc `-> Option<&'r T>`): the reference is the
    /// receiver's loan, and `T` is the set's own `T` (a subtype behind the
    /// `&`), as `call_map_get` does for a map's V. A `HashSet<&'static
    /// str>` element stays `'static`. False when the types do not pair.
    fn call_set_get(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let Some((t0, v0)) = avs.first() else { return false };
        let TyKind::Ref(_, _, set) = self.body.tys.kind(*t0) else { return false };
        let Some((crate::ty::hash::HashTy::HashSet, sargs)) = crate::ty::hash::hash_parts(&self.body.tys, set) else { return false };
        let Some(&t) = sargs.first() else { return false };
        let nt = self.sc.slots(t) as usize;
        if v0.len() < 1 + nt || dv.len() != nt + 1 {
            return false;
        }
        let tv = v0[1..1 + nt].to_vec();
        let mut at = 0usize;
        self.receiver_walk(dt, dv, &mut at, v0[0], Some(t), &tv, Variance::Co);
        true
    }

    /// The Entry API (W-STD-B): `map.entry(k)` holds the `&'a mut` loan
    /// and the map's K and V regions (invariant: it can insert, and the
    /// probe key flows into K); the `&'a mut V` an Entry method returns
    /// is that loan's, with the map's V regions; `and_modify` gives the
    /// same Entry back, `insert_entry` an `OccupiedEntry` of the same
    /// loan and regions (so do the `Entry::Occupied` / `Entry::Vacant`
    /// payload reads, `EntryAsOccupied` / `EntryAsVacant`). A stored value (`or_insert`'s, `insert_entry`'s,
    /// and `OccupiedEntry::insert`'s argument) and a closure form's
    /// closure (all its regions) flow into V. The owned results of
    /// `OccupiedEntry::insert`, `remove`, and `remove_entry` carry the
    /// entry's K and V regions, not the loan. The keys' regions never
    /// reach the loan.
    fn call_hash_entry(&mut self, b: crate::check::Builtin, avs: &[(Ty, Vec<u32>)], dv: &[u32]) -> bool {
        use crate::check::Builtin as B;
        use crate::ty::hash::hash_parts;
        let Some((t0, v0)) = avs.first() else { return false };
        // The Entry (or, for `entry`, the map behind its `&mut`; for the
        // `&self` and `&mut self` methods of `OccupiedEntry`, the entry
        // behind the reference, whose loan is `self_r`) and its K, V.
        let by_ref = matches!(b, B::OccKey | B::OccGet | B::OccGetMut | B::OccInsert);
        let (entry_args, v0, self_r) = if b == B::MapEntry || by_ref {
            let TyKind::Ref(_, _, inner) = self.body.tys.kind(*t0) else { return false };
            let Some((&r0, rest)) = v0.split_first() else { return false };
            let inner_v = if b == B::MapEntry { &v0[..] } else { rest };
            (hash_parts(&self.body.tys, inner), inner_v, r0)
        } else {
            (hash_parts(&self.body.tys, *t0), &v0[..], 0)
        };
        let Some((_, ka)) = entry_args else { return false };
        let (Some(&kt), Some(&vt)) = (ka.first(), ka.get(1)) else { return false };
        let (nk, nv) = (self.sc.slots(kt) as usize, self.sc.slots(vt) as usize);
        let Some((&own, hv)) = v0.split_first() else { return false };
        if hv.len() < nk + nv {
            return false;
        }
        let (hk, hvv) = (hv[..nk].to_vec(), hv[nk..nk + nv].to_vec());
        // The owned results: `insert`'s old value, `remove`'s value, and
        // `remove_entry`'s pair carry the entry's K and V regions, never
        // its loan; `insert` stores its argument in V.
        match b {
            B::OccInsert | B::OccRemove => {
                if b == B::OccInsert
                    && let Some((t1, v1)) = avs.get(1)
                {
                    self.relate(*t1, v1, vt, &hvv, Variance::Co);
                }
                return dv.len() == nv && self.relate(vt, &hvv, vt, dv, Variance::Co);
            }
            // `VacantEntry::into_key`: the owned key, with the entry's K.
            B::VacIntoKey => {
                return dv.len() == nk && self.relate(kt, &hk, kt, dv, Variance::Co);
            }
            B::OccRemoveEntry => {
                return dv.len() == nk + nv && self.relate(kt, &hk, kt, &dv[..nk], Variance::Co) && self.relate(vt, &hvv, vt, &dv[nk..], Variance::Co);
            }
            // `&'r K` or `&'r (mut) V` from `&'r self`: the result borrows
            // that loan, and its K or V is the entry's (invariant: a write
            // through `get_mut` stores into the map).
            B::OccKey | B::OccGet | B::OccGetMut => {
                let Some((&x, rv)) = dv.split_first() else { return false };
                self.edge(self_r, x);
                let (t, slots) = if b == B::OccKey { (kt, &hk) } else { (vt, &hvv) };
                return rv.len() == slots.len() && self.relate(t, slots, t, rv, Variance::Inv);
            }
            _ => {}
        }
        let Some((&dst, rv)) = dv.split_first() else { return false };
        self.edge(own, dst);
        match b {
            B::MapEntry | B::EntryAndModify | B::EntryInsertEntry | B::EntryAsOccupied | B::EntryAsVacant => {
                if rv.len() < nk + nv {
                    return false;
                }
                let (rk, rvv) = (rv[..nk].to_vec(), rv[nk..nk + nv].to_vec());
                self.relate(kt, &hk, kt, &rk, Variance::Inv);
                self.relate(vt, &hvv, vt, &rvv, Variance::Inv);
                if b == B::MapEntry
                    && let Some((t1, v1)) = avs.get(1)
                {
                    self.relate(*t1, v1, kt, &rk, Variance::Co);
                }
                // `insert_entry` stores its value in V.
                if b == B::EntryInsertEntry
                    && let Some((t1, v1)) = avs.get(1)
                {
                    self.relate(*t1, v1, vt, &hvv, Variance::Co);
                }
            }
            _ => {
                if rv.len() < nv {
                    return false;
                }
                self.relate(vt, &hvv, vt, &rv[..nv], Variance::Inv);
                if let Some((t1, v1)) = avs.get(1) {
                    if b == B::EntryOrInsert || b == B::EntryInsert {
                        self.relate(*t1, v1, vt, &hvv, Variance::Co);
                    } else if b == B::EntryOrInsertWith && matches!(self.body.tys.kind(*t1), TyKind::Closure(..)) {
                        // `or_insert_with(|| ..)` stores what the closure
                        // returns, not every region it captures (ts-rust
                        // misc.rs `note_file_names`).
                        let mut srcs = Vec::new();
                        self.closure_sources(*t1, v1, &mut 0, &mut srcs);
                        self.flow_all(&srcs, &hvv);
                        self.store_flat(&srcs, vt, &hvv);
                    } else {
                        self.flow_all(v1, &hvv);
                        self.store_flat(v1, vt, &hvv);
                    }
                }
            }
        }
        if b == B::EntryAndModify
            && let Some((_, v1)) = avs.get(1)
        {
            self.flow_all(v1, &hvv);
            self.store_flat(v1, vt, &hvv);
        }
        true
    }

    /// `cow.to_mut()` (W-STD-B): `&'r mut Owned` from `&'x mut Cow<'a,
    /// B>`. The loan outlives the result, and the Owned value's regions
    /// are B's (one invariant class, as behind `&mut`). The Cow's own
    /// `'a` does not reach the result: after the call it is Owned and
    /// holds no borrow of `'a` data.
    fn call_cow_to_mut(&mut self, avs: &[(Ty, Vec<u32>)], dv: &[u32]) -> bool {
        let Some((_, v0)) = avs.first() else { return false };
        let (Some((&x, cv)), Some((&r, ov))) = (v0.split_first(), dv.split_first()) else { return false };
        let Some(b_slots) = cv.get(1..) else { return false };
        self.edge(x, r);
        let mut class = b_slots.to_vec();
        class.extend_from_slice(ov);
        self.equate_all(&class, &[]);
        true
    }

    /// `v.extend(iter)` with a builtin iterator: the items' regions
    /// outlive the elements' (`Extend<&T>` copies, so an item's leading
    /// borrow does not flow), at the element's variance (`store_slots`;
    /// fn pointer items through `store_into`); the iterator's own loans
    /// and a closure's captures reach the Vec only through the items.
    /// False (nothing added) for another argument or unknown item slots.
    fn call_vec_extend(&mut self, avs: &[(Ty, Vec<u32>)]) -> bool {
        let [(t0, v0), (it, iv)] = avs else { return false };
        let TyKind::Ref(_, Mut::Mut, vt) = self.body.tys.kind(*t0) else { return false };
        let Some(elem) = self.body.tys.vec_elem(vt) else { return false };
        let n = self.sc.slots(elem) as usize;
        let Some(ev) = v0.get(1..1 + n) else { return false };
        let ev = ev.to_vec();
        // Items a type param's bound fixes (`fixed_items`): the elements
        // equal them, whatever else this call reads off the iterator.
        let fixed = self.fixed_items(*it);
        if let Some(x) = &fixed {
            match x.len() {
                k if k == n => self.tie_fixed(x, &ev),
                k if k == n + 1 => self.tie_fixed(&x[1..], &ev),
                _ => {}
            }
        }
        if crate::ty::iter::iter_parts(&self.body.tys, *it).is_none() && fixed.is_none() {
            return false;
        }
        let Some(cands) = self.extend_items(*it, iv, fixed.is_some()) else { return false };
        let mut items = Vec::new();
        for c in cands {
            items.push(match c.len() {
                k if k == n => c,
                k if k == n + 1 => c[1..].to_vec(),
                _ => return false,
            });
        }
        if store::has_fn_ptr(&self.body.tys, vt) {
            self.store_into(*it, iv, vt, &v0[1..]);
        }
        for item_vars in items {
            self.flow_all(&item_vars, &ev);
            self.store_slots(&item_vars, vt, &ev);
        }
        true
    }

    /// The items an `extend` reads off iterator `it` (slots `iv`): its
    /// `item_slots`, or after fixed items (`fixed_items`) each side of a
    /// `chain` (`chain_sides`). None when neither names them.
    fn extend_items(&mut self, it: Ty, iv: &[u32], fixed: bool) -> Option<Vec<Vec<u32>>> {
        if let Some(x) = self.item_slots(it, iv) {
            return Some(vec![x]);
        }
        let mut out = Vec::new();
        (fixed && self.chain_sides(it, iv, &mut out)).then_some(out)
    }

    /// `table.extend(iter)` (W-STD-B): the items' regions outlive the
    /// table's element regions; the iterator's own loans do not reach
    /// the table unless an item holds them. False (nothing added) when
    /// the item's regions cannot be read off the iterator type.
    fn call_hash_extend(&mut self, avs: &[(Ty, Vec<u32>)]) -> bool {
        let [(t0, v0), (it, iv)] = avs else { return false };
        let TyKind::Ref(_, _, table) = self.body.tys.kind(*t0) else { return false };
        let Some((kind, targs)) = crate::ty::hash::hash_parts(&self.body.tys, table) else { return false };
        let parts = if kind == crate::ty::hash::HashTy::HashMap { 2 } else { 1 };
        let n: usize = targs.iter().take(parts).map(|&t| self.sc.slots(t) as usize).sum();
        let Some(ev) = v0.get(1..1 + n) else { return false };
        let ev = ev.to_vec();
        // Fn pointer items have no slots to flow: prove them (`store_into`).
        if store::has_fn_ptr(&self.body.tys, table) {
            self.store_into(*it, iv, table, &v0[1..]);
        }
        // Items a type param's bound fixes: the elements equal them.
        let fixed_items = self.fixed_items(*it);
        let fixed = fixed_items.is_some();
        if let Some(x) = fixed_items
            && (x.len() == n || x.len() == n + parts)
        {
            let x = self.strip_copied_borrows(x, &targs[..parts], n);
            self.tie_fixed(&x, &ev);
        }
        // A Vec, array, slice, map, or set argument: its elements' slots
        // lead its own (after the borrow for `&C`, whose items are copied).
        let tys = &self.body.tys;
        let container = |c: Ty| {
            tys.vec_elem(c).is_some()
                || matches!(tys.kind(c), TyKind::Array(..) | TyKind::Slice(_))
                || crate::ty::hash::hash_parts(tys, c).is_some()
        };
        let skip = match tys.kind(*it) {
            TyKind::Ref(_, _, c) if container(c) => Some(1),
            _ if container(*it) => Some(0),
            _ => None,
        };
        if let Some(skip) = skip {
            let Some(part) = iv.get(skip..skip + n) else { return false };
            let part = part.to_vec();
            self.flow_all(&part, &ev);
            self.store_slots(&part, table, &ev);
            return true;
        }
        let Some(cands) = self.extend_items(*it, iv, fixed) else { return false };
        for item_vars in cands {
            let item_vars = self.strip_copied_borrows(item_vars, &targs[..parts], n);
            self.flow_all(&item_vars, &ev);
            self.store_slots(&item_vars, table, &ev);
        }
        true
    }

    /// `Extend<&T>` and `Extend<(&K, &V)>` copy the parts in: an item with
    /// one more (leading) region per part (`n` element slots, part types
    /// `parts`) drops each borrow, which does not flow. Else the item as is.
    fn strip_copied_borrows(&mut self, item_vars: Vec<u32>, parts: &[Ty], n: usize) -> Vec<u32> {
        if item_vars.len() != n + parts.len() {
            return item_vars;
        }
        let mut out = Vec::new();
        let mut at = 0;
        for &t in parts {
            let k = self.sc.slots(t) as usize;
            out.extend_from_slice(&item_vars[at + 1..at + 1 + k]);
            at += 1 + k;
        }
        out
    }

    /// `Peekable::peek(&'r mut self) -> Option<&'r Item>`: the outer
    /// reference borrows the receiver; the item's slots are the
    /// iterator's item slots (`item_slots`), which the `&mut` of the call
    /// does not reach (a peeked `Ref` guard would else hold the iterator
    /// borrowed until its drop). False when the item slots are unknown.
    fn call_peek(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let Some((t0, v0)) = avs.first() else { return false };
        let TyKind::Ref(_, Mut::Mut, it) = self.body.tys.kind(*t0) else { return false };
        let Some((&r, iv)) = v0.split_first() else { return false };
        let Some(o) = self.body.tys.option_elem(dt) else { return false };
        let TyKind::Ref(_, Mut::Shared, item_ty) = self.body.tys.kind(o) else { return false };
        let Some((&p, rv)) = dv.split_first() else { return false };
        let Some(items) = self.item_slots(it, iv) else { return false };
        if items.len() != rv.len() {
            return false;
        }
        self.edge(r, p);
        self.relate(item_ty, &items, item_ty, rv, Variance::Co)
    }

    /// The region slots of an iterator type's item, read off the
    /// iterator's own slots (`vars`, in slot order), for the builtin
    /// kinds whose item is made of parts of the iterator type. None for
    /// the rest (`Chain` mixes two sources).
    /// The output vars `item` (type `bt`) of one call of an adapter's
    /// callable `f` (vars `fv`) on an item with vars `x`: a fn pointer by
    /// its late-bound signature, a `&dyn Fn` by its sugar signature, a
    /// plain fn item by its region signature. False when `f` is another
    /// callable or the signature does not pair (the caller's flow then).
    fn callable_out(&mut self, f: Ty, fv: &[u32], x: &[u32], bt: Ty, item: &[u32]) -> bool {
        match self.body.tys.kind(f) {
            TyKind::FnPtr(sig) => {
                let s = self.body.tys.sig(sig).value;
                let ins: Vec<Ty> = self.body.tys.tys_of(s.inputs).to_vec();
                let free = if s.free_slots != 0 { fv.first().map(|&v| (s.free_slots, v)) } else { None };
                let [it] = ins[..] else { return false };
                // Against its own output type: `filter_map`'s callable returns
                // `Option<B>`, which has `B`'s slots.
                let out = s.output;
                if (s.free_slots != 0 && free.is_none()) || self.sc.slots(it) as usize != x.len() || self.sc.slots(out) as usize != item.len() {
                    return false;
                }
                self.call_late_bound_free(&ins, out, free, &[(it, x.to_vec())], out, item)
            }
            TyKind::FnDef(def, fargs) if self.body.tys.args(fargs).is_empty() => {
                let Some(l) = self.p.local_def(def.hash) else { return false };
                let Callee::Sig(sig) = self.callee(l) else { return false };
                let params = self.p.fn_info(l).params.clone();
                let [pt] = params[..] else { return false };
                if self.p.tys.flags(pt).contains_param() || self.sc.slots(pt) as usize != x.len() {
                    return false;
                }
                self.call_sig(l, sig, &[(pt, x.to_vec())], bt, item)
            }
            // A `dyn Fn` behind references and boxes: the item's own type is
            // the input's erased form (its slots give each slot's variance).
            _ if let Some((ins, _)) = self.dyn_fn_sig(f) => {
                let [it] = ins[..] else { return false };
                let Some(at) = erased_lookup(&self.body.tys, it) else { return false };
                if self.sc.slots(at) as usize != x.len() {
                    return false;
                }
                self.call_dyn_fn(&[(f, fv.to_vec()), (at, x.to_vec())], bt, item)
            }
            // A reference to another callable calls what it points to.
            TyKind::Ref(_, _, inner) => match fv.get(1..) {
                Some(iv) => self.callable_out(inner, iv, x, bt, item),
                None => false,
            },
            _ => false,
        }
    }

    /// The items of this body's type param `t` (or of `<t as
    /// IntoIterator>::IntoIter`): `X` of its own `t: Iterator<Item = X>`
    /// bound (or `IntoIterator`, `DoubleEndedIterator`, `ExactSizeIterator`),
    /// as this body's vars (universal `'a` is var `a + 1`, `'static` var 0).
    /// None in a closure body, for another type, for two different bounds,
    /// or when `X` holds an elided region or a part with no slot reading.
    fn own_param_items(&mut self, t: Ty) -> Option<Vec<u32>> {
        let p = self.p;
        let lang = p.gx.lang;
        let j = match self.body.tys.kind(t) {
            TyKind::Param(j) => j,
            // `<I as IntoIterator>::IntoIter` yields `I`'s items.
            TyKind::Projection(d, a) if d.0 == lang.assoc_into_iter => match self.body.tys.args(a).first().and_then(|g| g.as_ty()).map(|x| self.body.tys.kind(x)) {
                Some(TyKind::Param(j)) => j,
                _ => return None,
            },
            _ => return None,
        };
        // A closure body reads its enclosing fn's bounds: that fn's
        // lifetimes are its `OwnSig::fn_lts` universals there.
        let sig = p.regions.own_body_sig(p, root_fn(p, self.body.fn_id))?;
        let iter_trait = |d: DefId| [lang.iterator, lang.into_iterator, lang.double_ended_iterator, lang.exact_size_iterator].contains(&d);
        let mut xs = sig.item_bounds.iter().filter(|b| b.0 == j.0 && iter_trait(b.1)).map(|b| b.2);
        let x = xs.next()?;
        if xs.any(|y| y != x) {
            return None;
        }
        let mut rs = Vec::new();
        regions_of(&p.tys, x, &mut rs);
        if rs.iter().any(|r| !matches!(r, Region::Static | Region::Param(_))) {
            return None;
        }
        let univ: Vec<u32> = if self.own.closure {
            let lts = &self.own.fn_lts;
            if rs.iter().any(|r| matches!(r, Region::Param(k) if lts.get(*k as usize).copied().flatten().is_none())) {
                return None;
            }
            (0..sig.n_univ as usize).map(|k| lts.get(k).copied().flatten().unwrap_or(0)).collect()
        } else {
            (1..=sig.n_univ).collect()
        };
        let mut ps = Vec::new();
        params_in(&p.tys, x, &mut ps);
        let binds: FxMap<u32, Vec<u32>> = ps.into_iter().map(|q| (q, Vec::new())).collect();
        let mut out = Vec::new();
        self.vars_from_binds(x, &univ, &binds, &mut out).then_some(out)
    }

    /// The item slots of iterator type `t` when trait matching fixes them:
    /// a type param of this body (`own_param_items`), `&mut` of one, or an
    /// adapter (also the `ByNext` wrapper) that passes such items on. They
    /// are this body's universals, so a sink that matches the items
    /// (`Extend<T>` for `Vec<T>`) makes its elements equal to them, though
    /// the adapters' own item slots only flow. None for a builtin source,
    /// whose items the call may shorten (its slots are covariant).
    fn fixed_items(&mut self, t: Ty) -> Option<Vec<u32>> {
        use crate::ty::iter::IterKind as K;
        match self.body.tys.kind(t) {
            TyKind::Param(_) | TyKind::Projection(..) => return self.own_param_items(t),
            TyKind::Ref(_, Mut::Mut, inner) => return self.fixed_items(inner),
            _ => {}
        }
        let (k, a) = crate::ty::iter::iter_parts(&self.body.tys, t)?;
        let &a0 = a.first()?;
        match k {
            K::ByNext | K::Filter | K::Rev | K::Take | K::Skip | K::TakeWhile | K::SkipWhile | K::StepBy | K::Peekable | K::Inspect | K::Enumerate => {
                self.fixed_items(a0)
            }
            K::Copied | K::Cloned => self.fixed_items(a0)?.get(1..).map(<[u32]>::to_vec),
            // `Chain<A, B>` needs `B::Item == A::Item`: either side's.
            K::Chain => self.fixed_items(a0).or_else(|| self.fixed_items(*a.get(1)?)),
            K::Zip => {
                let mut x = self.fixed_items(a0)?;
                x.extend(self.fixed_items(*a.get(1)?)?);
                Some(x)
            }
            _ => None,
        }
    }

    /// True for a builtin iterator type, `Chars`, or a type param of this
    /// body with its own `Item = X` bound (`own_param_items`).
    fn is_iter_ty(&mut self, t: Ty) -> bool {
        crate::ty::iter::iter_parts(&self.body.tys, t).is_some() || self.body.tys.is_chars_ty(t) || self.own_param_items(t).is_some()
    }

    /// Fixed items (`fixed_items`) and a sink's element slots, pairwise:
    /// equal, as the trait match makes them (rustc E0597 on a later
    /// shorter borrow into the sink). Also the two copies of an array
    /// `IntoIter`'s element slots.
    fn tie_fixed(&mut self, items: &[u32], elems: &[u32]) {
        for (&a, &b) in items.iter().zip(elems) {
            self.edge(a, b);
            self.edge(b, a);
        }
    }

    fn item_slots(&mut self, t: Ty, vars: &[u32]) -> Option<Vec<u32>> {
        use crate::ty::iter::IterKind as K;
        if self.body.tys.is_chars_ty(t) {
            return Some(Vec::new());
        }
        match self.body.tys.kind(t) {
            TyKind::Param(_) => return self.own_param_items(t),
            // `impl Iterator for &mut I`: `I`'s items (the reborrow's region
            // is not part of them).
            TyKind::Ref(_, Mut::Mut, inner) if self.is_iter_ty(inner) => return self.item_slots(inner, vars.get(1..)?),
            _ => {}
        }
        let (k, a) = crate::ty::iter::iter_parts(&self.body.tys, t)?;
        let mut at = adt_regions(self.p, &self.body.tys, t) as usize;
        let own: Vec<u32> = vars.get(..at)?.to_vec();
        let mut args: Vec<Vec<u32>> = Vec::new();
        for &x in &a {
            let n = self.sc.slots(x) as usize;
            args.push(vars.get(at..at + n)?.to_vec());
            at += n;
        }
        let cat = |parts: &[&[u32]]| parts.concat();
        Some(match k {
            K::SliceIter | K::SliceIterMut | K::Windows | K::OptionIter | K::OptionIterMut | K::ResultIter | K::ResultIterMut => {
                cat(&[&own, &args[0]])
            }
            // The chunk items are `&'a [T]` (or `&'a mut [T]`), like
            // a window; a `Utf8Chunk` item is its one region.
            K::Chunks | K::ChunksMut | K::ChunksExact | K::ChunksExactMut => cat(&[&own, &args[0]]),
            // A slice split's item is `&'a [T]` (or `&'a mut [T]`), like a chunk.
            K::SliceSplit | K::SliceSplitMut | K::ChunkBy | K::ChunkByMut => cat(&[&own, &args[0]]),
            K::Utf8Chunks => own.clone(),
            K::Utf8Chunk => return None,
            K::VecIntoIter | K::Range | K::RangeInclusive | K::RangeFrom | K::VecDrain => args[0].clone(),
            // A `map` with no closure: what `iter_items` reads (above B).
            K::Map | K::FilterMap | K::MapWhile if !matches!(a.get(1).map(|&f| self.body.tys.kind(f)), Some(TyKind::Closure(..))) => {
                let mut xs = Vec::new();
                if !self.iter_items(t, vars, &mut xs) {
                    return None;
                }
                xs.into_iter().next()?
            }
            K::Map | K::FilterMap | K::MapWhile | K::TryCollect => args[2].clone(),
            K::Copied | K::Cloned => args[1].clone(),
            K::Filter | K::Rev | K::Take | K::Skip | K::TakeWhile | K::SkipWhile | K::StepBy | K::Peekable | K::Inspect | K::Enumerate => {
                self.item_slots(a[0], &args[0])?
            }
            K::Zip => {
                let x = self.item_slots(a[0], &args[0])?;
                let y = self.item_slots(a[1], &args[1])?;
                cat(&[&x, &y])
            }
            K::Chain => return None,
            K::MapIter | K::MapIterMut => cat(&[&own, &args[0], &own, &args[1]]),
            K::MapKeys | K::SetIter => cat(&[&own, &args[0]]),
            K::MapValues | K::MapValuesMut => cat(&[&own, &args[1]]),
            K::MapIntoIter | K::MapDrain => cat(&[&args[0], &args[1]]),
            K::MapIntoKeys | K::SetIntoIter | K::SetDrain | K::RepeatN => args[0].clone(),
            K::ArrayIntoIter => {
                self.tie_fixed(&args[0], &args[1]);
                args[0].clone()
            }
            K::MapIntoValues | K::ByNext => args[1].clone(),
            // (usize, char): no regions.
            K::CharIndices | K::StringDrain | K::Args => Vec::new(),
            // Range kinds that are `RangeBounds` values here, not iterators.
            K::RangeTo | K::RangeFull | K::RangeToInclusive => return None,
            // `flat_map`'s front and back iterators hold what its map holds
            // (`call_flat_map`); a plain `flatten`'s are not tied to the
            // outer iterator, so its items are not known here.
            K::Flatten if matches!(crate::ty::iter::iter_parts(&self.body.tys, a[0]), Some((K::Map, _))) => self.item_slots(a[1], &args[1])?,
            K::Flatten => return None,
            K::OptionIntoIter | K::ResultIntoIter => args[0].clone(),
            // `&'a str` of the haystack (W-STD-B); the matches forms
            // yield it too, with a plain `usize` for the indices forms.
            K::StrSplit | K::StrMatches => own,
            // `u16` items: no regions (tf-str).
            K::EncodeUtf16 => Vec::new(),
            // An mpsc receiver's items are its `T` values (W-THREADS).
            K::RecvIter | K::RecvTryIter | K::RecvIntoIter => args[0].clone(),
        })
    }

    /// Splits an iterator argument's slots (in `non_closure_slots`
    /// order) into the loan regions of the builtin iterator structs in
    /// it (their `adt_regions` slots) and the element regions (every
    /// other slot). Closures are skipped.
    fn iter_slot_split(&mut self, t: Ty, vars: &[u32], at: &mut usize, loans: &mut Vec<u32>, elems: &mut Vec<u32>) {
        let TyKind::Adt(_, args) = self.body.tys.kind(t) else {
            return self.non_closure_slots(t, vars, at, elems);
        };
        if !crate::ty::iter::is_iter(&self.body.tys, t) {
            return self.non_closure_slots(t, vars, at, elems);
        }
        for _ in 0..adt_regions(self.p, &self.body.tys, t) {
            if let Some(&v) = vars.get(*at) {
                loans.push(v);
            }
            *at += 1;
        }
        for g in self.body.tys.args(args).to_vec() {
            if let GenericArg::Ty(e) = g {
                self.iter_slot_split(e, vars, at, loans, elems);
            }
        }
    }

    /// Splits a result type's slots into its top-level reference regions
    /// (references reached through tuples, arrays, and Adt args without
    /// passing another reference, and builtin structs' own regions) and
    /// the rest.
    fn item_slot_split(&mut self, t: Ty, vars: &[u32], at: &mut usize, tops: &mut Vec<u32>, rest: &mut Vec<u32>) {
        let take = |at: &mut usize, n: usize, out: &mut Vec<u32>| {
            out.extend(vars.iter().skip(*at).take(n).copied());
            *at += n;
        };
        match self.body.tys.kind(t) {
            TyKind::Ref(_, _, inner) => {
                take(at, 1, tops);
                let n = self.sc.slots(inner) as usize;
                take(at, n, rest);
            }
            TyKind::Adt(_, args) => {
                let n = adt_regions(self.p, &self.body.tys, t) as usize;
                take(at, n, tops);
                for g in self.body.tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.item_slot_split(e, vars, at, tops, rest);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in self.body.tys.tys_of(ts).to_vec() {
                    self.item_slot_split(e, vars, at, tops, rest);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) => self.item_slot_split(e, vars, at, tops, rest),
            _ => {
                let n = self.sc.slots(t) as usize;
                take(at, n, rest);
            }
        }
    }

    /// The argument slot vars of a closure with free arguments, made at
    /// its creation with the contract edges between them and the
    /// closure's captured slots (`caps`, roles `roles`; not when
    /// `contract` is false: the creator adds the body's requirements).
    /// None for a closure whose arguments are higher-ranked.
    fn make_arg_vars(&mut self, def: DefId, roles: &[(bool, bool)], caps: &[u32], contract: bool) -> Option<Vec<u32>> {
        if let Some(v) = self.closure_args.get(&def) {
            return Some(v.clone());
        }
        let c = self.p.gx.closures.get(&def)?;
        let slots = match closure_arg_slots(&mut self.sc, c) {
            Ok(s) => s,
            Err(()) => {
                self.errs.push(Diag::new(
                    "L0203",
                    self.span,
                    "an explicit lifetime in this closure parameter's annotation is not supported yet",
                    "Drop the lifetime from the annotation, or write `'_`.",
                ));
                return None;
            }
        };
        if slots.iter().all(|(r, _)| r.is_none()) {
            return None;
        }
        let arg_roles: Vec<Option<(bool, bool)>> = slots.iter().map(|&(r, _)| r).collect();
        let vars: Vec<u32> = arg_roles.iter().map(|_| self.fresh()).collect();
        // A slot the annotation names is that region of the creator; only
        // the creating body has those universals (another body that calls
        // the closure, an instance of a generic callee, ties nothing).
        let creator = c.parent == self.body.fn_id
            || self.p.gx.instances.get(&self.body.fn_id).and_then(|i| i.template_local) == Some(c.parent);
        for (i, &(_, link)) in slots.iter().enumerate() {
            let u = match link {
                Some(Region::Static) => Some(0),
                Some(Region::Param(k)) if creator && !self.own.closure && k < self.own.n_univ => Some(k + 1),
                // A generic callee's instance: the bound took this input from
                // a type param (check rejects a higher-ranked one), so the
                // creator's call already tied what flows in.
                Some(Region::Param(_)) if !creator && !self.own.closure => None,
                Some(_) => {
                    self.errs.push(Diag::new(
                        "L0203",
                        self.span,
                        "a named lifetime in a closure parameter inside a closure is not supported yet",
                        "Move the closure out of the enclosing closure, or drop the lifetime.",
                    ));
                    None
                }
                None => None,
            };
            if let Some(u) = u {
                self.edge(vars[i], u);
                self.edge(u, vars[i]);
            }
        }
        let mut srcs: Vec<u32> = Vec::new();
        let mut snks: Vec<u32> = Vec::new();
        for (i, r) in arg_roles.iter().enumerate() {
            if let Some((src, snk)) = r {
                if *src {
                    srcs.push(vars[i]);
                }
                if *snk {
                    snks.push(vars[i]);
                }
            }
        }
        let mut cap_srcs: Vec<u32> = Vec::new();
        let mut cap_snks: Vec<u32> = Vec::new();
        for (i, &(src, snk)) in roles.iter().enumerate() {
            if let Some(&v) = caps.get(i) {
                if src {
                    cap_srcs.push(v);
                }
                if snk {
                    cap_snks.push(v);
                }
            }
        }
        // Argument sources into the captured sinks, captured sources into
        // the argument sinks (capture-to-capture is `contract_edges`'; an
        // argument does not flow into an argument's `&mut` target). The
        // output is the call's: `closure_sources` covers it. Not when the
        // creator adds the body's requirements instead.
        if !contract {
            self.closure_args.insert(def, vars.clone());
            return Some(vars);
        }
        for &a in &srcs {
            for &b in &cap_snks {
                self.edge(a, b);
            }
        }
        for &a in &cap_srcs {
            for &b in &snks {
                self.edge(a, b);
            }
        }
        self.closure_args.insert(def, vars.clone());
        Some(vars)
    }

    /// A builtin taking a closure with free arguments (an iterator
    /// method): an input that is the receiver's item (or `&item`, whose
    /// outer reference is higher-ranked) takes exactly the item's regions
    /// (`iter_items`); any other free argument slot (`fold`'s accumulator,
    /// an item the receiver cannot name, `b` None for a generic fn that did
    /// not pair) may hold any region of the call's other arguments, and a
    /// sink slot writes back into them. Closures in `skip` are linked
    /// already (`link_bound_closure`).
    fn link_closure_args(&mut self, avs: &[(Ty, Vec<u32>)], b: Option<crate::check::Builtin>, skip: &[DefId]) {
        let mut cands: Vec<Vec<u32>> = Vec::new();
        if b.is_some()
            && let Some((t0, v0)) = avs.first()
        {
            let (it, iv) = match self.body.tys.kind(*t0) {
                TyKind::Ref(_, _, inner) if !v0.is_empty() => (inner, v0[1..].to_vec()),
                _ => (*t0, v0.clone()),
            };
            if !self.iter_items(it, &iv, &mut cands) {
                cands.clear();
            }
        }
        for (k, (t, v)) in avs.iter().enumerate() {
            let TyKind::Closure(def, args) = self.body.tys.kind(*t) else { continue };
            if skip.contains(&def) {
                continue;
            }
            let Some(c) = self.p.gx.closures.get(&def) else { continue };
            let Ok(slots) = closure_arg_slots(&mut self.sc, c) else { continue };
            let inputs = c.inputs.clone();
            let c_output = c.output;
            let mut roles = Vec::new();
            closure_roles(&mut self.sc, def, args, &mut roles);
            let Some(vars) = self.closure_arg_vars(def, &roles, v) else { continue };
            let arg_roles: Vec<Option<(bool, bool)>> = slots.into_iter().map(|(r, _)| r).collect();
            let mut items: Vec<u32> = Vec::new();
            let mut elems: Vec<u32> = Vec::new();
            for (j, (ot, ov)) in avs.iter().enumerate() {
                if j != k {
                    self.non_closure_slots(*ot, ov, &mut 0, &mut items);
                    self.elem_slots(*ot, ov, &mut 0, &mut elems);
                    self.closure_sources(*ot, ov, &mut 0, &mut elems);
                }
            }
            let mut at = 0usize;
            for (pi, &pt) in inputs.iter().enumerate() {
                let n = self.sc.slots(pt) as usize;
                let range = at..(at + n).min(vars.len());
                at += n;
                // `filter(|x| ..)` takes `&Self::Item`: the method's own
                // borrow, higher-ranked in its bound.
                if k > 0 && by_ref_item(b) && n > 0 && arg_roles.get(range.start).is_some_and(|r| r.is_some()) {
                    self.not_general_enough();
                    continue;
                }
                // `fold`'s accumulator: the initial value, then what the
                // body returns (`closure_reqs`), round after round. A
                // `try_fold` body returns it as the leading slots of its
                // `Option` or `Result`.
                let folds = matches!(b, Some(crate::check::Builtin::IterFold | crate::check::Builtin::IterTryFold));
                let fe = self.fn_ends(def);
                if k == 2
                    && pi == 0
                    && folds
                    && let Some((it0, iv0)) = avs.get(1)
                    && (self.sc.slots(c_output) as usize == n || b == Some(crate::check::Builtin::IterTryFold) && self.sc.slots(c_output) as usize >= n)
                    && let Some(reqs) = self.closure_reqs(def, &roles)
                {
                    let pv: Vec<u32> = vars.get(range.clone()).map(<[u32]>::to_vec).unwrap_or_default();
                    // A constant initial value (`""`) holds no loan.
                    if pv.len() == n && (iv0.is_empty() || self.relate(*it0, iv0, pt, &pv, Variance::Co)) {
                        for &(x, y) in reqs.iter() {
                            let End::Out(q) = y else { continue };
                            let from = match x {
                                End::Cap(i) => v.get(i as usize).copied(),
                                End::Arg(j) => vars.get(j as usize).copied(),
                                End::Fn(k) => fe.get(k as usize).copied().flatten(),
                                End::Static | End::Out(_) => None,
                            };
                            if let (Some(from), Some(&a)) = (from, pv.get(q as usize)) {
                                self.edge(from, a);
                            }
                        }
                        continue;
                    }
                }
                let item_param = k > 0 && !cands.is_empty() && !(folds && pi == 0);
                if item_param {
                    let want = cands[0].len();
                    let (ity, skip) = match self.body.tys.kind(pt) {
                        TyKind::Ref(_, _, inner) if n == want + 1 && arg_roles.get(range.start).is_some_and(|r| r.is_none()) => (inner, 1),
                        _ => (pt, 0),
                    };
                    let pv: Vec<u32> = vars.get(range.start + skip..range.end).map(<[u32]>::to_vec).unwrap_or_default();
                    if pv.len() + skip == n && cands.iter().all(|c| c.len() == pv.len()) {
                        for c in cands.clone() {
                            self.relate(ity, &c, ity, &pv, Variance::Co);
                        }
                        continue;
                    }
                }
                for i in range {
                    let (Some((_, snk)), Some(&a)) = (arg_roles.get(i).copied().flatten(), vars.get(i)) else { continue };
                    if snk {
                        // Behind an item's `&mut`: the source's element regions
                        // (invariant), never the iterator's own borrow.
                        for &s in &elems {
                            self.edge(s, a);
                            self.edge(a, s);
                        }
                    } else {
                        for &s in &items {
                            self.edge(s, a);
                        }
                    }
                }
            }
        }
    }

    /// The item slots of builtin iterator type `t` (its slot vars `vars`),
    /// one candidate per source of items (`chain` has two): Rust's
    /// `Iterator::Item` of `slice::Iter<'a, T>` is `&'a T`, an adapter's
    /// is its inner iterator's, `copied`'s drops the outer reference, a
    /// `map` closure's is what its body returns (`closure_reqs`). False
    /// when the layout does not pair or the closure's body does not solve.
    fn iter_items(&mut self, t: Ty, vars: &[u32], out: &mut Vec<Vec<u32>>) -> bool {
        use crate::ty::iter::IterKind as K;
        if matches!(self.body.tys.builtin_of(t), Some(BuiltinTy::Chars)) {
            out.push(Vec::new());
            return true;
        }
        let Some((k, a)) = crate::ty::iter::iter_parts(&self.body.tys, t) else {
            // A type param of this body: its own `Item = X` bound.
            if let Some(item) = self.own_param_items(t) {
                out.push(item);
                return true;
            }
            // `&mut I` over a type param or a builtin iterator: `I`'s items.
            if let TyKind::Ref(_, Mut::Mut, inner) = self.body.tys.kind(t)
                && self.is_iter_ty(inner)
            {
                return vars.get(1..).is_some_and(|v| self.iter_items(inner, v, out));
            }
            // A library or user iterator type: its `next` signature.
            return match self.next_sig_item(t, vars) {
                Some(item) => {
                    out.push(item);
                    true
                }
                None => false,
            };
        };
        // `string::Drain` yields owned `char`s, like `Chars`.
        if k == K::StringDrain {
            out.push(Vec::new());
            return true;
        }
        let Some(&a0) = a.first() else { return false };
        let n0 = self.sc.slots(a0) as usize;
        match k {
            // The item `&'a T` is the iterator's own slots, in order.
            K::SliceIter | K::SliceIterMut | K::OptionIter | K::OptionIterMut | K::ResultIter | K::ResultIterMut => {
                if vars.len() != 1 + n0 {
                    return false;
                }
                out.push(vars.to_vec());
                true
            }
            // `mpsc::Iter<'a, T>` holds `&'a Receiver<T>`: its own region,
            // then `T`'s slots; `IntoIter<T>` holds the receiver.
            K::RecvIter | K::RecvTryIter => match vars.get(1..1 + n0) {
                Some(v) => {
                    out.push(v.to_vec());
                    true
                }
                None => false,
            },
            // `array::IntoIter<E, [E; N]>` names `E` twice; both are the one
            // `E` of std's `IntoIter<E, N>` (the loan goes into the array's).
            K::ArrayIntoIter => match (vars.get(..n0), vars.get(n0..2 * n0)) {
                (Some(e), Some(arr)) => {
                    let (e, arr) = (e.to_vec(), arr.to_vec());
                    self.tie_fixed(&e, &arr);
                    out.push(e);
                    true
                }
                _ => false,
            },
            K::VecIntoIter | K::Range | K::RangeInclusive | K::RangeFrom | K::RecvIntoIter => match vars.get(..n0) {
                Some(v) => {
                    out.push(v.to_vec());
                    true
                }
                None => false,
            },
            // The item `T` is owned; the drain's own region slot (its
            // borrow of the Vec) comes first and is not part of it.
            K::VecDrain => match vars.get(1..1 + n0) {
                Some(v) => {
                    out.push(v.to_vec());
                    true
                }
                None => false,
            },
            K::StringDrain | K::RangeTo | K::RangeFull | K::RangeToInclusive | K::Utf8Chunk | K::Args => false,
            K::Filter | K::Rev | K::Take | K::Skip | K::TakeWhile | K::SkipWhile | K::StepBy | K::Peekable | K::Inspect | K::Enumerate => {
                vars.get(..n0).is_some_and(|v| self.iter_items(a0, v, out))
            }
            K::Chain => {
                let Some(&a1) = a.get(1) else { return false };
                let n1 = self.sc.slots(a1) as usize;
                vars.get(..n0).is_some_and(|v| self.iter_items(a0, v, out))
                    && vars.get(n0..n0 + n1).is_some_and(|v| self.iter_items(a1, v, out))
            }
            K::Zip => {
                let Some(&a1) = a.get(1) else { return false };
                let n1 = self.sc.slots(a1) as usize;
                let (mut xs, mut ys) = (Vec::new(), Vec::new());
                if !(vars.get(..n0).is_some_and(|v| self.iter_items(a0, v, &mut xs))
                    && vars.get(n0..n0 + n1).is_some_and(|v| self.iter_items(a1, v, &mut ys)))
                {
                    return false;
                }
                for x in &xs {
                    for y in &ys {
                        out.push(x.iter().chain(y).copied().collect());
                    }
                }
                true
            }
            K::Copied | K::Cloned => {
                let mut xs = Vec::new();
                if !vars.get(..n0).is_some_and(|v| self.iter_items(a0, v, &mut xs)) || xs.iter().any(|x| x.is_empty()) {
                    return false;
                }
                out.extend(xs.into_iter().map(|x| x[1..].to_vec()));
                true
            }
            // The try wrapper's item is the value inside the inner
            // item (`Result<T, E>` or `Option<T>`): the first of its
            // slots, in the wrapper type's own arg order (F3).
            K::TryCollect => {
                let Some(&bt) = a.get(2) else { return false };
                let nb = self.sc.slots(bt) as usize;
                let mut xs = Vec::new();
                if !vars.get(..n0).is_some_and(|v| self.iter_items(a0, v, &mut xs)) || xs.iter().any(|x| x.len() < nb) {
                    return false;
                }
                out.extend(xs.into_iter().map(|x| x[..nb].to_vec()));
                true
            }
            // The closure's output (`FilterMap`'s `Option<B>` has `B`'s
            // slots): what its body returns of its captured slots (laid
            // out after the inner iterator's) and its free arguments.
            K::Map | K::FilterMap | K::MapWhile => {
                let (Some(&f), Some(&bt)) = (a.get(1), a.get(2)) else { return false };
                // A fn pointer, a `&dyn Fn`, or a fn item: its output through
                // its signature, for each item it takes (`callable_out`).
                if !matches!(self.body.tys.kind(f), TyKind::Closure(..)) {
                    let nf = self.sc.slots(f) as usize;
                    let nb = self.sc.slots(bt) as usize;
                    let Some(fv) = vars.get(n0..n0 + nf).map(<[u32]>::to_vec) else { return false };
                    let mut xs = Vec::new();
                    if !vars.get(..n0).is_some_and(|v| self.iter_items(a0, v, &mut xs)) {
                        return false;
                    }
                    let mut items = Vec::with_capacity(xs.len());
                    for x in xs {
                        let item: Vec<u32> = (0..nb).map(|_| self.fresh()).collect();
                        if !self.callable_out(f, &fv, &x, bt, &item) {
                            // A fn pointer whose erased signature does not
                            // pair (a library field type: `fn(&(K, V)) -> &K`
                            // at `K = &str`) keeps its callers' rule. Any
                            // other callable: the output may hold any region
                            // of the item and of the callable.
                            if matches!(self.body.tys.kind(f), TyKind::FnPtr(_)) {
                                return false;
                            }
                            let srcs: Vec<u32> = x.iter().chain(&fv).copied().collect();
                            self.flow_all(&srcs, &item);
                        }
                        items.push(item);
                    }
                    out.extend(items);
                    return true;
                }
                let TyKind::Closure(def, cargs) = self.body.tys.kind(f) else { return false };
                let nf = self.sc.slots(f) as usize;
                let nb = self.sc.slots(bt) as usize;
                let Some(caps) = vars.get(n0..n0 + nf).map(<[u32]>::to_vec) else { return false };
                // A closure made in another body (a revealed `impl
                // Iterator` value): its argument vars are not this body's,
                // so the items are the value's own `B` slots.
                if !self.closure_args.contains_key(&def) {
                    return match vars.get(n0 + nf..n0 + nf + nb) {
                        Some(v) => {
                            out.push(v.to_vec());
                            true
                        }
                        None => false,
                    };
                }
                let mut roles = Vec::new();
                closure_roles(&mut self.sc, def, cargs, &mut roles);
                let fe = self.fn_ends(def);
                let Some(reqs) = self.closure_reqs(def, &roles) else { return false };
                let args = self.closure_args.get(&def).cloned().unwrap_or_default();
                let item: Vec<u32> = (0..nb).map(|_| self.fresh()).collect();
                for &(x, y) in reqs.iter() {
                    let End::Out(k) = y else { continue };
                    let from = match x {
                        End::Static => Some(0),
                        End::Cap(i) => caps.get(i as usize).copied(),
                        End::Arg(j) => args.get(j as usize).copied(),
                        End::Fn(k) => fe.get(k as usize).copied().flatten(),
                        End::Out(_) => None,
                    };
                    if let (Some(from), Some(&o)) = (from, item.get(k as usize)) {
                        self.edge(from, o);
                    }
                }
                out.push(item);
                true
            }
            // A user iterator through its `next` (W-STD-B): the item's own
            // slots, which its construction ties to the iterator's.
            K::ByNext => {
                let Some(&a1) = a.get(1) else { return false };
                let own = adt_regions(self.p, &self.body.tys, t) as usize;
                let n1 = self.sc.slots(a1) as usize;
                match vars.get(own + n0..own + n0 + n1) {
                    Some(v) => {
                        out.push(v.to_vec());
                        true
                    }
                    None => false,
                }
            }
            // A str split's item is `&'a str` of its haystack: the own
            // region (W-STD-B). The matches forms are the same
            // (tf-str).
            K::StrSplit | K::StrMatches => match vars.first() {
                Some(&r) => {
                    out.push(vec![r]);
                    true
                }
                None => false,
            },
            // The hash iterators: `item_slots` names their items (`&'a V`
            // is the map loan and the map's V; `(K, V)` by value is the
            // map's K and V).
            K::MapIter
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
            | K::SetDrain => match self.item_slots(t, vars) {
                Some(v) => {
                    out.push(v);
                    true
                }
                None => false,
            },
            // The other W-STD-B kinds (repeat_n, Windows, CharIndices,
            // Flatten, option::IntoIter): the conservative item rule.
            K::RepeatN
            | K::Windows
            | K::Chunks
            | K::ChunksMut
            | K::ChunksExact
            | K::ChunksExactMut
            | K::Utf8Chunks
            | K::CharIndices
            | K::Flatten
            | K::OptionIntoIter
            | K::EncodeUtf16
            | K::ResultIntoIter
            | K::SliceSplit
            | K::SliceSplitMut
            | K::ChunkBy
            | K::ChunkByMut => false,
        }
    }

    /// An item call (`next`, `find`, `last`, `min`, `collect` into a `Vec`)
    /// over a receiver whose items `iter_items` names: the result's item
    /// takes exactly their regions, nothing of the iterator's own borrow
    /// beyond what the item holds. False (nothing added) otherwise.
    fn call_item(&mut self, b: crate::check::Builtin, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        if matches!(b, crate::check::Builtin::IterFindMap) {
            return false;
        }
        let Some((t0, v0)) = avs.first() else { return false };
        let (it, iv) = match self.body.tys.kind(*t0) {
            TyKind::Ref(_, _, inner) if !v0.is_empty() => (inner, v0[1..].to_vec()),
            _ => (*t0, v0.clone()),
        };
        use crate::ty::hash::HashTy;
        // The result's parts that hold the item: `Option<T>` and `Vec<T>`
        // hold `T`; a map or set from `collect` (W-STD-B) holds `(K, V)` or
        // `T`, and its hasher's slots (after them) are its own.
        if adt_regions(self.p, &self.body.tys, dt) != 0 {
            return false;
        }
        let Some((_, args)) = self.body.tys.adt_parts(dt) else { return false };
        let comps: Vec<Ty> = self.body.tys.args(args).iter().filter_map(|g| g.as_ty()).collect();
        let collect = matches!(b, crate::check::Builtin::IterCollect | crate::check::Builtin::FromIter);
        // A try collect result (`Result<C, E>` or `Option<C>`, F3)
        // holds the item inside `C` plus, for `Result`, the error:
        // its parts are `C`'s own item parts then `E`, which is
        // also the item's slot order (`Result<T, E>`), when `C`
        // has no further slotted args after its item parts.
        let coll_parts = |this: &mut Self, c: Ty| -> Option<Vec<Ty>> {
            let (_, cargs) = this.body.tys.adt_parts(c)?;
            let ccomps: Vec<Ty> = this.body.tys.args(cargs).iter().filter_map(|g| g.as_ty()).collect();
            let p = match (this.body.tys.builtin_of(c), &ccomps[..]) {
                (Some(BuiltinTy::Vec), &[t]) => vec![t],
                (Some(BuiltinTy::Hash(HashTy::HashMap)), &[k, v, _]) => vec![k, v],
                (Some(BuiltinTy::Hash(HashTy::HashSet)), &[t, _]) => vec![t],
                (Some(BuiltinTy::Boxed), &[s]) => match this.body.tys.kind(s) {
                    TyKind::Slice(e) => vec![e],
                    _ => return None,
                },
                _ => return None,
            };
            let mut total = 0usize;
            for &t in &p {
                total += this.sc.slots(t) as usize;
            }
            (total == this.sc.slots(c) as usize).then_some(p)
        };
        let parts = match (self.body.tys.builtin_of(dt), &comps[..]) {
            (Some(BuiltinTy::Result), &[c, e]) if collect => match coll_parts(self, c) {
                Some(mut p) => {
                    p.push(e);
                    p
                }
                None => return false,
            },
            (Some(BuiltinTy::Option), &[c]) if collect => match coll_parts(self, c) {
                Some(p) => p,
                None => return false,
            },
            (Some(BuiltinTy::Option | BuiltinTy::Vec), &[t]) => vec![t],
            // A `sum` into `Result<S, E>` holds the items' error.
            (Some(BuiltinTy::Result), &[s, e]) if matches!(b, crate::check::Builtin::IterSum | crate::check::Builtin::IterProduct) => vec![s, e],
            (Some(BuiltinTy::Hash(HashTy::HashMap)), &[k, v, _]) if collect => vec![k, v],
            (Some(BuiltinTy::Hash(HashTy::HashSet)), &[t, _]) if collect => vec![t],
            _ => return false,
        };
        let n: usize = parts.iter().map(|&t| self.sc.slots(t) as usize).sum();
        let Some(dv) = dv.get(..n) else { return false };
        // `Type::from_iter(src)` (fx-fromiter): a `&Vec`/`&[T]`/`&[T; N]`
        // source is a slice iterator whose item `&T` is the source's own
        // slots (the borrow region first, then `T`'s); a `Vec` source is
        // `vec::IntoIter`, whose item `T` is the Vec's element slots.
        let src_cand: Option<Vec<u32>> = if b == crate::check::Builtin::FromIter {
            match self.body.tys.kind(*t0) {
                TyKind::Ref(_, _, inner) => {
                    let el = match self.body.tys.kind(inner) {
                        TyKind::Slice(e) | TyKind::Array(e, _) => Some(e),
                        _ => self.body.tys.vec_elem(inner),
                    };
                    el.and_then(|e| (v0.len() == 1 + self.sc.slots(e) as usize).then(|| v0.clone()))
                }
                _ => self
                    .body
                    .tys
                    .vec_elem(*t0)
                    .and_then(|e| v0.get(..self.sc.slots(e) as usize).map(|v| v.to_vec())),
            }
        } else {
            None
        };
        let mut cands = Vec::new();
        match src_cand {
            Some(c) if c.len() == n => cands.push(c),
            _ if !self.iter_items(it, &iv, &mut cands) || cands.is_empty() || cands.iter().any(|c| c.len() != n) => {
                return false;
            }
            _ => {}
        }
        for c in cands {
            let mut at = 0;
            for &t in &parts {
                let k = self.sc.slots(t) as usize;
                self.relate(t, &c[at..at + k], t, &dv[at..at + k], Variance::Co);
                at += k;
            }
        }
        true
    }

    /// `non_closure_slots` without the Adts' own region slots (an
    /// iterator's borrow of its source): the regions of the elements.
    fn elem_slots(&mut self, t: Ty, vars: &[u32], at: &mut usize, out: &mut Vec<u32>) {
        let n = self.sc.slots(t) as usize;
        match self.body.tys.kind(t) {
            TyKind::Closure(..) => *at += n,
            TyKind::Ref(_, _, inner) => {
                if let Some(&v) = vars.get(*at) {
                    out.push(v);
                }
                *at += 1;
                self.elem_slots(inner, vars, at, out);
            }
            TyKind::Adt(_, args) => {
                *at += adt_regions(self.p, &self.body.tys, t) as usize;
                for g in self.body.tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.elem_slots(e, vars, at, out);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in self.body.tys.tys_of(ts).to_vec() {
                    self.elem_slots(e, vars, at, out);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.elem_slots(e, vars, at, out),
            _ => {
                out.extend(vars.iter().skip(*at).take(n).copied());
                *at += n;
            }
        }
    }

    /// The closure contract over a closure value's slot vars: every
    /// source outlives every other sink.
    fn contract_edges(&mut self, roles: &[(bool, bool)], vars: &[u32]) {
        for (i, &(src, _)) in roles.iter().enumerate() {
            for (j, &(_, snk)) in roles.iter().enumerate() {
                if src && snk && i != j
                    && let (Some(&a), Some(&b)) = (vars.get(i), vars.get(j))
                {
                    self.edge(a, b);
                }
            }
        }
    }

    /// Whether closure `def` returns a value with regions (W-BORROW: its
    /// body's output may hold its captured sources).
    fn closure_returns_regions(&mut self, def: DefId) -> bool {
        match self.p.gx.closures.get(&def) {
            Some(c) => self.sc.slots(c.output) > 0,
            None => true,
        }
    }

    /// Adds the captured sources of each closure inside `t` (laid out from
    /// `*at` in `vars`) whose output has regions to `out`.
    fn closure_sources(&mut self, t: Ty, vars: &[u32], at: &mut usize, out: &mut Vec<u32>) {
        let n = self.sc.slots(t) as usize;
        match self.body.tys.kind(t) {
            TyKind::Closure(def, args) => {
                if self.closure_returns_regions(def) {
                    let mut roles = Vec::new();
                    closure_roles(&mut self.sc, def, args, &mut roles);
                    let av = self.closure_args.get(&def).cloned().unwrap_or_default();
                    let fe = self.fn_ends(def);
                    match self.closure_reqs(def, &roles) {
                        // What its body returns (`closure_reqs`).
                        Some(reqs) => {
                            for &(x, y) in reqs.iter() {
                                if !matches!(y, End::Out(_)) {
                                    continue;
                                }
                                let v = match x {
                                    End::Cap(i) => vars.get(*at + i as usize).copied(),
                                    End::Arg(j) => av.get(j as usize).copied(),
                                    End::Fn(k) => fe.get(k as usize).copied().flatten(),
                                    End::Static | End::Out(_) => None,
                                };
                                out.extend(v);
                            }
                        }
                        // Every captured source, and its free argument
                        // regions: the output may borrow from an argument
                        // (`opt.map(|e| &e.1)`).
                        None => {
                            for (i, &(src, _)) in roles.iter().enumerate() {
                                if src && let Some(&v) = vars.get(*at + i) {
                                    out.push(v);
                                }
                            }
                            out.extend(av);
                        }
                    }
                }
                *at += n;
            }
            TyKind::Ref(_, _, inner) => {
                *at += 1;
                self.closure_sources(inner, vars, at, out);
            }
            TyKind::Adt(_, args) => {
                *at += adt_regions(self.p, &self.body.tys, t) as usize;
                for g in self.body.tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.closure_sources(e, vars, at, out);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in self.body.tys.tys_of(ts).to_vec() {
                    self.closure_sources(e, vars, at, out);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.closure_sources(e, vars, at, out),
            _ => *at += n,
        }
    }

    /// The conservative call rule: the result may hold any argument's
    /// regions (equal to them when it holds a `&mut`), and each `&mut`
    /// argument's target may receive every other argument's regions.
    /// The item slot vars of a call's revealed `impl Iterator<Item = T>`
    /// value (type `dt`, vars `dv`) where `T` writes `'static`: the
    /// definer's check proves its items outlive `T`'s lifetimes
    /// (`rpit_item_edges`), and rustc's caller sees only `T`, so those
    /// slots take no argument's loan (`let names: Vec<&'static str> =
    /// c.file_names().collect()`).
    fn opaque_static_items(&mut self, f: LocalDefId, dt: Ty, dv: &[u32]) -> Vec<u32> {
        let p = self.p;
        let ot = p.gx.opaque_ret_of.get(&f).copied().unwrap_or(p.fn_info(f).ret);
        let TyKind::Opaque(od, _) = p.tys.kind(ot) else { return Vec::new() };
        let Some(item) = p.gx.opaques.get(&od).and_then(|i| i.item_out) else { return Vec::new() };
        let mut rs = Vec::new();
        regions_of(&p.tys, item, &mut rs);
        if !rs.contains(&Region::Static) {
            return Vec::new();
        }
        let mut cands = Vec::new();
        if !self.iter_items(dt, dv, &mut cands) {
            return Vec::new();
        }
        let mut out = Vec::new();
        for c in cands {
            if c.len() != rs.len() {
                return Vec::new();
            }
            out.extend(c.iter().zip(&rs).filter(|(_, r)| **r == Region::Static).map(|(&v, _)| v));
        }
        out
    }

    /// True when `f` returns an `impl Trait` value. A template callee
    /// (`lust check` makes no instances) keeps its opaque return in
    /// `FnInfo::ret`.
    fn returns_opaque(&self, f: LocalDefId) -> bool {
        self.p.gx.opaque_ret_of.contains_key(&f) || crate::check::opaque::mentions_opaque(&self.p.tys, self.p.fn_info(f).ret, None)
    }

    /// The vars of a call of `f` that its `impl Trait` value captures:
    /// the call's vars for the universals a `use<..>` list names
    /// (`RegionSig::opaque_caps`), or for every universal without one
    /// (edition 2024 captures every lifetime param, elided ones too), and
    /// for every type param (all of which it captures). A `'static` in an
    /// argument type (`Rc<dyn Fn()>`'s object lifetime) is no param.
    /// The signature is instantiated as in `call_sig_with`: arguments
    /// flow into fresh universals, related by the callee's facts and by
    /// the bounds its param types imply (`&'a &'b u8`: `'b: 'a`), so a
    /// captured universal holds what the hidden type may hold shortened
    /// to it. All argument regions when the signature does not pair.
    fn captured_vars(&mut self, f: LocalDefId, avs: &[(Ty, Vec<u32>)]) -> Vec<u32> {
        let all = || avs.iter().flat_map(|(_, v)| v.iter().copied()).collect();
        let p = self.p;
        let info = p.fn_info(f);
        let Some(sig) = p.regions.opaque_sig(p, f).filter(|s| s.params.len() == avs.len() && info.params.len() == avs.len()) else {
            return all();
        };
        let caps: Vec<u32> = match &sig.opaque_caps {
            Some(c) => c.clone(),
            None => (0..sig.n_univ).collect(),
        };
        let univ: Vec<u32> = (0..sig.n_univ).map(|_| self.fresh()).collect();
        let mut binds: FxMap<u32, Vec<u32>> = FxMap::default();
        self.bind_tys.clear();
        for (i, (at, av)) in avs.iter().enumerate() {
            let et = if p.tys.flags(info.params[i]).contains_param() { *at } else { info.params[i] };
            let mut pv = Vec::new();
            if !self.inst(sig.params[i], et, &univ, &mut binds, &mut pv) || (!av.is_empty() && !self.relate(*at, av, et, &pv, Variance::Co)) {
                return all();
            }
            self.sig_implied_edges(sig.params[i], &univ);
        }
        for &(a, b) in &sig.facts {
            let (x, y) = (self.inst_region(a, &univ), self.inst_region(b, &univ));
            self.edge(x, y);
        }
        let mut out: Vec<u32> = caps.iter().filter_map(|&k| univ.get(k as usize).copied()).collect();
        for vs in binds.values() {
            out.extend(vs);
        }
        // The callee's bounds hold at the call as for any fn (`F: Fn(&mut
        // L<'s>)` ties the argument passed for `'s`); the signature's
        // return is a placeholder, so only the arguments pair here.
        let src = p.gx.instances.get(&f).and_then(|i| i.template_local).unwrap_or(f);
        let preds = p.gx.fn_templates.get(src.0 as usize).and_then(|t| t.as_ref()).map_or(&[][..], |t| &t.generics.predicates[..]);
        if !preds.is_empty() {
            let _ = self.call_sig_with(sig, &info.params, UNIT, avs, UNIT, &[], preds);
        }
        out
    }

    /// The outlives bounds a regioned signature type implies, as edges
    /// between the call's universals `univ`: what a reference points at
    /// outlives it, and (conservatively) an Adt's regions outlive each
    /// other, for the bounds its fields would imply.
    fn sig_implied_edges(&mut self, t: Ty, univ: &[u32]) {
        let tys = &self.p.tys;
        let var = |r: Region| match r {
            Region::Param(k) => univ.get(k as usize).copied(),
            _ => None,
        };
        let mut pairs: Vec<(u32, u32)> = Vec::new();
        let mut stack = vec![t];
        while let Some(t) = stack.pop() {
            match tys.kind(t) {
                TyKind::Ref(r, _, inner) => {
                    let mut rs = Vec::new();
                    regions_of(tys, inner, &mut rs);
                    if let Some(y) = var(r) {
                        pairs.extend(rs.iter().filter_map(|&x| var(x)).map(|x| (x, y)));
                    }
                    stack.push(inner);
                }
                TyKind::Adt(..) => {
                    let mut rs = Vec::new();
                    regions_of(tys, t, &mut rs);
                    let vs: Vec<u32> = rs.iter().filter_map(|&x| var(x)).collect();
                    pairs.extend(vs.iter().flat_map(|&x| vs.iter().map(move |&y| (x, y))).filter(|(x, y)| x != y));
                }
                TyKind::Slice(e) | TyKind::Array(e, _) | TyKind::RawPtr(_, e) => stack.push(e),
                TyKind::Tuple(ts) => stack.extend(tys.tys_of(ts).iter().copied()),
                _ => {}
            }
        }
        for (x, y) in pairs {
            self.edge(x, y);
        }
    }

    fn call_opaque(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) {
        let all: Vec<u32> = avs.iter().flat_map(|(_, v)| v.iter().copied()).collect();
        self.call_opaque_from(avs, &all, dt, dv);
    }

    /// `call_opaque` where only the vars `into_dest` reach the result
    /// (`captured_vars`); a `&mut` argument may still take any
    /// argument's regions, at their variance (`store_into`).
    fn call_opaque_from(&mut self, avs: &[(Ty, Vec<u32>)], into_dest: &[u32], dt: Ty, dv: &[u32]) {
        let all = into_dest;
        if has_mut_ref(&self.body.tys, dt) || has_interior(&self.body.tys, dt) {
            self.equate_all(&all, dv);
        } else {
            self.flow_all(&all, dv);
        }
        for (i, (t, v)) in avs.iter().enumerate() {
            if let TyKind::Ref(_, Mut::Mut, pt) = self.body.tys.kind(*t)
                && !v.is_empty()
                && (v.len() > 1 || store::has_fn_ptr(&self.body.tys, pt))
            {
                // Exact variance for what it may store (`store_into`), and
                // a one-way flow of the rest into every slot. A builtin
                // stores a plain argument whole (or the values it holds, as
                // they are), so the parts `store_into` related go nowhere
                // else: `v.push((a, b))` into `Vec<(&'a u8, &'b u8)>` needs
                // no `'a: 'b`. Any other callee or argument may move a part
                // anywhere.
                let pv = v[1..].to_vec();
                // An iterator method's `dyn` callable (`fold(0, f)` for `f:
                // &mut dyn FnMut(..)`): an unsized pointee cannot be
                // overwritten, so only its methods take values, at its trait
                // args' slots, never at its object lifetime. (A stored `&mut
                // dyn` keeps the flow: `v.push(d)` may fix `v`'s type.)
                if let TyKind::Dyn(_, r) = self.body.tys.kind(pt)
                    && self.cur_builtin.is_some_and(crate::lower::iter::expands)
                    && self.dyn_fn_sig(*t).is_some()
                {
                    let args = &pv[usize::from(!bound(r)).min(pv.len())..];
                    let all: Vec<u32> = avs.iter().enumerate().filter(|(j, _)| *j != i).flat_map(|(_, (_, v))| v.iter().copied()).collect();
                    self.flow_all(&all, args);
                    continue;
                }
                for (j, (at, av)) in avs.iter().enumerate() {
                    if j != i {
                        self.store_into(*at, av, pt, &pv);
                        let exact = self.cur_builtin.is_some() && store::plain_store(&self.body.tys, *at);
                        let rest: Vec<u32> = av.iter().zip(&self.store_covered).filter(|(_, c)| !exact || !**c).map(|(&x, _)| x).collect();
                        self.flow_all(&rest, &pv);
                    }
                }
            }
        }
    }

    /// Instantiates `sig` at a call of `f`: fresh vars for its universals,
    /// type params bound from `f`'s erased param types, `arg <: param` and
    /// `ret <: dest`, plus the callee's facts and implied bounds. False when
    /// the signature cannot be paired with the call's types.
    fn call_sig(&mut self, f: LocalDefId, sig: &RegionSig, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let p = self.p;
        // An `impl Trait` return captures every input region (edition
        // 2024): the call takes `call_opaque` (W-CHECK-G3).
        if p.gx.opaque_ret_of.contains_key(&f) {
            return false;
        }
        let info = p.fn_info(f);
        // The callee's bounds name the template's params, like `sig`.
        let src = p.gx.instances.get(&f).and_then(|i| i.template_local).unwrap_or(f);
        let preds = p.gx.fn_templates.get(src.0 as usize).and_then(|t| t.as_ref()).map_or(&[][..], |t| &t.generics.predicates[..]);
        self.call_sig_with(sig, &info.params, info.ret, avs, dt, dv, preds)
    }

    /// `call_sig` over the callee's erased param and return types. A
    /// `T: 'static` bound makes every region bound to `T` outlive
    /// `'static` (check proves the rest of the bound; regions are here).
    #[allow(clippy::too_many_arguments)]
    fn call_sig_with(
        &mut self,
        sig: &RegionSig,
        params: &[Ty],
        ret: Ty,
        avs: &[(Ty, Vec<u32>)],
        dt: Ty,
        dv: &[u32],
        preds: &[Predicate],
    ) -> bool {
        if params.len() != sig.params.len() || avs.len() != sig.params.len() {
            return false;
        }
        let mut univ: Vec<u32> = Vec::with_capacity(sig.n_univ as usize);
        for k in 0..sig.n_univ as usize {
            let v = match self.seed_univ.get(k) {
                Some(&v) => v,
                None => self.fresh(),
            };
            univ.push(v);
        }
        let mut binds: FxMap<u32, Vec<u32>> = FxMap::default();
        self.bind_tys.clear();
        for (j, vs, t) in std::mem::take(&mut self.seed_binds) {
            binds.insert(j, vs);
            self.bind_tys.insert(j, t);
        }
        let mut ok = true;
        // A callee type that names type params (a template called in
        // check mode, a stub) has no slots where its params are: the
        // call's own types give them, so the params bind their slots.
        let has_param = |t: Ty| self.p.tys.flags(t).contains_param();
        // A constant at a type param's position (`map_or("", f)`'s `U`)
        // holds only `'static` data: its params bind at their other uses
        // first (the return's `&str`), and a slot count that differs
        // there is no pairing failure.
        let mut consts: Vec<usize> = Vec::new();
        for i in 0..avs.len() {
            let (at, av) = &avs[i];
            if *at == ERROR && av.is_empty() && has_param(params[i]) {
                consts.push(i);
                continue;
            }
            let et = if has_param(params[i]) { *at } else { params[i] };
            let mut pv = Vec::new();
            ok &= self.inst(sig.params[i], et, &univ, &mut binds, &mut pv);
            if !av.is_empty() {
                self.guard_coerce = !has_param(params[i]) && outer_dyn_pointees(&self.p.tys, params[i], params[i], true, true).is_some();
                ok &= self.relate(*at, av, et, &pv, Variance::Co);
                self.guard_coerce = false;
            }
        }
        let er = if has_param(ret) { dt } else { ret };
        let mut rv = Vec::new();
        self.inst_ret = true;
        ok &= self.inst(sig.ret, er, &univ, &mut binds, &mut rv);
        self.inst_ret = false;
        if !dv.is_empty() {
            ok &= self.relate(er, &rv, dt, dv, Variance::Co);
        }
        for i in consts {
            let mut pv = Vec::new();
            self.inst(sig.params[i], ERROR, &univ, &mut binds, &mut pv);
        }
        for &(a, b) in &sig.facts {
            let (x, y) = (self.inst_region(a, &univ), self.inst_region(b, &univ));
            self.edge(x, y);
        }
        let flows = ok && self.item_bound_flows(preds, &binds);
        let mut equated = false;
        if ok {
            equated = self.item_bound_equate(sig, &binds, &univ);
            self.replay_bounds(sig, &univ, &binds);
        }
        self.item_bound_exact = flows || equated;
        // `T: Tr<'a>` for a trait with lifetime params: the type bound to
        // `T` implements `Tr` with exactly those lifetimes (trait args are
        // invariant), so its own (this body's bound on a type param, or the
        // selected impl's header) equal the call's `'a`; unknown ones are
        // `'static`, never free.
        for b in &sig.trait_bounds {
            let n = b.lifetimes.len();
            let want: Vec<u32> = b.lifetimes.iter().map(|&r| self.inst_region(r, &univ)).collect();
            let have = match (self.bind_tys.get(&b.param).copied(), binds.get(&b.param).cloned()) {
                (Some(t), Some(vs)) => self.trait_lts_for(b.trait_def, t, &vs, n),
                _ => None,
            }
            .unwrap_or_else(|| vec![0; n]);
            for (x, y) in want.into_iter().zip(have) {
                self.edge(x, y);
                self.edge(y, x);
            }
        }
        for pred in preds {
            if let Predicate::TypeOutlives(t, Region::Static) = pred
                && let TyKind::Param(j) = self.p.tys.kind(*t)
                && let Some(vs) = binds.get(&j.0)
            {
                for &v in vs {
                    self.edge(v, 0);
                }
            }
            // `T: 'a` (fns and inherent methods): the regions bound to `T`
            // outlive the call's `'a`, and so do this body's type params
            // inside `T`'s type, by this body's own bounds.
            if let Predicate::TypeOutlives(t, Region::Param(k)) = pred
                && let TyKind::Param(j) = self.p.tys.kind(*t)
            {
                let a = self.inst_region(Region::Param(*k), &univ);
                match (binds.get(&j.0).cloned(), self.bind_tys.get(&j.0).copied()) {
                    (Some(vs), Some(actual)) => {
                        for &v in &vs {
                            self.edge(v, a);
                        }
                        self.params_outlive(actual, a);
                    }
                    // `T` only in a bound (`F: FnOnce() -> T`): the output of
                    // what `F` binds to, when it has no slots of its own.
                    _ => match self.bound_output_actual(j.0, preds) {
                        Some(actual) if self.sc.slots(actual) == 0 => self.params_outlive(actual, a),
                        _ => self.type_outlives_unproved(),
                    },
                }
            }
            // `P: Tr` proves more through trait selection: `Tr` (or a
            // supertrait) bounded by `'static` makes `P` `'static`, and the
            // impl selected for `P`'s type adds its own `X: 'static`
            // where-clauses on the parts of `P` they name.
            if let Predicate::Trait(b) = pred
                && b.count == 0
                && let Some(self_t) = self.p.tys.args(b.value.args).first().and_then(|g| g.as_ty())
                && let TyKind::Param(j) = self.p.tys.kind(self_t)
                && let Some(vs) = binds.get(&j.0).cloned()
            {
                if self.p.gx.dyn_infos.get(&b.value.def).is_some_and(|i| i.static_bound) {
                    for &v in &vs {
                        self.edge(v, 0);
                    }
                }
                if let Some(&actual) = self.bind_tys.get(&j.0) {
                    self.impl_static_edges(b.value.def, actual, &vs);
                }
            }
            // A closure passed for `F: Fn*(A..)`: an input that is a type
            // param there is that param's regions exactly (`&T`: past its
            // higher-ranked outer reference).
            if let Predicate::Trait(b) = pred
                && b.count == 0
                && self.p.gx.lang.is_fn_family(b.value.def)
            {
                self.link_bound_closure(b.value.args, &binds, sig, &univ);
                self.tie_bound_output(b.value.args, &binds, sig, &univ);
                self.free_sig_bound(b.value.args, sig, &univ);
                self.flow_closure_output(b.value.args, &binds, sig, &univ, dv);
                self.entail_bound(b.value.args, sig, &univ);
                self.entail_bound_ptr(b.value.args, &binds, sig, &univ);
                self.flow_bound_inputs(b.value.args, &binds, sig, &univ);
            }
        }
        ok
    }

    /// The type params of this body inside `t` (a callee's `T: 'a` at a
    /// call, `a` its var) outlive `a`: each must have a `P: 'static` bound,
    /// or `P: 'r` facts (bounds, implied bounds), and then every such `'r`
    /// outlives `a` (rustc needs one; requiring all only restricts). A
    /// param without facts, a projection, or a closure body is
    /// `type_outlives_unproved`.
    fn params_outlive(&mut self, t: Ty, a: u32) {
        let tys = &self.body.tys;
        if !tys.flags(t).contains_param() {
            return;
        }
        if tys.flags(t).contains_projection() {
            return self.type_outlives_unproved();
        }
        let mut ps = Vec::new();
        params_in(tys, t, &mut ps);
        let p = self.p;
        // A closure body's type params are its enclosing fn's: that fn's
        // bounds, read through the closure's universals for its lifetimes.
        let f = root_fn(p, self.body.fn_id);
        let bounds = crate::check::outlives::param_bounds(p, p.regions.own_body_sig(p, f), fn_env(p, f));
        for j in ps {
            if bounds.contains(&(j, Region::Static)) {
                continue;
            }
            let rs: Vec<u32> = bounds.iter().filter(|(k, _)| *k == j).filter_map(|&(_, r)| if let Region::Param(i) = r { self.root_univ(i) } else { None }).collect();
            if rs.is_empty() {
                self.type_outlives_unproved();
            }
            for u in rs {
                self.edge(u, a);
            }
        }
    }

    /// `params_outlive` for the hidden type `t` of this body's `impl Trait
    /// + 'a` return (`a` the universal of `'a`): each type param in it needs
    /// a `P: 'static` bound or `P: 'r` facts whose `'r` outlive `a`, else
    /// L0617 (rustc E0309).
    fn hidden_params_outlive(&mut self, t: Ty, a: u32) {
        let tys = &self.body.tys;
        if !tys.flags(t).contains_param() {
            return;
        }
        let mut ps = Vec::new();
        params_in(tys, t, &mut ps);
        let p = self.p;
        let f = self.body.fn_id;
        let bounds = crate::check::outlives::param_bounds(p, p.regions.own_body_sig(p, f), fn_env(p, f));
        for j in ps {
            if bounds.contains(&(j, Region::Static)) {
                continue;
            }
            let rs: Vec<u32> = bounds.iter().filter(|(k, _)| *k == j).filter_map(|&(_, r)| if let Region::Param(i) = r { Some(i + 1) } else { None }).collect();
            if rs.is_empty() {
                self.errs.push(Diag::new(
                    "L0617",
                    p.fn_def(f).name_span,
                    "a type parameter may not live long enough: the returned `impl Trait` must outlive a lifetime it does not",
                    "Add the bound (`T: 'a`) to the type parameter the returned value holds.",
                ));
                return;
            }
            for u in rs {
                self.edge(u, a);
            }
        }
    }

    /// True when fn `f` (its template) has a `T: 'a` bound on a named
    /// lifetime: a call that does not pair its signature cannot prove it.
    fn has_type_outlives(&self, f: LocalDefId) -> bool {
        let p = self.p;
        let src = p.gx.instances.get(&f).and_then(|i| i.template_local).unwrap_or(f);
        p.gx.fn_templates
            .get(src.0 as usize)
            .and_then(|t| t.as_ref())
            .is_some_and(|t| t.generics.predicates.iter().any(|q| matches!(q, Predicate::TypeOutlives(_, Region::Param(_)))))
    }

    /// The type a call gives callee param `j` when `j` is only the output
    /// of an Fn-family bound on another param `F` (`F: FnOnce() -> T`):
    /// the output of the closure `F` binds to, or of this body's own
    /// Fn-family bound when `F` binds to a param of this body.
    fn bound_output_actual(&self, j: u32, preds: &[Predicate]) -> Option<Ty> {
        let p = self.p;
        let lang = p.gx.lang;
        let out_assoc = lang.output_of(lang.fn_once)?;
        let output_of = |pred: &Predicate| -> Option<(Ty, Ty)> {
            let Predicate::Trait(b) = pred else { return None };
            if b.count != 0 || !lang.is_fn_family(b.value.def) {
                return None;
            }
            let self_t = p.tys.args(b.value.args).first()?.as_ty()?;
            let out = p.tys.bindings(b.value.bindings).iter().find(|(d, _)| *d == out_assoc)?.1.as_ty()?;
            Some((self_t, out))
        };
        let f = preds.iter().filter_map(output_of).find_map(|(st, out)| match (p.tys.kind(st), p.tys.kind(out)) {
            (TyKind::Param(f), TyKind::Param(o)) if o.0 == j => Some(f.0),
            _ => None,
        })?;
        let ft = *self.bind_tys.get(&f)?;
        match self.body.tys.kind(ft) {
            TyKind::Closure(def, _) => p.gx.closures.get(&def).map(|c| c.output),
            TyKind::Param(_) => fn_env(p, self.body.fn_id).iter().filter_map(output_of).find_map(|(st, out)| (st == ft).then_some(out)),
            _ => None,
        }
    }

    /// A callee's `T: 'a` bound that this call cannot prove (L0203).
    fn type_outlives_unproved(&mut self) {
        self.errs.push(Diag::new(
            "L0203",
            self.span,
            "lust cannot prove the callee's `T: 'a` bound at this call yet",
            "Give the caller the same bound (`T: 'a` on its own type parameter), or bound the type by `'static`.",
        ));
    }

    /// The vars a call takes for the lifetime params of the callee's trait
    /// (its universals `0..n`) when `f` is a method of a trait with
    /// lifetime params (a stub, or a default body and its instances):
    /// those of the receiver's type (`trait_lts_for`), else `'static`. Never
    /// fresh: a fresh trait lifetime would let the callee take a borrow for
    /// less than the trait promises. Empty for any other callee.
    fn trait_lifetime_seeds(&mut self, f: LocalDefId, avs: &[(Ty, Vec<u32>)]) -> Vec<u32> {
        let p = self.p;
        let trait_method = |g: LocalDefId| p.fn_defs.get(g.0 as usize).copied().filter(|d| p.regions.trait_methods.contains_key(d));
        let Some(m) = p
            .regions
            .stub_method(p, f)
            .or_else(|| trait_method(f))
            .or_else(|| trait_method(p.gx.instances.get(&f)?.template_local?))
        else {
            return Vec::new();
        };
        let Some(trait_def) = p.gx.index.trait_of_method(m) else { return Vec::new() };
        let n = p.gx.adt_lifetimes.get(&trait_def).map_or(0, |v| v.len());
        if n == 0 {
            return Vec::new();
        }
        let has_self = p.gx.trait_methods.get(&m).is_some_and(|t| t.self_kind.is_some());
        if has_self && let Some((rt, rv)) = avs.first() {
            let (mut t, mut skip) = (*rt, 0usize);
            while let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
                t = inner;
                skip += 1;
            }
            let vars: Vec<u32> = rv.iter().skip(skip).copied().collect();
            if let Some(seeds) = self.trait_lts_for(trait_def, t, &vars, n) {
                return seeds;
            }
        }
        vec![0; n]
    }

    /// The vars of the `n` lifetime params of `trait_def` that Self type `t`
    /// (erased, slot vars `vars`) implements it with: through this body's
    /// bound on a type param (`Self` in the trait's own default body: the
    /// trait's lifetimes), or through the one impl whose header matches
    /// (`impl Tr<'static> for S`: `'static`; `impl<'d> Tr<'d> for S<'d>`:
    /// `S`'s region; a lifetime the Self type does not name is free).
    /// None when neither tells, or when the impl has where-clauses that
    /// would need a replay of their own.
    fn trait_lts_for(&mut self, trait_def: DefId, t: Ty, vars: &[u32], n: usize) -> Option<Vec<u32>> {
        self.trait_lts_at(trait_def, t, vars, n, 0)
    }

    fn trait_lts_at(&mut self, trait_def: DefId, t: Ty, vars: &[u32], n: usize, depth: u32) -> Option<Vec<u32>> {
        let p = self.p;
        if depth > 8 {
            return None;
        }
        // A closure body's type params are its creator's: the enclosing
        // fn's bound tells, read through the closure's universals for its
        // lifetimes. An impl's header tells the same in any body.
        if let TyKind::Param(j) = self.body.tys.kind(t) {
            let root = root_fn(p, self.body.fn_id);
            let sig = p.regions.own_body_sig(p, root)?;
            if let Some(b) = sig.trait_bounds.iter().find(|b| b.param == j.0 && b.trait_def == trait_def) {
                return b.lifetimes.iter().map(|&r| if let Region::Param(k) = r { self.root_univ(k) } else { Some(0) }).collect();
            }
            let own_trait = p.fn_defs.get(root.0 as usize).and_then(|&d| p.gx.index.trait_of_method(d));
            if j.0 == 0 && own_trait == Some(trait_def) && sig.n_univ as usize >= n {
                return (0..n as u32).map(|k| self.root_univ(k)).collect();
            }
            return None;
        }
        let mut found: Option<Vec<u32>> = None;
        for &id in p.gx.index.impls_of_trait(trait_def) {
            let rec = p.gx.index.get(id);
            let Some(pat) = p.tys.args(rec.trait_ref.args).first().and_then(|g| g.as_ty()) else { continue };
            let mut parts: FxMap<u32, Vec<u32>> = FxMap::default();
            if !self.match_impl_self(pat, t, vars, &mut 0, &mut parts) {
                continue;
            }
            let head = p.regions.impl_heads.get(&rec.def)?;
            // Every where-clause on a lifetime trait must be one the head
            // kept (on a type param), else nothing tells its lifetimes.
            let nested = rec.generics.predicates.iter().filter(|pr| self.lifetime_trait_pred(pr)).count();
            if found.is_some() || nested != head.where_lts.len() {
                return None;
            }
            let mut lts: FxMap<u32, u32> = FxMap::default();
            self.match_impl_lifetimes(head.self_ty, t, vars, &mut 0, &mut lts);
            // The impl's own `T: Tr2<'x>` bounds: the part of Self that `T`
            // matched implements `Tr2` with lifetimes equal to the impl's
            // `'x` (replayed the same way, a bounded number of levels).
            if !head.where_lts.is_empty() {
                let mut part_tys: FxMap<u32, Ty> = FxMap::default();
                self.impl_param_tys(pat, t, &mut part_tys);
                for w in head.where_lts.clone() {
                    let pt = *part_tys.get(&w.param)?;
                    let pv = parts.get(&w.param).cloned().unwrap_or_default();
                    let inner = self.trait_lts_at(w.trait_def, pt, &pv, w.lifetimes.len(), depth + 1)?;
                    for (r, v) in w.lifetimes.iter().zip(inner) {
                        let x = match *r {
                            Region::Param(m) => match lts.get(&m) {
                                Some(&x) => x,
                                None => {
                                    let x = self.fresh();
                                    lts.insert(m, x);
                                    x
                                }
                            },
                            _ => 0,
                        };
                        self.edge(x, v);
                        self.edge(v, x);
                    }
                }
            }
            let mut out = Vec::with_capacity(n);
            for &r in &head.trait_lifetimes {
                let v = match r {
                    Region::Param(m) => match lts.get(&m) {
                        Some(&v) => v,
                        None => self.fresh(),
                    },
                    _ => 0,
                };
                out.push(v);
            }
            found = Some(out);
        }
        found.filter(|v| v.len() == n)
    }

    /// The erased part of `actual` each type param of an impl's Self
    /// pattern `pat` matches.
    fn impl_param_tys(&self, pat: Ty, actual: Ty, out: &mut FxMap<u32, Ty>) {
        let tys = &self.body.tys;
        match (tys.kind(pat), tys.kind(actual)) {
            (TyKind::Param(k), _) => {
                out.entry(k.0).or_insert(actual);
            }
            (TyKind::Ref(_, _, pi), TyKind::Ref(_, _, ai)) => self.impl_param_tys(pi, ai, out),
            (TyKind::Adt(pd, pa), TyKind::Adt(ad, aa)) if pd == ad => {
                let (xs, ys): (Vec<Ty>, Vec<Ty>) =
                    (tys.args(pa).iter().filter_map(|g| g.as_ty()).collect(), tys.args(aa).iter().filter_map(|g| g.as_ty()).collect());
                for (x, y) in xs.into_iter().zip(ys) {
                    self.impl_param_tys(x, y, out);
                }
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                for (x, y) in tys.tys_of(a).to_vec().into_iter().zip(tys.tys_of(b).to_vec()) {
                    self.impl_param_tys(x, y, out);
                }
            }
            (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
                self.impl_param_tys(a, b, out)
            }
            _ => {}
        }
    }

    /// True for a predicate on a trait with lifetime params.
    fn lifetime_trait_pred(&self, pr: &Predicate) -> bool {
        matches!(pr, Predicate::Trait(b) if self.p.gx.adt_lifetimes.get(&b.value.def).is_some_and(|v| !v.is_empty()))
    }

    /// Matches an impl's regioned Self type against an erased type whose
    /// slots are `vars` from `*at`, collecting the var of each impl
    /// lifetime param it names (`Region::Param(k)`).
    fn match_impl_lifetimes(&mut self, pat: Ty, actual: Ty, vars: &[u32], at: &mut usize, out: &mut FxMap<u32, u32>) {
        let tys = &self.body.tys;
        match (tys.kind(pat), tys.kind(actual)) {
            (TyKind::Ref(r, pm, pi), TyKind::Ref(_, am, ai)) if pm == am => {
                if let (Region::Param(k), Some(&v)) = (r, vars.get(*at)) {
                    out.entry(k).or_insert(v);
                }
                *at += 1;
                self.match_impl_lifetimes(pi, ai, vars, at, out);
            }
            (TyKind::Adt(pd, pa), TyKind::Adt(ad, aa)) if pd == ad => {
                let lts: Vec<Region> = tys.args(pa).iter().filter_map(|g| if let GenericArg::Lifetime(r) = g && *r != crate::ty::DYN_LATE { Some(*r) } else { None }).collect();
                let n = adt_regions(self.p, tys, actual) as usize;
                for (i, r) in lts.into_iter().enumerate().take(n) {
                    if let (Region::Param(k), Some(&v)) = (r, vars.get(*at + i)) {
                        out.entry(k).or_insert(v);
                    }
                }
                *at += n;
                let (xs, ys): (Vec<Ty>, Vec<Ty>) =
                    (tys.args(pa).iter().filter_map(|g| g.as_ty()).collect(), tys.args(aa).iter().filter_map(|g| g.as_ty()).collect());
                for (x, y) in xs.into_iter().zip(ys) {
                    self.match_impl_lifetimes(x, y, vars, at, out);
                }
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                for (x, y) in tys.tys_of(a).to_vec().into_iter().zip(tys.tys_of(b).to_vec()) {
                    self.match_impl_lifetimes(x, y, vars, at, out);
                }
            }
            (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
                self.match_impl_lifetimes(a, b, vars, at, out)
            }
            _ => *at += self.sc.slots(actual) as usize,
        }
    }

    /// A call through the `Fn*` bound of a type param of this body
    /// (`(self.f)(x)`: the callee is the bound's `call`, `call_mut`, or
    /// `call_once` stub, the receiver `F`, `&F`, or `&mut F`), with the
    /// bound from this fn's region signature (the fn's own, its impl's,
    /// or its trait's): the arguments flow into the bound's inputs and its
    /// output into the destination; a lifetime the bound writes is this
    /// fn's own, an elided one a fresh region of this call (higher-ranked).
    /// False when no regioned bound pairs: the caller then takes the
    /// conservative rule, which ties the result to the receiver too.
    /// `I: Iterator<Item = T>` (or `IntoIterator`) bounds of a callee
    /// where `I` and `T` are type params and the argument bound to `I` is
    /// an iterator whose items lust reads (`iter_items`): `T`'s regions
    /// take exactly those items' (`suggest(name, v.iter().map(..), ..)`
    /// returning `T` holds no loan the items do not hold). True when there
    /// was at least one such bound and every one paired.
    fn item_bound_flows(&mut self, preds: &[Predicate], binds: &FxMap<u32, Vec<u32>>) -> bool {
        let p = self.p;
        let item_of = |tr: DefId| {
            p.gx.index.trait_record(tr).and_then(|r| r.assoc_items.iter().find(|a| p.interner.get(a.1) == "Item").map(|a| a.0))
        };
        let items: Vec<DefId> = [p.gx.lang.iterator, p.gx.lang.into_iterator].into_iter().filter_map(item_of).collect();
        let mut pairs: Vec<(Ty, Ty)> = Vec::new();
        for pr in preds {
            match pr {
                Predicate::AssocEq(b) if items.contains(&b.value.assoc) => {
                    let Some(st) = p.tys.args(b.value.trait_args).first().and_then(|g| g.as_ty()) else { return false };
                    pairs.push((st, b.value.ty));
                }
                Predicate::Trait(b) => {
                    for &(d, t) in p.tys.bindings(b.value.bindings) {
                        if items.contains(&d) {
                            let (Some(st), Some(t)) = (p.tys.args(b.value.args).first().and_then(|g| g.as_ty()), t.as_ty()) else { return false };
                            pairs.push((st, t));
                        }
                    }
                }
                _ => {}
            }
        }
        if pairs.is_empty() {
            return false;
        }
        for (st, t) in pairs {
            let (TyKind::Param(ji), TyKind::Param(jt)) = (p.tys.kind(st), p.tys.kind(t)) else { return false };
            let (Some(&it), Some(iv), Some(tv)) = (self.bind_tys.get(&ji.0), binds.get(&ji.0).cloned(), binds.get(&jt.0).cloned()) else { return false };
            let mut cands = Vec::new();
            if crate::ty::iter::iter_parts(&self.body.tys, it).is_none() || !self.iter_items(it, &iv, &mut cands) || cands.is_empty() || cands.iter().any(|c| c.len() != tv.len()) {
                return false;
            }
            for c in cands {
                for (&a, &b) in c.iter().zip(&tv) {
                    self.edge(a, b);
                }
            }
        }
        true
    }

    /// True when `f`'s template bounds an `Item` of `Iterator` or
    /// `IntoIterator` to a type (`call`'s over-approximation, W-STD-C).
    fn item_bound(&self, f: LocalDefId) -> bool {
        let p = self.p;
        let src = p.gx.instances.get(&f).and_then(|i| i.template_local).unwrap_or(f);
        let Some(Some(t)) = p.gx.fn_templates.get(src.0 as usize) else { return false };
        let items: Vec<DefId> = [p.gx.lang.iterator, p.gx.lang.into_iterator]
            .iter()
            .filter_map(|&tr| p.gx.index.trait_record(tr))
            .flat_map(|r| r.assoc_items.iter().filter(|a| p.interner.get(a.1) == "Item").map(|a| a.0).collect::<Vec<_>>())
            .collect();
        t.generics.predicates.iter().any(|pr| match pr {
            Predicate::AssocEq(b) => items.contains(&b.value.assoc),
            Predicate::Trait(b) => p.tys.bindings(b.value.bindings).iter().any(|(d, _)| items.contains(d)),
            _ => false,
        })
    }

    /// In a closure body: per lifetime `'k` of the enclosing fn (by `k`),
    /// the universal of a closure parameter slot whose annotation names it
    /// (`|p: &mut Parser<'a>, _| parse_element(p)`), when every lifetime
    /// that the regioned types `tys` name has one. Its creator ties such a
    /// slot to that lifetime (`closure_arg_slots`), so a call through the
    /// enclosing fn's `Fn` bound may bind `'k` to it. Other entries are
    /// fresh vars (no named input uses them).
    fn closure_named_univs(&mut self, tys: &[Ty]) -> Option<Vec<u32>> {
        let p = self.p;
        let c = p.gx.closure_fns.get(&self.body.fn_id).and_then(|d| p.gx.closures.get(d))?;
        let slots = closure_arg_slots(&mut self.sc, c).ok()?;
        let mut map: Vec<Option<u32>> = Vec::new();
        let mut at = 0usize;
        for l in 2..=self.body.arg_count {
            let us = self.own.slots.get(l)?.clone();
            for (s, &u) in us.iter().enumerate() {
                if let Some((_, Some(Region::Param(k)))) = slots.get(at + s)
                    && u != 0
                {
                    let k = *k as usize;
                    if map.len() <= k {
                        map.resize(k + 1, None);
                    }
                    map[k].get_or_insert(u);
                }
            }
            at += us.len();
        }
        if at != slots.len() {
            return None;
        }
        let mut rs = Vec::new();
        for &t in tys {
            regions_of(&p.tys, t, &mut rs);
        }
        if rs.iter().any(|r| matches!(r, Region::Param(k) if map.get(*k as usize).copied().flatten().is_none())) {
            return None;
        }
        Some(map.into_iter().map(|u| u.unwrap_or_else(|| self.fresh())).collect())
    }

    /// In a closure body: per lifetime `'k` of the enclosing fn, its
    /// universal (`OwnSig::fn_lts`), when every lifetime the regioned types
    /// `tys` name has one. Other entries are fresh vars.
    fn closure_fn_univs(&mut self, tys: &[Ty]) -> Option<Vec<u32>> {
        let mut rs = Vec::new();
        for &t in tys {
            regions_of(&self.p.tys, t, &mut rs);
        }
        let lts = self.own.fn_lts.clone();
        if rs.iter().any(|r| matches!(r, Region::Param(k) if lts.get(*k as usize).copied().flatten().is_none())) {
            return None;
        }
        Some(lts.into_iter().map(|u| u.unwrap_or_else(|| self.fresh())).collect())
    }

    /// `it.next()` (also `nth`, `last`, `min`, `max`, `next_back`,
    /// `nth_back`) through a type param's own `Iterator<Item = X>` bound,
    /// a trait stub call: the `Option<X>` result holds `X`'s regions
    /// (`fixed_items`), not the receiver's `&mut` borrow, as the trait's
    /// `-> Option<Self::Item>` says. False for another call (the caller
    /// takes the conservative rule).
    fn call_param_item(&mut self, f: LocalDefId, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let p = self.p;
        if p.gx.fn_class.get(f.0 as usize) != Some(&crate::check::generics::FnClass::Stub) {
            return false;
        }
        let Some(m) = p.regions.stub_method(p, f) else { return false };
        let lang = p.gx.lang;
        let named = |tr: DefId, names: &[&str]| {
            p.gx.index.trait_record(tr).is_some_and(|r| names.iter().any(|&n| r.method_by_name(p.interner.intern(n)) == Some(m)))
        };
        if !named(lang.iterator, &["next", "nth", "last", "min", "max"]) && !named(lang.double_ended_iterator, &["next_back", "nth_back"]) {
            return false;
        }
        let Some((rt, _)) = avs.first() else { return false };
        if self.body.tys.option_elem(dt).is_none() {
            return false;
        }
        let Some(items) = self.fixed_items(*rt) else { return false };
        if items.len() != dv.len() {
            return false;
        }
        for (&a, &b) in items.iter().zip(dv) {
            self.edge(a, b);
        }
        true
    }

    fn call_fn_bound(&mut self, f: LocalDefId, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let p = self.p;
        if p.gx.fn_class.get(f.0 as usize) != Some(&crate::check::generics::FnClass::Stub) {
            return false;
        }
        let Some(m) = p.regions.stub_method(p, f) else { return false };
        let lang = p.gx.lang;
        let is_call = [(lang.fn_, "call"), (lang.fn_mut, "call_mut"), (lang.fn_once, "call_once")]
            .iter()
            .any(|&(tr, name)| p.gx.index.trait_record(tr).and_then(|r| r.method_by_name(p.interner.intern(name))) == Some(m));
        let Some((rt, _)) = avs.first() else { return false };
        let mut t = *rt;
        while let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
            t = inner;
        }
        let TyKind::Param(j) = self.body.tys.kind(t) else { return false };
        // A closure body calls through its enclosing fn's bound; the
        // fn's lifetimes are not universals there, so only a bound that
        // names none (`'static` and elided ones) takes this rule.
        let Some(sig) = p.regions.own_body_sig(p, root_fn(p, self.body.fn_id)) else { return false };
        let Some(b) = sig.fn_bounds.iter().find(|b| b.param == j.0 && b.inputs.len() + 1 == avs.len()).cloned() else { return false };
        if !is_call {
            return false;
        }
        let mut closure_univ: Vec<u32> = Vec::new();
        if self.own.closure {
            let named = |ts: &[Ty]| {
                let mut rs = Vec::new();
                for &t in ts {
                    regions_of(&p.tys, t, &mut rs);
                }
                rs.iter().any(|r| matches!(r, Region::Param(_)))
            };
            // An input that must live for the fn's lifetime is proved here
            // only when a parameter annotation names that lifetime (its
            // slot stands for it, `closure_named_univs`); an output that
            // names one takes the conservative rule.
            if b.output.is_some_and(|o| named(&[o])) {
                return false;
            }
            if named(&b.inputs) {
                match self.closure_named_univs(&b.inputs).or_else(|| self.closure_fn_univs(&b.inputs)) {
                    Some(u) => closure_univ = u,
                    None => {
                        self.errs.push(Diag::new(
                            "L0203",
                            self.span,
                            "a call inside a closure through an `Fn` bound whose argument names a lifetime of the enclosing fn is not supported yet",
                            "Annotate the closure parameter with that lifetime, make the call outside the closure, or write the bound with an elided lifetime.",
                        ));
                        return false;
                    }
                }
            }
        }
        let univ: Vec<u32> = if self.own.closure { closure_univ } else { (1..=sig.n_univ).collect() };
        let mut binds: FxMap<u32, Vec<u32>> = FxMap::default();
        self.bind_tys.clear();
        let mut ok = true;
        // Each elided input lifetime is its own higher-ranked region, as in
        // rustc: one var each at this call.
        self.bound_each = Some(Vec::new());
        for (i, &it) in b.inputs.iter().enumerate() {
            let (at, av) = &avs[i + 1];
            let mut pv = Vec::new();
            ok &= self.inst(it, *at, &univ, &mut binds, &mut pv);
            if !av.is_empty() {
                ok &= self.relate(*at, av, *at, &pv, Variance::Co);
            }
        }
        // An elided output lifetime is the one elided input lifetime
        // (`sugar_elision` rejects the other cases; if one gets here, all
        // input ones are tied together, which only restricts the call).
        let each = self.bound_each.take().unwrap_or_default();
        let out_elided = b.output.is_some_and(|o| {
            let mut rs = Vec::new();
            regions_of(&p.tys, o, &mut rs);
            rs.iter().any(|r| matches!(r, Region::Bound(_)))
        });
        let bv = match each[..] {
            [v] => v,
            _ if !out_elided => self.fresh(),
            _ => {
                let v = self.fresh();
                for &x in &each {
                    self.edge(x, v);
                    self.edge(v, x);
                }
                v
            }
        };
        self.bound_var = Some(bv);
        if let Some(ot) = b.output {
            let mut rv = Vec::new();
            ok &= self.inst(ot, dt, &univ, &mut binds, &mut rv);
            if !dv.is_empty() {
                ok &= self.relate(dt, &rv, dt, dv, Variance::Co);
            }
        } else {
            ok &= dv.is_empty();
        }
        self.bound_var = None;
        ok
    }

    /// The free argument slots of the closure bound to `F` in a call's
    /// `F: Fn*(A..)` bound (`trait_args`; found through the type `F` binds,
    /// so a mono instance pairs like its template), equated with the
    /// call's instantiation of each type param of the callee the input
    /// holds (`binds`; at any depth: `T`, `&T`, `&V<'a, T>`).
    /// Records the closure in `bound_linked` when every free slot paired;
    /// `call` links any other closure conservatively.
    fn link_bound_closure(&mut self, trait_args: ArgsId, binds: &FxMap<u32, Vec<u32>>, sig: &RegionSig, univ: &[u32]) {
        let p = self.p;
        let targs: Vec<GenericArg> = p.tys.args(trait_args).to_vec();
        let (Some(self_t), Some(tuple)) = (targs.first().and_then(|g| g.as_ty()), targs.get(1).and_then(|g| g.as_ty())) else { return };
        let TyKind::Param(jf) = p.tys.kind(self_t) else { return };
        let Some(&ft) = self.bind_tys.get(&jf.0) else { return };
        let TyKind::Closure(def, _) = self.body.tys.kind(ft) else { return };
        let Some(vars) = self.closure_args.get(&def).cloned() else { return };
        let TyKind::Tuple(ts) = p.tys.kind(tuple) else { return };
        let inputs_tmpl: Vec<Ty> = p.tys.tys_of(ts).to_vec();
        let Some(c) = p.gx.closures.get(&def) else { return };
        let Ok(slots) = closure_arg_slots(&mut self.sc, c) else { return };
        let inputs = c.inputs.clone();
        // A reference the bound writes with an elided lifetime is
        // higher-ranked there: the callee may pass a borrow of its own
        // data, so the closure must take any region in that slot (rustc:
        // "not general enough"). A written one (`&'static Message`, the
        // callee's `'a`) ties the slot to that region. The regioned inputs
        // come from the callee's signature; without them every written
        // reference counts as higher-ranked.
        let regioned: Option<Vec<Ty>> =
            sig.fn_bounds.iter().find(|b| b.param == jf.0 && b.inputs.len() == inputs_tmpl.len()).map(|b| b.inputs.clone());
        let tmpl = regioned.unwrap_or_else(|| inputs_tmpl.clone());
        let mut kinds: Vec<BoundSlot> = Vec::with_capacity(slots.len());
        for (i, &it) in inputs.iter().enumerate() {
            match tmpl.get(i) {
                Some(&t) => self.bound_slots(t, it, univ, &mut kinds),
                None => kinds.extend(std::iter::repeat_n(BoundSlot::Free, self.sc.slots(it) as usize)),
            }
        }
        if kinds.iter().zip(&slots).any(|(k, (r, link))| *k == BoundSlot::Hr && (r.is_some() || link.is_some())) {
            self.not_general_enough();
            return;
        }
        // A tied slot is paired: the bound says exactly what flows in.
        let mut paired = vec![false; vars.len()];
        for (idx, k) in kinds.iter().enumerate() {
            if let BoundSlot::Tie(u) = *k
                && slots.get(idx).is_some_and(|(r, _)| r.is_some())
                && let Some(&v) = vars.get(idx)
            {
                self.edge(v, u);
                self.edge(u, v);
                paired[idx] = true;
            }
        }
        // A slot inside a type param's instantiation (`T`, `&T`, `&V<'a,
        // T>`) is equated with the call's binding of that slot.
        for (idx, k) in kinds.iter().enumerate() {
            if let BoundSlot::Param { j, q, n } = *k
                && let Some(bv) = binds.get(&j)
                && bv.len() == n as usize
                && slots.get(idx).is_some_and(|(r, _)| r.is_some())
                && let Some(&v) = vars.get(idx)
            {
                let b = bv[q as usize];
                self.edge(v, b);
                self.edge(b, v);
                paired[idx] = true;
            }
        }
        if slots.iter().enumerate().all(|(i, (r, _))| r.is_none() || paired.get(i) == Some(&true)) {
            self.bound_linked.push(def);
        }
    }

    /// A closure with a free output (`ClosureEntry::free_sig`, also behind
    /// `&`) passed for `F: Fn*(..) -> O` where `O` holds a higher-ranked
    /// region: its output region is one free region, never the input's,
    /// so it does not implement the bound (rustc E0308 "one type is more
    /// general than the other"); and a closure whose output is its
    /// input's where `O` fixes that slot.
    fn free_sig_bound(&mut self, trait_args: ArgsId, sig: &RegionSig, univ: &[u32]) {
        let p = self.p;
        let targs: Vec<GenericArg> = p.tys.args(trait_args).to_vec();
        let (Some(self_t), Some(tuple)) = (targs.first().and_then(|g| g.as_ty()), targs.get(1).and_then(|g| g.as_ty())) else { return };
        let (TyKind::Param(jf), TyKind::Tuple(ts)) = (p.tys.kind(self_t), p.tys.kind(tuple)) else { return };
        let n_in = p.tys.tys_of(ts).len();
        let Some(g) = sig.fn_bounds.iter().find(|b| b.param == jf.0 && b.inputs.len() == n_in).cloned() else { return };
        let Some(out_t) = g.output else { return };
        let Some(&(mut ft)) = self.bind_tys.get(&jf.0) else { return };
        while let TyKind::Ref(_, _, inner) = self.body.tys.kind(ft) {
            ft = inner;
        }
        let TyKind::Closure(def, _) = self.body.tys.kind(ft) else { return };
        let Some((c_out, free)) = p.gx.closures.get(&def).map(|c| (c.output, c.free_sig)) else { return };
        let mut outs: Vec<BoundSlot> = Vec::new();
        self.bound_slots(out_t, c_out, univ, &mut outs);
        if free {
            let mut rs = Vec::new();
            regions_of(&p.tys, out_t, &mut rs);
            if rs.iter().any(|r| matches!(r, Region::Bound(_))) && outs.contains(&BoundSlot::Hr) {
                self.free_output_not_general();
            }
            return;
        }
        // The other way: an output slot the closure's own bound made its
        // input's (`tie(|a: &u8| &G)`) meets a fixed one (`'static`, a
        // named lifetime, a type param's) where the bound's input is
        // higher-ranked, which no binder can be (`Fn(T) -> R` instead
        // takes the binder at the call's `T`).
        let Some(c_in) = p.gx.closures.get(&def).map(|c| c.inputs.clone()) else { return };
        let mut ins: Vec<BoundSlot> = Vec::new();
        for (&t, &ci) in g.inputs.iter().zip(&c_in) {
            self.bound_slots(t, ci, univ, &mut ins);
        }
        if !ins.contains(&BoundSlot::Hr) {
            return;
        }
        let hr = self.bound_hr_out_slots(def);
        if hr.iter().any(|&k| outs.get(k as usize).is_some_and(|&o| o != BoundSlot::Hr)) {
            self.free_output_not_general();
        }
    }

    /// L0735 for a closure whose output lifetime is not the one the bound
    /// it meets returns (`free_sig_bound`, `dyn_fn_coercion`).
    fn free_output_not_general(&mut self) {
        self.errs.push(Diag::new(
            "L0735",
            self.span,
            "this closure is not general enough for the bound it meets: its return lifetime and the bound's differ (one is its argument's, the other is not)",
            "Pass the closure where it is written (`f(|x: &T| ..)`), so it takes the bound's signature.",
        ));
    }

    /// A closure passed for `F: Fn*(..) -> R` whose regioned output names
    /// a lifetime (`-> &'static str`, the callee's `'a`) or is
    /// higher-ranked (`Fn(&u8) -> &u8`): rustc gives the closure that
    /// return type, so what the body returns from its captured or free
    /// argument slots (`closure_reqs`, else every captured source) must
    /// outlive that region, `'static` for a higher-ranked one (the callee
    /// picks it). Higher-ranked arguments take no part: the body itself
    /// checks those.
    fn tie_bound_output(&mut self, trait_args: ArgsId, binds: &FxMap<u32, Vec<u32>>, sig: &RegionSig, univ: &[u32]) {
        let p = self.p;
        let targs: Vec<GenericArg> = p.tys.args(trait_args).to_vec();
        let (Some(self_t), Some(tuple)) = (targs.first().and_then(|g| g.as_ty()), targs.get(1).and_then(|g| g.as_ty())) else { return };
        let (TyKind::Param(jf), TyKind::Tuple(ts)) = (p.tys.kind(self_t), p.tys.kind(tuple)) else { return };
        let n_in = p.tys.tys_of(ts).len();
        let Some(out_t) = sig.fn_bounds.iter().find(|b| b.param == jf.0 && b.inputs.len() == n_in).and_then(|b| b.output) else { return };
        let Some(&ft) = self.bind_tys.get(&jf.0) else { return };
        let TyKind::Closure(def, args) = self.body.tys.kind(ft) else { return };
        let Some(c_out) = p.gx.closures.get(&def).map(|c| c.output) else { return };
        let mut outs: Vec<BoundSlot> = Vec::new();
        self.bound_slots(out_t, c_out, univ, &mut outs);
        let target = |k: BoundSlot| match k {
            BoundSlot::Tie(u) => Some(u),
            BoundSlot::Hr => Some(0),
            BoundSlot::Free | BoundSlot::Param { .. } => None,
        };
        if outs.iter().all(|&k| target(k).is_none()) {
            return;
        }
        let caps = binds.get(&jf.0).cloned().unwrap_or_default();
        let mut roles = Vec::new();
        closure_roles(&mut self.sc, def, args, &mut roles);
        let fe = self.fn_ends(def);
        match self.closure_reqs(def, &roles) {
            Some(reqs) => {
                let vars = self.closure_args.get(&def).cloned().unwrap_or_default();
                for &(x, y) in reqs.iter() {
                    let End::Out(k) = y else { continue };
                    let Some(u) = outs.get(k as usize).and_then(|&k| target(k)) else { continue };
                    let from = match x {
                        End::Cap(i) => caps.get(i as usize),
                        End::Arg(j) => vars.get(j as usize),
                        End::Fn(k) => fe.get(k as usize).and_then(|u| u.as_ref()),
                        End::Static | End::Out(_) => None,
                    };
                    if let Some(&v) = from {
                        self.edge(v, u);
                    }
                }
            }
            None => {
                let us: Vec<u32> = outs.iter().filter_map(|&k| target(k)).collect();
                for (i, &(src, _)) in roles.iter().enumerate() {
                    if src && let Some(&v) = caps.get(i) {
                        for &u in &us {
                            self.edge(v, u);
                        }
                    }
                }
            }
        }
    }

    /// A closure passed for `F: Fn*(..) -> O` where `O` holds a callee
    /// type param (`Option::map`'s `FnOnce(T) -> U`): per slot of the
    /// closure's output, what its body returns of its captured and free
    /// argument slots (`closure_reqs`) flows into `O`'s instantiation at
    /// the call, so `U`'s slots in the result get only that (`Some(s).map(
    /// |st| (st, "x"))` keeps the `'static` slot free of `s`), and
    /// `output_tied` skips the call's every-source rule for it. When the
    /// output does not pair, or the body does not solve, every source of
    /// the closure flows into the result `dv`.
    fn flow_closure_output(&mut self, trait_args: ArgsId, binds: &FxMap<u32, Vec<u32>>, sig: &RegionSig, univ: &[u32], dv: &[u32]) {
        let p = self.p;
        let targs: Vec<GenericArg> = p.tys.args(trait_args).to_vec();
        let (Some(self_t), Some(tuple)) = (targs.first().and_then(|g| g.as_ty()), targs.get(1).and_then(|g| g.as_ty())) else { return };
        let (TyKind::Param(jf), TyKind::Tuple(ts)) = (p.tys.kind(self_t), p.tys.kind(tuple)) else { return };
        let n_in = p.tys.tys_of(ts).len();
        let Some(out_t) = sig.fn_bounds.iter().find(|b| b.param == jf.0 && b.inputs.len() == n_in).and_then(|b| b.output) else { return };
        if !p.tys.flags(out_t).contains_param() {
            return;
        }
        let Some(&ft) = self.bind_tys.get(&jf.0) else { return };
        let TyKind::Closure(def, args) = self.body.tys.kind(ft) else { return };
        let Some(c_out) = p.gx.closures.get(&def).map(|c| c.output) else { return };
        let caps = binds.get(&jf.0).cloned().unwrap_or_default();
        let mut roles = Vec::new();
        closure_roles(&mut self.sc, def, args, &mut roles);
        let mut ps = Vec::new();
        params_in(&p.tys, out_t, &mut ps);
        let mut ob = binds.clone();
        let mut rv = Vec::new();
        let paired = ps.iter().all(|j| binds.contains_key(j))
            && self.inst(out_t, c_out, univ, &mut ob, &mut rv)
            && rv.len() == self.sc.slots(c_out) as usize;
        let fe = self.fn_ends(def);
        match self.closure_reqs(def, &roles) {
            Some(reqs) if paired => {
                let vars = self.closure_args.get(&def).cloned().unwrap_or_default();
                let end = |e: End| match e {
                    End::Static => Some(0),
                    End::Cap(i) => caps.get(i as usize).copied(),
                    End::Arg(j) => vars.get(j as usize).copied(),
                    End::Fn(k) => fe.get(k as usize).copied().flatten(),
                    End::Out(k) => rv.get(k as usize).copied(),
                };
                // `(x, Out(k))`: what slot `k` may hold; `(Out(k), x)`
                // (a `call_out` body): what slot `k` must outlive.
                let mut all = true;
                for &(x, y) in reqs.iter() {
                    if !matches!((x, y), (_, End::Out(_)) | (End::Out(_), _)) {
                        continue;
                    }
                    match (end(x), end(y)) {
                        (Some(a), Some(b)) => self.edge(a, b),
                        _ => all &= !matches!(x, End::Out(_)),
                    }
                }
                if all {
                    self.out_proved.push(def);
                }
            }
            _ => {
                let mut srcs = Vec::new();
                self.closure_sources(ft, &caps, &mut 0, &mut srcs);
                self.flow_all(&srcs, dv);
            }
        }
    }

    /// A type param `F` of this body or a fn item (also behind `&`)
    /// passed for the callee's `G: Fn*(..)` bound: its regioned signature
    /// (`F`'s own bound, the fn's signature) must prove `G`'s, as rustc
    /// selects the `Fn*` impl and equates the signatures (trait args are
    /// invariant). Per pair of places: lifetimes both write are one
    /// region; a binder of the argument (an elided lifetime of `F`'s
    /// bound, a late-bound lifetime of the fn) takes the lifetime `G`
    /// writes there, or stays higher-ranked where `G`'s is (not both); a
    /// higher-ranked `G` input needs a binder (L0735); outputs must agree
    /// the same way (L0733). A fn's early-bound lifetimes are fresh here.
    /// Type params are the call's instantiation. In a closure body a
    /// lifetime of the enclosing fn that `F`'s bound names is its
    /// `OwnSig::fn_lts` universal (L0203 where it has none).
    fn entail_bound(&mut self, trait_args: ArgsId, sig: &RegionSig, univ: &[u32]) {
        let p = self.p;
        let targs: Vec<GenericArg> = p.tys.args(trait_args).to_vec();
        let (Some(self_t), Some(tuple)) = (targs.first().and_then(|g| g.as_ty()), targs.get(1).and_then(|g| g.as_ty())) else { return };
        let (TyKind::Param(jg), TyKind::Tuple(ts)) = (p.tys.kind(self_t), p.tys.kind(tuple)) else { return };
        let n_in = p.tys.tys_of(ts).len();
        let Some(g) = sig.fn_bounds.iter().find(|b| b.param == jg.0 && b.inputs.len() == n_in).cloned() else { return };
        let Some(&ft) = self.bind_tys.get(&jg.0) else { return };
        let Some(src) = self.source_fn_sig(ft, n_in) else { return };
        if src.is_none() && self.lang_method_general(ft, &g.inputs, g.output) {
            return;
        }
        let Some((inputs, output, item)) = src else { return self.unproved_bound(&g) };
        let mut ins: Vec<(Region, Region)> = Vec::new();
        let mut outs: Vec<(Region, Region)> = Vec::new();
        let paired = g.inputs.iter().zip(&inputs).all(|(&a, &b)| region_pairs(&p.tys, a, b, &mut ins))
            && match (g.output, output) {
                (Some(a), Some(b)) => region_pairs(&p.tys, a, b, &mut outs),
                (None, None) => true,
                // No output is `()`: it pairs with an output without regions.
                (Some(t), None) | (None, Some(t)) => {
                    let mut rs = Vec::new();
                    regions_of(&p.tys, t, &mut rs);
                    rs.is_empty()
                }
            };
        if !paired {
            return self.unproved_bound(&g);
        }
        let mut sides = FnSides::new(item.clone());
        if item.is_none() && self.own.closure && ins.iter().chain(&outs).any(|&(_, b)| matches!(b, Region::Param(_))) {
            let lts = self.own.fn_lts.clone();
            if ins.iter().chain(&outs).any(|&(_, b)| matches!(b, Region::Param(k) if lts.get(k as usize).copied().flatten().is_none())) {
                return self.closure_param_bound_cut();
            }
            sides.fn_lts = Some(lts);
        }
        let gside = |r: Region, n: &mut u32, out: bool| match r {
            Region::Static => Side::Tie(0),
            Region::Param(k) => univ.get(k as usize).map_or(Side::Free, |&u| Side::Tie(u)),
            Region::Bound(_) if out => Side::Binder(0),
            Region::Bound(_) => {
                *n += 1;
                Side::Binder(*n - 1)
            }
            _ => Side::Free,
        };
        let mut gn = 0u32;
        let ins: Vec<(Side, Side)> = ins.iter().map(|&(a, b)| (gside(a, &mut gn, false), sides.side(self, b, false))).collect();
        let outs: Vec<(Side, Side)> = outs.iter().map(|&(a, b)| (gside(a, &mut gn, true), sides.side(self, b, true))).collect();
        // The argument's output regions in the places of `G`'s output type
        // params (`F: Fn(&u8) -> T`): the call fixes `T` outside `G`'s
        // binder, so none may be a binder `G`'s input takes (rustc:
        // "implementation of `FnOnce` is not general enough").
        let mut covered = Vec::new();
        if let (Some(a), Some(b)) = (g.output, output) {
            param_covered_regions(&p.tys, a, b, &mut covered);
        }
        let covered: Vec<Side> = covered.into_iter().map(|b| sides.side(self, b, true)).collect();
        self.match_fn_sides(&ins, &outs, &covered);
    }

    /// A fn pointer passed for the callee's `G: Fn*` bound (W-BORROW3):
    /// its signature must match the bound's once its binders are picked
    /// (rustc's trait matching, `fnptr::ptr_matches`): L0735 when it is
    /// not general enough. A bound over type params (`Fn(T) -> R`) pairs
    /// no slots here; `flow_bound_inputs` relates those.
    fn entail_bound_ptr(&mut self, trait_args: ArgsId, binds: &FxMap<u32, Vec<u32>>, sig: &RegionSig, univ: &[u32]) {
        let p = self.p;
        let targs: Vec<GenericArg> = p.tys.args(trait_args).to_vec();
        let (Some(self_t), Some(tuple)) = (targs.first().and_then(|g| g.as_ty()), targs.get(1).and_then(|g| g.as_ty())) else { return };
        let (TyKind::Param(jg), TyKind::Tuple(ts)) = (p.tys.kind(self_t), p.tys.kind(tuple)) else { return };
        let n_in = p.tys.tys_of(ts).len();
        let Some(g) = sig.fn_bounds.iter().find(|b| b.param == jg.0 && b.inputs.len() == n_in).cloned() else { return };
        let Some(&ft) = self.bind_tys.get(&jg.0) else { return };
        let TyKind::FnPtr(fs) = self.body.tys.kind(ft) else { return };
        let fs = self.body.tys.sig(fs).value;
        let ins: Vec<Ty> = self.body.tys.tys_of(fs.inputs).to_vec();
        let Some(dst) = self.bound_nodes(&g, &ins, fs.output, univ) else { return };
        let free = if fs.free_slots != 0 { binds.get(&jg.0).and_then(|v| v.first().copied()) } else { None };
        if !self.ptr_matches(ft, free, &dst) {
            self.not_general_enough_param();
        }
    }

    /// A source that is not a closure (a fn item, a constructor, a fn
    /// pointer, a type param) passed for the callee's `G: Fn*(..) -> R`
    /// bound: what it returns may hold what it takes, so the regions bound
    /// to the type params in `G`'s inputs, and the lifetimes `G` writes
    /// there, flow into the regions bound to the type params in its output
    /// (rustc instantiates the source's signature with the call's types;
    /// a closure's sources flow through `closure_sources`).
    fn flow_bound_inputs(&mut self, trait_args: ArgsId, binds: &FxMap<u32, Vec<u32>>, sig: &RegionSig, univ: &[u32]) {
        let p = self.p;
        let targs: Vec<GenericArg> = p.tys.args(trait_args).to_vec();
        let (Some(self_t), Some(tuple)) = (targs.first().and_then(|g| g.as_ty()), targs.get(1).and_then(|g| g.as_ty())) else { return };
        let (TyKind::Param(jg), TyKind::Tuple(ts)) = (p.tys.kind(self_t), p.tys.kind(tuple)) else { return };
        let n_in = p.tys.tys_of(ts).len();
        let Some(&ft) = self.bind_tys.get(&jg.0) else { return };
        let mut t = ft;
        while let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
            t = inner;
        }
        if matches!(self.body.tys.kind(t), TyKind::Closure(..)) {
            return;
        }
        let Some(g) = sig.fn_bounds.iter().find(|b| b.param == jg.0 && b.inputs.len() == n_in) else { return };
        let Some(out) = g.output else { return };
        // Bare type params in and out (`Fn(T, U) -> R`): the source's own
        // signature, where it has one, says exactly which input reaches R.
        let bare = |t: Ty| match p.tys.kind(t) {
            TyKind::Param(j) => Some(j.0),
            _ => None,
        };
        if let (Some(ins), Some(r)) = (g.inputs.iter().map(|&t| bare(t)).collect::<Option<Vec<u32>>>(), bare(out))
            && self.flow_by_signature(t, &ins, r, binds)
        {
            return;
        }
        // A source whose output holds only `'static` data where `G`'s output
        // has its type params (`fn f(v: &V) -> &'static [u8]` for `Fn(&V) ->
        // T`) returns nothing of what it takes.
        if let Some(Some((_, Some(s_out), _))) = self.source_fn_sig(t, n_in)
            && static_at_params(&p.tys, out, s_out)
        {
            return;
        }
        let (mut outs, mut ins) = (Vec::new(), Vec::new());
        type_params_in(&p.tys, out, &mut outs);
        let dsts: Vec<u32> = outs.iter().filter_map(|j| binds.get(j)).flatten().copied().collect();
        if dsts.is_empty() {
            return;
        }
        let mut srcs: Vec<u32> = Vec::new();
        for &it in &g.inputs {
            type_params_in(&p.tys, it, &mut ins);
            let mut rs = Vec::new();
            regions_of(&p.tys, it, &mut rs);
            srcs.extend(rs.into_iter().filter_map(|r| match r {
                Region::Param(k) => univ.get(k as usize).copied(),
                _ => None,
            }));
        }
        srcs.extend(ins.iter().filter_map(|j| binds.get(j)).flatten().copied());
        self.flow_all(&srcs, &dsts);
    }

    /// `flow_bound_inputs` through the source's own regioned signature
    /// (a fn item's, or a type param's `Fn` bound outside a closure body),
    /// instantiated at this use: its universals are fresh vars, its
    /// late-bound regions one var of the use, and each input `ins[i]` and
    /// the output `out` take exactly the regions of the type params the
    /// call binds there. False when there is no such signature or it does
    /// not pair (the conservative flow then).
    fn flow_by_signature(&mut self, src: Ty, ins: &[u32], out: u32, binds: &FxMap<u32, Vec<u32>>) -> bool {
        let p = self.p;
        let root = root_fn(p, self.body.fn_id);
        let (s_ins, s_out, univ): (Vec<Ty>, Ty, Vec<u32>) = match self.body.tys.kind(src) {
            TyKind::FnDef(def, args) if def == crate::ty::prim_fn_def() => return self.flow_prim_item(args, ins, out, binds),
            TyKind::FnDef(def, _) => {
                let Some(fs) = p.local_def(def.hash).and_then(|l| p.regions.body_sig(p, l)) else { return false };
                let univ: Vec<u32> = (0..fs.n_univ).map(|_| self.fresh()).collect();
                (fs.params.clone(), fs.ret, univ)
            }
            TyKind::Param(jf) if !self.own.closure => {
                let Some(rs) = p.regions.own_body_sig(p, root) else { return false };
                let Some(f) = rs.fn_bounds.iter().find(|b| b.param == jf.0 && b.inputs.len() == ins.len()) else { return false };
                let Some(o) = f.output else { return false };
                (f.inputs.clone(), o, (1..=rs.n_univ).collect())
            }
            _ => return false,
        };
        if s_ins.len() != ins.len() {
            return false;
        }
        let bv = self.fresh();
        self.bound_var = Some(bv);
        let mut ok = true;
        // The source's own type params (`id::<T>`'s T) bind once for all
        // inputs and the output, so `fn id<T>(x: T) -> T` carries its
        // input's regions to its output. `inst` records their types in
        // `bind_tys` under the source's param indices, which are not the
        // callee's: those entries are undone after.
        let saved = self.bind_tys.clone();
        let mut own = FxMap::default();
        for (&st, &j) in s_ins.iter().zip(ins).chain(std::iter::once((&s_out, &out))) {
            let (Some(&at), Some(bvs)) = (saved.get(&j), binds.get(&j)) else {
                ok = false;
                break;
            };
            let mut pv = Vec::new();
            if !self.inst(st, at, &univ, &mut own, &mut pv) || pv.len() != bvs.len() {
                ok = false;
                break;
            }
            for (&a, &b) in pv.iter().zip(bvs) {
                self.edge(a, b);
                self.edge(b, a);
            }
        }
        self.bound_var = None;
        self.bind_tys = saved;
        ok
    }

    /// `flow_by_signature` for a primitive builtin method item
    /// (`check::prim_item_value`): `PoisonError::into_inner` returns its
    /// error's value, so the output's regions are exactly the input's
    /// (`unwrap_or_else(PoisonError::into_inner)` keeps a guard's borrow
    /// out of the `'static` object lifetime it guards). False for the
    /// others (the conservative flow).
    fn flow_prim_item(&mut self, args: ArgsId, ins: &[u32], out: u32, binds: &FxMap<u32, Vec<u32>>) -> bool {
        let code = match self.body.tys.args(args).get(2) {
            Some(GenericArg::Const(c)) => match self.body.tys.const_kind(*c) {
                crate::ty::ConstKind::Int(v) => v as u32,
                _ => return false,
            },
            _ => return false,
        };
        if crate::check::prim_builtin_of_code(code) != Some(crate::check::Builtin::Sync(crate::check::sync::SyncOp::PoisonIntoInner)) {
            return false;
        }
        let ([e], Some(dst)) = (ins, binds.get(&out)) else { return false };
        let Some(src) = binds.get(e) else { return false };
        if src.len() != dst.len() {
            return false;
        }
        for (&a, &b) in src.clone().iter().zip(&dst.clone()) {
            self.edge(a, b);
            self.edge(b, a);
        }
        true
    }

    /// The regioned signature of a type param `F` of this body's fn (its
    /// `Fn` bound with `n_in` inputs) or of a fn item (also behind `&`),
    /// passed where a `Fn*` bound or a `dyn Fn` is expected: inputs,
    /// output, and for a fn item which of its lifetimes are early-bound.
    /// `Some(None)` for such a source without a signature that pairs;
    /// None for any other type (closures have their own rules).
    #[allow(clippy::type_complexity)]
    fn source_fn_sig(&self, t: Ty, n_in: usize) -> Option<Option<(Vec<Ty>, Option<Ty>, Option<Vec<bool>>)>> {
        let p = self.p;
        let mut t = t;
        while let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
            t = inner;
        }
        Some(match self.body.tys.kind(t) {
            TyKind::Param(jf) => p
                .regions
                .own_body_sig(p, root_fn(p, self.body.fn_id))
                .and_then(|s| s.fn_bounds.iter().find(|b| b.param == jf.0 && b.inputs.len() == n_in).cloned())
                .map(|f| (f.inputs, f.output, None)),
            // A trait method by path (`Clone::clone`), or an impl method
            // with no signature of its own (a derived one): the trait's
            // signature, which every impl satisfies (`impl_contract`).
            TyKind::FnDef(def, _) => match p
                .local_def(def.hash)
                .and_then(|l| p.regions.body_sig(p, l).or_else(|| p.regions.trait_methods.get(&impl_trait_method(p, l)?)))
                .or_else(|| p.regions.trait_methods.get(&def))
            {
                Some(fs) if fs.params.len() == n_in => Some((fs.params.clone(), Some(fs.ret), Some(fs.early.clone()))),
                _ => None,
            },
            _ => return None,
        })
    }

    /// `entail_bound` for a coercion to `dyn Fn*(I..) -> O` (`dyn_fn_sig`)
    /// with places `pin` and `pout` (`dyn_positions`): every late-bound
    /// input place there is its own binder, every late-bound output place
    /// the one input place's, and every other place the var it holds. A
    /// source whose signature does not pair takes the conservative answer
    /// (L0733 when the target has regions).
    fn entail_dyn(&mut self, src: Ty, ins: &[Ty], pin: &[Pos], pout: &[Pos]) {
        let p = self.p;
        let Some(src) = self.source_fn_sig(src, ins.len()) else { return };
        let mut n_slots: Vec<usize> = Vec::with_capacity(ins.len());
        for &t in ins {
            let mut rs = Vec::new();
            self.sugar_regions(t, &mut rs);
            n_slots.push(rs.len());
        }
        let n_out = pout.len();
        let unproved = |this: &mut Self| {
            if n_slots.iter().sum::<usize>() + n_out > 0 {
                this.bound_mismatch();
            }
        };
        let Some((f_ins, f_out, item)) = src else { return unproved(self) };
        let mut f_in_regions: Vec<Region> = Vec::new();
        for (&t, &n) in f_ins.iter().zip(&n_slots) {
            let mut rs = Vec::new();
            sig_slot_regions(p, &p.tys, t, &mut rs);
            if rs.len() != n {
                return unproved(self);
            }
            f_in_regions.extend(rs);
        }
        let mut f_out_regions: Vec<Region> = Vec::new();
        if let Some(o) = f_out {
            sig_slot_regions(p, &p.tys, o, &mut f_out_regions);
        }
        // The target's places: each late-bound input its own binder, a
        // late-bound output the one late-bound input's, any other the var
        // it holds (`'static` is var 0).
        let tside = |i: usize, p: Pos| match p {
            Pos::Var(v) => Side::Tie(v),
            Pos::Late => Side::Binder(i as u32),
        };
        let lates: Vec<usize> = pin.iter().enumerate().filter(|(_, p)| **p == Pos::Late).map(|(i, _)| i).collect();
        let t_outs: Option<Vec<Side>> = pout
            .iter()
            .map(|&p| match (p, &lates[..]) {
                (Pos::Var(v), _) => Some(Side::Tie(v)),
                (Pos::Late, [one]) => Some(Side::Binder(*one as u32)),
                _ => None,
            })
            .collect();
        let Some(t_outs) = t_outs else { return unproved(self) };
        if f_out_regions.len() != n_out || pin.len() != f_in_regions.len() {
            return unproved(self);
        }
        let mut sides = FnSides::new(item.clone());
        if item.is_none() && self.own.closure && f_in_regions.iter().chain(&f_out_regions).any(|r| matches!(r, Region::Param(_))) {
            let lts = self.own.fn_lts.clone();
            if f_in_regions.iter().chain(&f_out_regions).any(|r| matches!(r, Region::Param(k) if lts.get(*k as usize).copied().flatten().is_none())) {
                return self.closure_param_bound_cut();
            }
            sides.fn_lts = Some(lts);
        }
        let ins: Vec<(Side, Side)> = pin.iter().zip(&f_in_regions).enumerate().map(|(i, (&t, &r))| (tside(i, t), sides.side(self, r, false))).collect();
        let outs: Vec<(Side, Side)> = t_outs.into_iter().zip(&f_out_regions).map(|(t, &r)| (t, sides.side(self, r, true))).collect();
        self.match_fn_sides(&ins, &outs, &[]);
    }

    /// L0203: inside a closure, a type param whose `Fn` bound names a
    /// lifetime of the enclosing fn, passed on (the closure body cannot
    /// name that lifetime).
    fn closure_param_bound_cut(&mut self) {
        self.errs.push(Diag::new(
            "L0203",
            self.span,
            "a type param whose `Fn` bound names a lifetime of the enclosing fn, passed to a generic fn inside a closure, is not supported yet",
            "Make the call outside the closure, or pass a closure written in place.",
        ));
    }

    /// Proves a target `Fn` signature (the left side of each pair) from a
    /// source's (the right), place by place in the inputs, then the
    /// outputs. A source binder takes either one target binder, where the
    /// target is higher-ranked, or the one lifetime the target writes there
    /// (trait args are invariant); a target binder needs a source binder
    /// (L0735); outputs agree the same way (L0733).
    fn match_fn_sides(&mut self, ins: &[(Side, Side)], outs: &[(Side, Side)], covered: &[Side]) {
        let mut takes: FxMap<u32, u32> = FxMap::default();
        let mut inst: FxMap<u32, u32> = FxMap::default();
        for &(ga, fb) in ins {
            match (ga, fb) {
                (Side::Binder(gi), Side::Binder(k)) => {
                    if inst.contains_key(&k) || takes.get(&k).is_some_and(|&gj| gj != gi) {
                        return self.not_general_enough_param();
                    }
                    takes.insert(k, gi);
                }
                (Side::Binder(_), Side::Tie(_)) => return self.not_general_enough_param(),
                (Side::Tie(u), Side::Binder(k)) => {
                    if takes.contains_key(&k) {
                        return self.not_general_enough_param();
                    }
                    match inst.get(&k) {
                        Some(&v) => {
                            self.edge(u, v);
                            self.edge(v, u);
                        }
                        None => {
                            inst.insert(k, u);
                        }
                    }
                }
                (Side::Tie(u), Side::Tie(v)) => {
                    self.edge(u, v);
                    self.edge(v, u);
                }
                _ => {}
            }
        }
        if covered.iter().any(|c| matches!(c, Side::Binder(k) if takes.contains_key(k))) {
            return self.bound_mismatch();
        }
        for &(ga, fb) in outs {
            match (ga, fb) {
                (Side::Binder(gi), Side::Binder(k)) if takes.get(&k) == Some(&gi) => {}
                (Side::Tie(u), Side::Binder(k)) if inst.contains_key(&k) => {
                    let v = inst[&k];
                    self.edge(u, v);
                    self.edge(v, u);
                }
                (Side::Tie(u), Side::Tie(v)) => {
                    self.edge(u, v);
                    self.edge(v, u);
                }
                (Side::Free, _) | (_, Side::Free) => {}
                _ => return self.bound_mismatch(),
            }
        }
    }

    /// A std trait method by path (`Clone::clone`, `ToString::to_string`)
    /// or a primitive's builtin method item (`str::len`, `<[T]>::len`)
    /// has no region signature here. Its lifetimes are elided, so where
    /// each input of the bound (regioned `ins -> out`) holds only an
    /// outer reference and the output no region, it is `for<'r> fn(&'r
    /// Self) -> R`: as general as any bound of that shape.
    fn lang_method_general(&mut self, ft: Ty, ins: &[Ty], out: Option<Ty>) -> bool {
        let p = self.p;
        let mut t = ft;
        while let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
            t = inner;
        }
        let TyKind::FnDef(def, _) = self.body.tys.kind(t) else { return false };
        let prim_item = def == crate::ty::prim_fn_def();
        if p.local_def(def.hash).is_some() || p.regions.trait_methods.contains_key(&def) || (p.gx.index.trait_of_method(def).is_none() && !prim_item) {
            return false;
        }
        // No region inside: none written, and a type param the call binds
        // to a type with no slots.
        let no_regions = |this: &mut Self, t: Ty| -> bool {
            let mut rs = Vec::new();
            regions_of(&p.tys, t, &mut rs);
            rs.is_empty() && no_open_parts(this, t)
        };
        fn no_open_parts(this: &mut Builder<'_, '_>, t: Ty) -> bool {
            let tys = &this.p.tys;
            match tys.kind(t) {
                TyKind::Param(j) => match this.bind_tys.get(&j.0).copied() {
                    Some(b) => this.sc.slots(b) == 0,
                    None => false,
                },
                TyKind::Projection(..) | TyKind::Dyn(..) | TyKind::Opaque(..) => false,
                TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => no_open_parts(this, e),
                TyKind::Tuple(ts) => tys.tys_of(ts).to_vec().into_iter().all(|e| no_open_parts(this, e)),
                TyKind::Adt(_, a) => tys.args(a).to_vec().into_iter().all(|g| g.as_ty().is_none_or(|e| no_open_parts(this, e))),
                _ => true,
            }
        }
        let outer_only = |this: &mut Self, t: Ty| match p.tys.kind(t) {
            TyKind::Ref(_, _, inner) => no_regions(this, inner),
            _ => no_regions(this, t),
        };
        ins.iter().all(|&t| outer_only(self, t)) && out.is_none_or(|o| no_regions(self, o))
    }

    /// An argument whose signature does not pair with the callee's `G:
    /// Fn*` bound (check selected the impl some other way): only a bound
    /// without lifetimes is proved (L0733).
    fn unproved_bound(&mut self, g: &FnBound) {
        let mut rs = Vec::new();
        for &it in &g.inputs {
            regions_of(&self.p.tys, it, &mut rs);
        }
        if let Some(o) = g.output {
            regions_of(&self.p.tys, o, &mut rs);
        }
        if rs.into_iter().any(|r| matches!(r, Region::Param(_) | Region::Static | Region::Bound(_))) {
            self.bound_mismatch();
        }
    }

    /// L0735 for a type param's `Fn` bound or a fn item that fixes an
    /// argument lifetime where the callee's bound is higher-ranked (rustc
    /// E0277, "not general enough").
    fn not_general_enough_param(&mut self) {
        self.errs.push(Diag::new(
            "L0735",
            self.span,
            "this argument is not general enough for the callee's `Fn` bound: it fixes an argument lifetime, but the callee may pass a borrow of its own data",
            "Give that argument an elided lifetime (`F: Fn(&T)`, `fn f(x: &T)`).",
        ));
    }

    /// L0733 for a type param's `Fn` bound or a fn item whose signature
    /// does not prove the callee's bound (rustc E0308).
    fn bound_mismatch(&mut self) {
        self.errs.push(Diag::new(
            "L0733",
            self.span,
            "lifetime may not live long enough: this argument's signature does not prove the callee's `Fn` bound (their lifetimes differ)",
            "Write the same lifetimes in both signatures.",
        ));
    }

    /// Per slot of a closure input's erased type `t`, what the bound's
    /// input type `tmpl` (over the callee's params; regioned when the
    /// signature has it) makes of it: a type param or projection is the
    /// call's instantiation (free; a param's slots name the param); an
    /// elided lifetime (`Region::Bound`, or any region in an erased bound)
    /// is higher-ranked; `'static` and the callee's lifetime `k` tie the
    /// slot to `'static` and `univ[k]`.
    fn bound_slots(&mut self, tmpl: Ty, t: Ty, univ: &[u32], out: &mut Vec<BoundSlot>) {
        let p = self.p;
        let n = self.sc.slots(t) as usize;
        let kind = |r: Region| match r {
            Region::Static => BoundSlot::Tie(0),
            Region::Param(k) => univ.get(k as usize).map_or(BoundSlot::Hr, |&u| BoundSlot::Tie(u)),
            _ => BoundSlot::Hr,
        };
        match (p.tys.kind(tmpl), self.body.tys.kind(t)) {
            (TyKind::Param(j), _) => out.extend((0..n as u32).map(|q| BoundSlot::Param { j: j.0, q, n: n as u32 })),
            (TyKind::Projection(..), _) => out.extend(std::iter::repeat_n(BoundSlot::Free, n)),
            (TyKind::Ref(r, _, ti), TyKind::Ref(er, _, ei)) => {
                if !bound(er) {
                    out.push(if bound(r) { BoundSlot::Hr } else { kind(r) });
                }
                self.bound_slots(ti, ei, univ, out);
            }
            (TyKind::Adt(_, ta), TyKind::Adt(_, ea)) => {
                let lts: Vec<Region> = p.tys.args(ta).iter().filter_map(|g| if let GenericArg::Lifetime(r) = g && *r != crate::ty::DYN_LATE { Some(*r) } else { None }).collect();
                let nr = adt_regions(p, &self.body.tys, t) as usize;
                for i in 0..nr {
                    out.push(lts.get(i).map_or(BoundSlot::Hr, |&r| kind(r)));
                }
                let ta_tys: Vec<Ty> = p.tys.args(ta).iter().filter_map(|g| g.as_ty()).collect();
                let ea_tys: Vec<Ty> = self.body.tys.args(ea).iter().filter_map(|g| g.as_ty()).collect();
                if ta_tys.len() == ea_tys.len() {
                    for (a, b) in ta_tys.into_iter().zip(ea_tys) {
                        self.bound_slots(a, b, univ, out);
                    }
                } else {
                    out.extend(std::iter::repeat_n(BoundSlot::Hr, n - nr));
                }
            }
            (TyKind::Tuple(ta), TyKind::Tuple(ea)) if p.tys.tys_of(ta).len() == self.body.tys.tys_of(ea).len() => {
                let pairs: Vec<(Ty, Ty)> = p.tys.tys_of(ta).iter().copied().zip(self.body.tys.tys_of(ea).iter().copied()).collect();
                for (a, b) in pairs {
                    self.bound_slots(a, b, univ, out);
                }
            }
            (TyKind::Array(a, _) | TyKind::Slice(a), TyKind::Array(b, _) | TyKind::Slice(b)) => self.bound_slots(a, b, univ, out),
            (TyKind::Dyn(_, r), TyKind::Dyn(_, er)) => {
                let start = out.len();
                if !bound(er) {
                    out.push(if bound(r) { BoundSlot::Hr } else { kind(r) });
                }
                let (ta, ea) = (dyn_arg_tys(&p.tys, tmpl), dyn_arg_tys(&self.body.tys, t));
                if ta.len() == ea.len() {
                    for (a, b) in ta.into_iter().zip(ea) {
                        self.bound_slots(a, b, univ, out);
                    }
                }
                let k = out.len() - start;
                out.extend(std::iter::repeat_n(BoundSlot::Hr, n.saturating_sub(k)));
                out.truncate(start + n);
            }
            _ => out.extend(std::iter::repeat_n(BoundSlot::Hr, n)),
        }
    }

    /// L0735: a closure whose argument lifetime is free (inferred, or named
    /// by an annotation) where the callee's bound is higher-ranked.
    fn not_general_enough(&mut self) {
        self.errs.push(Diag::new(
            "L0735",
            self.span,
            "this closure is not general enough for the bound it is passed to: its argument lifetime is fixed, but the callee may pass a borrow of its own data",
            "Annotate the parameter with an elided lifetime (`|x: &T|`), or pass the closure where it is written.",
        ));
    }

    /// The `X: 'static` where-clauses of the impls of `trait_def` whose Self
    /// pattern matches `actual` (laid out in `vars`): each region of the part
    /// `X` matches outlives `'static`.
    fn impl_static_edges(&mut self, trait_def: DefId, actual: Ty, vars: &[u32]) {
        let p = self.p;
        for (id, statics) in p.regions.static_impls(p, trait_def).to_vec() {
            let rec = p.gx.index.get(id);
            let Some(pat) = p.tys.args(rec.trait_ref.args).first().and_then(|g| g.as_ty()) else { continue };
            let mut parts: FxMap<u32, Vec<u32>> = FxMap::default();
            if !self.match_impl_self(pat, actual, vars, &mut 0, &mut parts) {
                continue;
            }
            for k in statics {
                for &v in parts.get(&k).map(|x| x.as_slice()).unwrap_or(&[]) {
                    self.edge(v, 0);
                }
            }
        }
    }

    /// Matches an impl's Self pattern (over its params) against an erased
    /// type whose slots are `vars` from `*at`, collecting each param's
    /// slot vars. False when the shapes differ.
    fn match_impl_self(&mut self, pat: Ty, actual: Ty, vars: &[u32], at: &mut usize, out: &mut FxMap<u32, Vec<u32>>) -> bool {
        let tys = &self.body.tys;
        match (tys.kind(pat), tys.kind(actual)) {
            (TyKind::Param(k), _) => {
                let n = self.sc.slots(actual) as usize;
                out.entry(k.0).or_default().extend(vars.iter().skip(*at).take(n).copied());
                *at += n;
                true
            }
            (TyKind::Ref(_, pm, pi), TyKind::Ref(_, am, ai)) if pm == am => {
                *at += 1;
                self.match_impl_self(pi, ai, vars, at, out)
            }
            (TyKind::Adt(pd, pa), TyKind::Adt(ad, aa)) if pd == ad => {
                *at += adt_regions(self.p, tys, actual) as usize;
                let (xs, ys): (Vec<Ty>, Vec<Ty>) =
                    (tys.args(pa).iter().filter_map(|g| g.as_ty()).collect(), tys.args(aa).iter().filter_map(|g| g.as_ty()).collect());
                xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| self.match_impl_self(x, y, vars, at, out))
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                let (xs, ys) = (tys.tys_of(a).to_vec(), tys.tys_of(b).to_vec());
                xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| self.match_impl_self(x, y, vars, at, out))
            }
            (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
                self.match_impl_self(a, b, vars, at, out)
            }
            _ => {
                *at += self.sc.slots(actual) as usize;
                pat == actual
            }
        }
    }

    fn inst_region(&mut self, r: Region, univ: &[u32]) -> u32 {
        match r {
            Region::Static => 0,
            Region::Param(k) => univ.get(k as usize).copied().unwrap_or_else(|| self.fresh()),
            Region::Bound(_) if self.bound_each.is_some() => {
                let v = self.fresh();
                self.bound_each.as_mut().unwrap().push(v);
                v
            }
            Region::Bound(_) if let Some(v) = self.bound_var => v,
            _ => self.fresh(),
        }
    }

    /// The vars of erased type `e` under regioned signature type `r`:
    /// universals map through `univ`, each type param binds once (fresh
    /// vars shared by all its occurrences). Also adds the implied bounds of
    /// `r` (every region inside a reference outlives it) as constraints.
    fn inst(&mut self, r: Ty, e: Ty, univ: &[u32], binds: &mut FxMap<u32, Vec<u32>>, out: &mut Vec<u32>) -> bool {
        let start = out.len();
        let saved = std::mem::replace(&mut self.inst_inv, (false, None));
        let ok = self.inst_walk(r, e, univ, binds, out);
        self.inst_inv = saved;
        if !ok {
            out.truncate(start);
            let n = self.sc.slots(e);
            for _ in 0..n {
                let v = self.fresh();
                out.push(v);
            }
            return false;
        }
        let mut refs: Vec<u32> = Vec::new();
        let vars = out[start..].to_vec();
        self.implied_edges(e, &vars, &mut 0, &mut refs);
        true
    }

    /// The vars of `<T as Deref>::Target` (assoc `a`, args `pa`) at
    /// erased type `e` when `T` is a bound param whose erased type is a
    /// builtin pointer (`&`, `&mut`, Box, Rc, Arc, Cow, a RefCell or lock
    /// guard) or a Vec (`[T]`): the pointee's own vars inside `T`'s,
    /// after the pointer's regions. None for anything else (a user
    /// impl's target).
    fn deref_target_vars(&mut self, a: crate::ty::AssocId, pa: crate::ty::ArgsId, e: Ty, binds: &FxMap<u32, Vec<u32>>) -> Option<Vec<u32>> {
        let p = self.p;
        if a.0 != p.gx.lang.assoc_target {
            return None;
        }
        let Some(GenericArg::Ty(t)) = p.tys.args(pa).first().copied() else { return None };
        let TyKind::Param(j) = p.tys.kind(t) else { return None };
        let (vars, et) = (binds.get(&j.0)?, *self.bind_tys.get(&j.0)?);
        let tys = &self.body.tys;
        let (off, inner) = match tys.kind(et) {
            TyKind::Ref(r, _, inner) => (u32::from(!bound(r)), inner),
            // `Vec<T>` derefs to `[T]`: the same slots as `T`.
            _ if tys.vec_elem(et).is_some_and(|el| matches!(tys.kind(e), TyKind::Slice(x) if x == el)) => (adt_regions(p, tys, et), e),
            _ if tys.smart_elem(et).is_some() || crate::check::collect::cow_arg(tys, et).is_some() => {
                let inner = tys.smart_elem(et).or_else(|| crate::check::collect::cow_arg(tys, et))?;
                // The pointee is the first type arg, after the Adt's regions.
                (adt_regions(p, tys, et), inner)
            }
            _ => return None,
        };
        if inner != e {
            return None;
        }
        let n = self.sc.slots(e);
        vars.get(off as usize..(off + n) as usize).map(|v| v.to_vec())
    }

    /// The vars of `<T as Iterator>::Item` or `<T as IntoIterator>::Item`
    /// (assoc `a`, args `pa`) at erased type `e`, when `T` is a bound param
    /// whose erased type is an iterator `item_slots` reads: its items'
    /// own vars. None for anything else.
    fn iter_item_vars(&mut self, a: crate::ty::AssocId, pa: crate::ty::ArgsId, e: Ty, binds: &FxMap<u32, Vec<u32>>) -> Option<Vec<u32>> {
        let p = self.p;
        if a.0 != p.gx.lang.assoc_item && a.0 != p.gx.lang.assoc_into_item {
            return None;
        }
        let Some(GenericArg::Ty(t)) = p.tys.args(pa).first().copied() else { return None };
        let TyKind::Param(j) = p.tys.kind(t) else { return None };
        let (vars, et) = (binds.get(&j.0)?.clone(), *self.bind_tys.get(&j.0)?);
        let items = self.item_slots(et, &vars)?;
        (items.len() == self.sc.slots(e) as usize).then_some(items)
    }

    fn inst_walk(&mut self, r: Ty, e: Ty, univ: &[u32], binds: &mut FxMap<u32, Vec<u32>>, out: &mut Vec<u32>) -> bool {
        let tys = &self.p.tys;
        let et = &self.body.tys;
        match (tys.kind(r), et.kind(e)) {
            // A late-bound place of a dyn's sugar (`T` against `&u8` in
            // `dyn Fn(T)` from a `dyn Fn(&u8)`, R11) tells nothing of `T`:
            // `T` binds at its other uses. That is a subtyping, so the dyn
            // must sit in a covariant place (rustc E0308 under `&mut`).
            (TyKind::Param(_), _) if et.flags(e).contains_loose_bound() => {
                if self.inst_inv.1 != Some(false) || self.inst_ret {
                    self.dyn_not_general();
                }
                for _ in 0..self.sc.slots(e) {
                    let v = self.fresh();
                    out.push(v);
                }
                true
            }
            (TyKind::Param(j), _) => {
                let n = self.sc.slots(e) as usize;
                match binds.get(&j.0) {
                    Some(v) if v.len() == n => out.extend_from_slice(v),
                    Some(_) => return false,
                    None => {
                        let v: Vec<u32> = (0..n).map(|_| self.fresh()).collect();
                        out.extend_from_slice(&v);
                        binds.insert(j.0, v);
                        self.bind_tys.insert(j.0, e);
                    }
                }
                true
            }
            (TyKind::Projection(..), _) if self.proj.is_some() => {
                let n = self.sc.slots(e) as usize;
                let have = self.proj.as_ref().and_then(|m| m.get(&r)).cloned();
                match have {
                    Some(v) if v.len() == n => out.extend_from_slice(&v),
                    Some(_) => return false,
                    None => {
                        let v: Vec<u32> = (0..n).map(|_| self.fresh()).collect();
                        out.extend_from_slice(&v);
                        if let Some(m) = self.proj.as_mut() {
                            m.insert(r, v);
                        }
                    }
                }
                true
            }
            // A projection over the callee's bound type params outside a
            // trait view (`&'a <T as Deref>::Target` in core's generic
            // `Option::as_deref`): its regions can only be some of the
            // params' (an impl's params are fixed by its Self type) or
            // `'static`. In a covariant place of the return, every param
            // region outlives its vars (the result lives no longer than
            // the shortest); in an argument or an invariant place they
            // are all equal. Neither is looser than rustc's normalized
            // signature, and the reference's own region stays the
            // signature's (the opaque rule tied it to a dyn's `'static`).
            (TyKind::Projection(a, pa), _) => {
                // `<T as Deref>::Target` over a builtin pointer `T` is its
                // pointee, region for region: share those vars.
                if let Some(v) = self.deref_target_vars(a, pa, e, binds) {
                    out.extend_from_slice(&v);
                    return true;
                }
                // `<I as Iterator>::Item` (or `IntoIterator::Item`) over an
                // iterator type the call binds `I` to: those items' own vars
                // (`I = &mut slice::Iter<'w, T>` gives `&'w T`, not the
                // reborrow's region).
                if let Some(v) = self.iter_item_vars(a, pa, e, binds) {
                    out.extend_from_slice(&v);
                    return true;
                }
                let mut src = Vec::new();
                for g in tys.args(pa).to_vec() {
                    match g.as_ty().map(|t| tys.kind(t)) {
                        Some(TyKind::Param(j)) => match binds.get(&j.0) {
                            Some(v) => src.extend_from_slice(v),
                            None => return false,
                        },
                        Some(_) => return false,
                        None => {}
                    }
                }
                // With no param regions bound (`S` with `Out = &'static
                // str`), the projection's regions can only be `'static`:
                // fresh vars no argument loan reaches.
                let n = self.sc.slots(e) as usize;
                let v: Vec<u32> = (0..n).map(|_| self.fresh()).collect();
                if self.inst_ret && !self.inst_inv.0 {
                    self.flow_all(&src, &v);
                } else {
                    self.equate_all(&src, &v);
                }
                out.extend_from_slice(&v);
                true
            }
            (TyKind::Ref(rr, rm, ri), TyKind::Ref(er, em, ei)) if rm == em => {
                if bound(rr) != bound(er) {
                    return false;
                }
                if !bound(er) {
                    let v = self.inst_region(rr, univ);
                    out.push(v);
                }
                let saved = self.inst_inv;
                self.inst_inv.0 |= rm.is_mut();
                let ok = self.inst_walk(ri, ei, univ, binds, out);
                self.inst_inv = saved;
                ok
            }
            (TyKind::Adt(rd, ra), TyKind::Adt(ed, ea)) if rd == ed => {
                let lts: Vec<Region> = tys.args(ra).iter().filter_map(|g| if let GenericArg::Lifetime(r) = g && *r != crate::ty::DYN_LATE { Some(*r) } else { None }).collect();
                for k in 0..adt_regions(self.p, et, e) as usize {
                    let v = match lts.get(k) {
                        Some(&r) => self.inst_region(r, univ),
                        None => self.fresh(),
                    };
                    out.push(v);
                }
                let rargs: Vec<Ty> = tys.args(ra).iter().filter_map(|g| g.as_ty()).collect();
                let ej: Vec<(usize, Ty)> = et.args(ea).iter().enumerate().filter_map(|(j, g)| g.as_ty().map(|t| (j, t))).collect();
                rargs.len() == ej.len()
                    && rargs.into_iter().zip(ej).all(|(x, (j, y))| {
                        let saved = self.inst_inv;
                        self.inst_inv.0 |= self.p.regions.adts(self.p).arg_modes(self.p, ed, j).0 != Variance::Co;
                        let ok = self.inst_walk(x, y, univ, binds, out);
                        self.inst_inv = saved;
                        ok
                    })
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                let (xs, ys) = (tys.tys_of(a).to_vec(), et.tys_of(b).to_vec());
                xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| self.inst_walk(x, y, univ, binds, out))
            }
            (TyKind::RawPtr(m, a), TyKind::RawPtr(_, b)) => {
                let saved = self.inst_inv;
                self.inst_inv.0 |= m.is_mut();
                let ok = self.inst_walk(a, b, univ, binds, out);
                self.inst_inv = saved;
                ok
            }
            (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) => self.inst_walk(a, b, univ, binds, out),
            (TyKind::Dyn(_, rr), TyKind::Dyn(_, er)) => {
                if bound(rr) != bound(er) {
                    return false;
                }
                if !bound(er) {
                    let rr = if crate::check::object::dyn_is_static(self.p, et, e) { Region::Static } else { rr };
                    let v = self.inst_region(rr, univ);
                    out.push(v);
                }
                let (ra, ea) = (dyn_arg_tys(tys, r), dyn_arg_tys(et, e));
                let saved = self.inst_inv;
                // A dyn nested in another's args is in an invariant place.
                self.inst_inv = (true, Some(saved.0 || saved.1.is_some()));
                let ok = ra.len() == ea.len() && ra.into_iter().zip(ea).all(|(x, y)| self.inst_walk(x, y, univ, binds, out));
                self.inst_inv = saved;
                ok
            }
            (TyKind::FnPtr(_), TyKind::FnPtr(_)) if ptr_free(et, e).is_some() => match ptr_free(tys, r) {
                Some(rr) => {
                    let v = self.inst_region(rr, univ);
                    out.push(v);
                    true
                }
                None => false,
            },
            _ => self.sc.slots(e) == 0,
        }
    }

    /// Edges for the `T: 'static` bounds of the user Adts inside a type
    /// (rustc's well-formedness: `S<&'a i32>` with `struct S<T: 'static>`
    /// needs `'a: 'static`): every slot of such an argument outlives
    /// `'static`. `at` walks the slots in order.
    fn static_bound_edges(&mut self, t: Ty, vars: &[u32], at: &mut usize) {
        let tys = &self.body.tys;
        match tys.kind(t) {
            TyKind::Ref(r, _, inner) => {
                *at += usize::from(!bound(r));
                self.static_bound_edges(inner, vars, at);
            }
            TyKind::Adt(def, args) => {
                *at += adt_regions(self.p, tys, t) as usize;
                let statics: Vec<u32> = match self.p.adt_by_def(def).and_then(|a| self.p.gx.adt_generics.get(a.0 as usize)) {
                    Some(g) => g
                        .predicates
                        .iter()
                        .filter_map(|pr| match pr {
                            Predicate::TypeOutlives(x, Region::Static) => match self.p.tys.kind(*x) {
                                TyKind::Param(j) => Some(j.0),
                                _ => None,
                            },
                            _ => None,
                        })
                        .collect(),
                    None => Vec::new(),
                };
                for (j, g) in tys.args(args).to_vec().into_iter().enumerate() {
                    if let GenericArg::Ty(e) = g {
                        let start = *at;
                        self.static_bound_edges(e, vars, at);
                        if statics.contains(&(j as u32)) {
                            for &v in vars.get(start..*at).unwrap_or(&[]) {
                                self.edge(v, 0);
                            }
                        }
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in tys.tys_of(ts).to_vec() {
                    self.static_bound_edges(e, vars, at);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.static_bound_edges(e, vars, at),
            _ => *at += self.sc.slots(t) as usize,
        }
    }

    /// Edges for the implied bounds of a type with slot vars: every slot
    /// inside a reference outlives the reference's region.
    fn implied_edges(&mut self, t: Ty, vars: &[u32], at: &mut usize, refs: &mut Vec<u32>) {
        let tys = &self.body.tys;
        match tys.kind(t) {
            TyKind::Ref(r, _, inner) if bound(r) => self.implied_edges(inner, vars, at, refs),
            TyKind::Ref(_, _, inner) => {
                let Some(&v) = vars.get(*at) else { return };
                for &o in refs.iter() {
                    self.edge(v, o);
                }
                *at += 1;
                refs.push(v);
                self.implied_edges(inner, vars, at, refs);
                refs.pop();
            }
            TyKind::Adt(def, args) => {
                let start = *at;
                for _ in 0..adt_regions(self.p, tys, t) {
                    if let Some(&v) = vars.get(*at) {
                        for &o in refs.iter() {
                            self.edge(v, o);
                        }
                    }
                    *at += 1;
                }
                // The Adt's own outlives facts: every value of the type
                // meets them (`struct H<'a, 'b: 'a>`).
                for &(x, y) in self.p.regions.adt_facts.get(&def).map_or(&[][..], |v| v.as_slice()) {
                    let to = if y == crate::check::generics::STATIC_FACT { Some(0) } else { vars.get(start + y as usize).copied() };
                    if let (Some(&a), Some(b)) = (vars.get(start + x as usize), to) {
                        self.edge(a, b);
                    }
                }
                for g in tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.implied_edges(e, vars, at, refs);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in tys.tys_of(ts).to_vec() {
                    self.implied_edges(e, vars, at, refs);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.implied_edges(e, vars, at, refs),
            TyKind::Closure(_, args) => {
                for e in closure_fields(tys, args) {
                    self.implied_edges(e, vars, at, refs);
                }
            }
            // `&'r (dyn Tr + 'o)` needs `'o: 'r` only; the trait args are
            // well formed on their own (R11).
            TyKind::Dyn(_, r) => {
                if !bound(r) {
                    if let Some(&v) = vars.get(*at) {
                        for &o in refs.iter() {
                            self.edge(v, o);
                        }
                    }
                    *at += 1;
                }
                for e in dyn_arg_tys(tys, t) {
                    self.implied_edges(e, vars, at, &mut Vec::new());
                }
            }
            TyKind::FnPtr(_) => *at += self.sc.slots(t) as usize,
            _ => {}
        }
    }
}

/// True when `ret` is an `impl Trait` type with a `'static` bound.
fn opaque_static_ret(p: &Program, ret: Ty) -> bool {
    let TyKind::Opaque(od, _) = p.tys.kind(ret) else { return false };
    p.gx.opaques.get(&od).is_some_and(|o| o.bounds.iter().any(|b| matches!(b, Predicate::TypeOutlives(_, Region::Static))))
}

/// True for a bare slice or `str` type: as a local's type it is a fat
/// pointer that borrows its base (see `Builder::local_slots`).
fn fat_local(tys: &impl TyIntern, t: Ty) -> bool {
    matches!(tys.kind(t), TyKind::Slice(_) | TyKind::Str)
}

/// The builtins whose result borrows the receiver type's own
/// region (its `'a`), not the `&self` loan (see
/// `Builder::call_own_region`).
fn own_region_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(b, B::IterRemainder | B::Utf8ChunkValid | B::Utf8ChunkInvalid)
}

/// The builtins that borrow into their receiver (or move elements out of
/// it) and return nothing of their other arguments, storing nothing
/// either (see `Builder::call_receiver`).
fn receiver_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(
        b,
        B::VecGet
            | B::SliceSplitAt(_)
            | B::StrSplitAt(_)
            | B::SliceSplitEnd(_)
            | B::SliceStrip(_)
            | B::SliceTrimAscii(_)
            | B::SliceAsChunks(_)
            | B::VecFirst
            | B::VecLast
            | B::VecGetMut
            | B::VecFirstMut
            | B::VecLastMut
            | B::VecAsSlice
            | B::VecAsMutSlice
            | B::VecSpareCapacityMut
            | B::StringAsStr
            | B::StringAsMutStr
            | B::StrTrim
            | B::StrTrimStart
            | B::StrTrimEnd
            | B::StrStripPrefix
            | B::StrStripSuffix
            | B::StrPatStripPrefix
            | B::StrPatStripSuffix
            | B::StrTrimMatches
            | B::StrTrimStartMatches
            | B::StrTrimEndMatches
            | B::IterIter
            | B::IterIterMut
            | B::VecPop
            | B::VecRemove
            | B::VecSwapRemove
            | B::VecSplitOff
            | B::SliceToVec
            | B::Sync(
                crate::check::sync::SyncOp::MutexLock
                    | crate::check::sync::SyncOp::RwLockRead
                    | crate::check::sync::SyncOp::RwLockWrite
                    | crate::check::sync::SyncOp::LockGetMut
                    | crate::check::sync::SyncOp::PoisonGetRef
                    | crate::check::sync::SyncOp::PoisonGetMut
                    | crate::check::sync::SyncOp::ChanRecv
                    | crate::check::sync::SyncOp::ChanTryRecv
                    | crate::check::sync::SyncOp::ChanRecvTimeout
                    | crate::check::sync::SyncOp::OnceGet
                    | crate::check::sync::SyncOp::OnceGetMut
                    | crate::check::sync::SyncOp::OnceTake
                    | crate::check::sync::SyncOp::TryLock(_)
                    | crate::check::sync::SyncOp::RecvMakeIter(0 | 1)
            )
            | B::VecDrain
            | B::StringDrain
            | B::VecDrainAsSlice
            | B::ArrayIterAsSlice
            | B::StrDrainAsStr
            | B::SliceGetRange
            | B::SliceGetRangeMut
            | B::StrGetRange
    )
}

/// The iterator methods whose closure takes `&Self::Item` (check/iter.rs
/// `fn_mut_param_ref`): its outer reference is higher-ranked.
fn by_ref_item(b: Option<crate::check::Builtin>) -> bool {
    use crate::check::Builtin as B;
    matches!(b, Some(B::IterFilter | B::IterTakeWhile | B::IterSkipWhile | B::IterInspect | B::IterNextIf | B::IterFind | B::IterMinByKey | B::IterMaxByKey | B::VecRetain | B::VecRetainMut | B::MapRetain | B::SetRetain))
        || b.is_some_and(sort_by_builtin)
}

/// Iterator methods that call their closure argument during the call
/// and keep nothing of it (`any`, `all`, `position`, `rposition`,
/// `for_each`).
fn consume_closure_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(b, B::IterAny | B::IterAll | B::IterPosition | B::IterRposition | B::IterForEach)
}

/// `sort_by(f)`, `sort_by_key(f)`, and their unstable forms: `f` takes
/// higher-ranked `&T` arguments and runs during the call only.
fn sort_by_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(b, B::SliceSortBy | B::SliceSortUnstableBy | B::SliceSortByKey | B::SliceSortUnstableByKey)
}

/// The map and set lookups by `&Q` (W-STD-B): the key is not stored or
/// returned.
fn hash_lookup_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(b, B::MapGet | B::MapGetMut | B::MapGetKeyValue | B::MapContainsKey | B::MapRemove | B::MapRemoveEntry | B::SetContains | B::SetRemove | B::SetGet)
}

/// `map.entry(k)` and the Entry methods that return the value or the
/// Entry (W-STD-B, `call_hash_entry`).
fn entry_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(
        b,
        B::MapEntry
            | B::EntryOrInsert
            | B::EntryOrDefault
            | B::EntryOrInsertWith
            | B::EntryOrInsertWithKey
            | B::EntryAndModify
            | B::EntryInsertEntry
            | B::EntryInsert
            | B::EntryAsOccupied
            | B::EntryAsVacant
            | B::VacIntoKey
            | B::OccKey
            | B::OccGet
            | B::OccGetMut
            | B::OccIntoMut
            | B::OccInsert
            | B::OccRemove
            | B::OccRemoveEntry
    )
}

/// The builtin iterator calls whose result is an item (or a collection
/// of items): their regions come from the iterator's sources.
/// The `core::fmt` builtins whose result borrows from the receiver
/// alone (a builder, or `&mut Self` of one).
fn fmt_builder_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(
        b,
        B::FmtDebugStruct
            | B::FmtDebugTuple
            | B::FmtDebugList
            | B::FmtDebugSet
            | B::FmtDebugMap
            | B::DsField
            | B::DtField
            | B::DlEntry
            | B::DmEntry
            | B::DlEntries
            | B::DmEntries
            | B::DmKey
            | B::DmValue
    )
}

/// The builtin iterator calls whose result is an item (or a collection
/// of items, or a `sum` into `Option` or `Result`): their regions come
/// from the iterator's sources.
fn item_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(
        b,
        B::IterNext
            | B::IterNextBack
            | B::IterNextIf
            | B::IterNextIfEq
            | B::IterNth
            | B::IterFind
            | B::IterFindMap
            | B::IterLast
            | B::IterMin
            | B::IterMax
            | B::IterMinByKey
            | B::IterMaxByKey
            | B::IterCollect
            | B::IterPartition
            | B::IterUnzip
            | B::FromIter
            | B::IterSum
            | B::IterProduct
    )
}

/// True when nothing in a value of type `t` can be written through a
/// shared reference to it, at any depth: built only from primitives,
/// `str`, references, `String`, `Vec`, `Box`, `Option`, tuples,
/// arrays, slices, the hash tables of such parts, and trait objects
/// whose trait names no lifetime. Any other type (a `Cell` anywhere,
/// a user Adt, a parameter) answers false.
fn plain_shared(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Str | TyKind::Unit => true,
        TyKind::Ref(_, _, i) | TyKind::Array(i, _) | TyKind::Slice(i) => plain_shared(p, tys, i),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| plain_shared(p, tys, e)),
        // A trait object stores a borrow only through a lifetime its
        // trait names: none here (no lifetime args, plain type args),
        // so its object lifetime alone takes no capture.
        TyKind::Dyn(b, _) => tys.dyn_bounds(b).principal.is_none_or(|pr| {
            !tys.args(pr.value.args).iter().any(|g| matches!(g, GenericArg::Lifetime(_)))
                && dyn_arg_tys(tys, t).into_iter().all(|e| plain_shared(p, tys, e))
        }),
        // `Rc<T>` and `Arc<T>` hand out `&T` only.
        TyKind::Adt(..) if let Some(e) = tys.rc_elem(t) => plain_shared(p, tys, e),
        // A written Adt with no lifetime param and no borrow in its type
        // arguments holds no borrow at any depth, so nothing written through
        // `&T` can take one (ts-rust goport_watch.rs:308: an `Arc<dyn Fn(Ev)>`
        // element, `Ev` a plain struct). Builtins keep the rule below:
        // `Chars` and the guards hold a borrow no argument names.
        TyKind::Adt(..) if holds_no_borrow(p, tys, t) => true,
        TyKind::Adt(_, a) => {
            matches!(
                tys.builtin_of(t),
                Some(BuiltinTy::String | BuiltinTy::Vec | BuiltinTy::Boxed | BuiltinTy::Option | BuiltinTy::Hash(_))
            ) && tys.args(a).iter().all(|g| g.as_ty().is_none_or(|e| plain_shared(p, tys, e)))
        }
        _ => false,
    }
}

/// True when a value of type `t` holds no borrow at any depth: built from
/// primitives, `str`, tuples, arrays, slices, and written Adts with no
/// lifetime param whose type arguments are such types. A reference, pointer,
/// trait object, parameter, closure or builtin Adt answers false
/// (`plain_shared`).
fn holds_no_borrow(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Str | TyKind::Unit | TyKind::Never => true,
        TyKind::Array(e, _) | TyKind::Slice(e) => holds_no_borrow(p, tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| holds_no_borrow(p, tys, e)),
        // A body type erases a user Adt's lifetime arguments: its own
        // lifetime params count (`adt_regions`).
        TyKind::Adt(_, a) if tys.builtin_of(t).is_none() && adt_regions(p, tys, t) == 0 => tys.args(a).iter().all(|g| match g {
            GenericArg::Ty(e) => holds_no_borrow(p, tys, *e),
            GenericArg::Lifetime(_) => false,
            GenericArg::Const(_) => true,
        }),
        _ => false,
    }
}

/// True when a type holds a `&mut` reference somewhere.
/// True when a value of type `t` can reach a `Cell`, `RefCell`, or
/// `RefCell` guard: memory shared values can write through. A builtin
/// result of such a type may alias its source (an `Rc` clone shares the
/// cell), so its regions are the source's, not just outlived by them.
fn has_interior(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(_, _, inner) | TyKind::Array(inner, _) | TyKind::Slice(inner) => has_interior(tys, inner),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| has_interior(tys, e)),
        TyKind::Adt(_, a) => {
            matches!(tys.builtin_of(t), Some(BuiltinTy::Cell | BuiltinTy::RefCell | BuiltinTy::RefGuard | BuiltinTy::RefMutGuard))
                || tys.guard_elem(t).is_some()
                || tys.lock_elem(t).is_some()
                || tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| has_interior(tys, e)))
        }
        TyKind::Closure(_, a) => closure_fields(tys, a).into_iter().any(|e| has_interior(tys, e)),
        _ => false,
    }
}

fn has_mut_ref(tys: &impl TyIntern, t: Ty) -> bool {
    // A map Entry holds `&'a mut HashMap<K, V>` (W-STD-B).
    if let Some(BuiltinTy::Hash(crate::ty::hash::HashTy::Entry | crate::ty::hash::HashTy::OccupiedEntry | crate::ty::hash::HashTy::VacantEntry)) = tys.builtin_of(t) {
        return true;
    }
    match tys.kind(t) {
        TyKind::Ref(_, m, inner) => m.is_mut() || has_mut_ref(tys, inner),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| has_mut_ref(tys, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) => has_mut_ref(tys, e),
        TyKind::Adt(_, a) | TyKind::Closure(_, a) => tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| has_mut_ref(tys, e))),
        _ => false,
    }
}

impl Builder<'_, '_> {
    /// Solves the constraints: strongly connected components of the
    /// outlives graph, then per component (sinks first) the locals,
    /// drop-live locals, and universals it reaches.
    pub fn solve(self) -> Solution {
        let nv = self.owner.len();
        let nl = self.body.locals.len();
        let wn = nl.div_ceil(64).max(1);
        // CSR adjacency.
        let mut start = vec![0u32; nv + 1];
        for &(a, _) in &self.edges {
            start[a as usize + 1] += 1;
        }
        for i in 0..nv {
            start[i + 1] += start[i];
        }
        let mut adj = vec![0u32; self.edges.len()];
        let mut fill = start.clone();
        for &(a, b) in &self.edges {
            adj[fill[a as usize] as usize] = b;
            fill[a as usize] += 1;
        }
        let (scc, n_scc) = tarjan(nv, &start, &adj);
        // Components in emission order are sinks first; members by component.
        let nu = self.own.n_univ as usize + 1;
        let wu = nu.div_ceil(64).max(1);
        let mut use_l = vec![0u64; n_scc * wn];
        let mut drop_l = vec![0u64; n_scc * wn];
        let mut univ = vec![0u64; n_scc * wu];
        let mut ret = vec![false; n_scc];
        let mut members: Vec<Vec<u32>> = vec![Vec::new(); n_scc];
        for v in 0..nv {
            members[scc[v] as usize].push(v as u32);
        }
        for c in 0..n_scc {
            for &v in &members[c] {
                let v = v as usize;
                if v < nu {
                    univ[c * wu + v / 64] |= 1 << (v % 64);
                }
                let o = self.owner[v];
                if o > 0 {
                    let l = (o - 1) as usize;
                    use_l[c * wn + l / 64] |= 1 << (l % 64);
                    if self.drop_slot[v] {
                        drop_l[c * wn + l / 64] |= 1 << (l % 64);
                    }
                    if l == 0 {
                        ret[c] = true;
                    }
                }
                for k in start[v]..start[v + 1] {
                    let d = scc[adj[k as usize] as usize] as usize;
                    if d != c {
                        for w in 0..wn {
                            use_l[c * wn + w] |= use_l[d * wn + w];
                            drop_l[c * wn + w] |= drop_l[d * wn + w];
                        }
                        for w in 0..wu {
                            univ[c * wu + w] |= univ[d * wu + w];
                        }
                        ret[c] |= ret[d];
                    }
                }
            }
        }
        let n_loans = self.loan_var.len();
        let mut sol = Solution {
            wn,
            use_locals: vec![0; n_loans * wn],
            drop_locals: vec![0; n_loans * wn],
            univ: vec![false; n_loans],
            to_ret: vec![false; n_loans],
            drop_live: vec![false; nl],
            errs: self.errs.clone(),
            reqs: Vec::new(),
        };
        for (i, &lv) in self.loan_var.iter().enumerate() {
            let c = scc[lv as usize] as usize;
            sol.use_locals[i * wn..(i + 1) * wn].copy_from_slice(&use_l[c * wn..(c + 1) * wn]);
            sol.drop_locals[i * wn..(i + 1) * wn].copy_from_slice(&drop_l[c * wn..(c + 1) * wn]);
            sol.univ[i] = univ[c * wu..(c + 1) * wu].iter().any(|&w| w != 0);
            sol.to_ret[i] = ret[c];
        }
        for v in 0..nv {
            if self.drop_slot[v] && self.owner[v] > 0 {
                sol.drop_live[(self.owner[v] - 1) as usize] = true;
            }
        }
        if self.own.closure {
            for u in 1..nu {
                let c = scc[u] as usize;
                for v in bit_iter(&univ[c * wu..(c + 1) * wu]) {
                    if v != u && v < nu {
                        sol.reqs.push((u as u32, v as u32));
                    }
                }
            }
        }
        if self.own.check {
            let known = self.own.known();
            let mut reported: Vec<(usize, usize)> = Vec::new();
            for u in 1..nu {
                let c = scc[u] as usize;
                // A captured or free argument region the body needs to be
                // `'static` is the creator's requirement (`'static` outlives
                // every region, so the others it reaches follow from it).
                let creator_static = matches!(self.own.ends.get(u), Some(Some(End::Cap(_) | End::Arg(_) | End::Fn(_))))
                    && matches!(self.own.ends.first(), Some(Some(End::Static)))
                    && bit_iter(&univ[c * wu..(c + 1) * wu]).any(|v| v == 0);
                for v in bit_iter(&univ[c * wu..(c + 1) * wu]) {
                    if v == u || v >= nu || known[u * nu + v] || reported.contains(&(u, v)) || creator_static {
                        continue;
                    }
                    // A closure's creator proves relations between its
                    // captured and free argument regions and the enclosing
                    // fn's lifetimes (`closure_reqs`).
                    if matches!(self.own.ends.get(u), Some(Some(End::Cap(_) | End::Arg(_) | End::Fn(_))))
                        && matches!(self.own.ends.get(v), Some(Some(End::Static | End::Cap(_) | End::Arg(_) | End::Fn(_))))
                    {
                        continue;
                    }
                    // So does a `call_out` closure's creator for its output
                    // slots: the call picks their regions.
                    if self.own.call_out
                        && matches!(self.own.ends.get(u), Some(Some(End::Out(_))))
                        && matches!(self.own.ends.get(v), Some(Some(End::Static | End::Cap(_) | End::Arg(_) | End::Fn(_))))
                    {
                        continue;
                    }
                    // `u: v` follows from `u: w` and a known `w: v` (an implied
                    // bound: a capture's region outlives the closure env's
                    // lifetime) when `u: w` itself is known or is the
                    // creator's to prove (not skipped by this rule in turn).
                    let to_creator = |w: usize| {
                        let end = |x: usize| self.own.ends.get(x).copied().flatten();
                        matches!(end(w), Some(End::Static | End::Cap(_) | End::Arg(_) | End::Fn(_)))
                            && (matches!(end(u), Some(End::Cap(_) | End::Arg(_) | End::Fn(_))) || self.own.call_out && matches!(end(u), Some(End::Out(_))))
                    };
                    if bit_iter(&univ[c * wu..(c + 1) * wu])
                        .any(|w| w != u && w != v && w < nu && known[w * nu + v] && (known[u * nu + w] || to_creator(w)))
                    {
                        continue;
                    }
                    reported.push((u, v));
                    let span = self.path_span(u as u32, v as u32, &start, &adj);
                    let (a, b) = (&self.own.names[u], &self.own.names[v]);
                    sol.errs.push(Diag::new(
                        "L0733",
                        span,
                        format!("lifetime may not live long enough: {a} must outlive {b}"),
                        "Return or store data that borrows from the right parameter, or declare the relation (`'a: 'b`).",
                    ));
                }
            }
        }
        sol
    }

    /// The span of the statement whose constraint completes the path from
    /// `from` to `to`, for an error at the right place.
    fn path_span(&self, from: u32, to: u32, start: &[u32], adj: &[u32]) -> Span {
        let nv = self.owner.len();
        let mut parent: Vec<u32> = vec![u32::MAX; nv];
        parent[from as usize] = from;
        let mut queue = std::collections::VecDeque::from([from]);
        while let Some(v) = queue.pop_front() {
            if v == to {
                break;
            }
            for k in start[v as usize]..start[v as usize + 1] {
                let w = adj[k as usize];
                if parent[w as usize] == u32::MAX {
                    parent[w as usize] = v;
                    queue.push_back(w);
                }
            }
        }
        // Walk back from `to`; the last edge with a real span wins.
        let mut v = to;
        let mut best = Span::default();
        while parent[v as usize] != u32::MAX && parent[v as usize] != v {
            let u = parent[v as usize];
            if let Some(i) = self.edges.iter().position(|&e| e == (u, v))
                && self.edge_span[i] != Span::default()
                && best == Span::default()
            {
                best = self.edge_span[i];
            }
            v = u;
        }
        if best == Span::default() { self.p.fn_def(self.body.fn_id).name_span } else { best }
    }
}

/// Tarjan's strongly connected components, iteratively. Returns the
/// component of each node, numbered in completion order (sinks first),
/// and the component count.
fn tarjan(n: usize, start: &[u32], adj: &[u32]) -> (Vec<u32>, usize) {
    const NONE: u32 = u32::MAX;
    let mut index = vec![NONE; n];
    let mut low = vec![0u32; n];
    let mut on_stack = vec![false; n];
    let mut comp = vec![NONE; n];
    let mut stack: Vec<u32> = Vec::new();
    let mut next = 0u32;
    let mut n_comp = 0u32;
    // (node, next edge offset)
    let mut work: Vec<(u32, u32)> = Vec::new();
    for root in 0..n as u32 {
        if index[root as usize] != NONE {
            continue;
        }
        work.push((root, start[root as usize]));
        index[root as usize] = next;
        low[root as usize] = next;
        next += 1;
        stack.push(root);
        on_stack[root as usize] = true;
        while let Some(&mut (v, ref mut k)) = work.last_mut() {
            if *k < start[v as usize + 1] {
                let w = adj[*k as usize];
                *k += 1;
                if index[w as usize] == NONE {
                    index[w as usize] = next;
                    low[w as usize] = next;
                    next += 1;
                    stack.push(w);
                    on_stack[w as usize] = true;
                    work.push((w, start[w as usize]));
                } else if on_stack[w as usize] {
                    low[v as usize] = low[v as usize].min(index[w as usize]);
                }
            } else {
                work.pop();
                if let Some(&(u, _)) = work.last() {
                    low[u as usize] = low[u as usize].min(low[v as usize]);
                }
                if low[v as usize] == index[v as usize] {
                    loop {
                        let w = stack.pop().unwrap();
                        on_stack[w as usize] = false;
                        comp[w as usize] = n_comp;
                        if w == v {
                            break;
                        }
                    }
                    n_comp += 1;
                }
            }
        }
    }
    (comp, n_comp as usize)
}

/// The trait method an impl method implements, for a fn of a trait impl
/// (or an instance of one); None for inherent methods and plain fns.
pub fn impl_trait_method(p: &Program, f: LocalDefId) -> Option<DefId> {
    let src = p.gx.instances.get(&f).and_then(|i| i.template_local).unwrap_or(f);
    let impl_def = p.defs.parent_of(p.def_id(src))?;
    let (_, rec) = p.gx.index.by_def(impl_def)?;
    p.gx.index.trait_record(rec.trait_def)?.method_by_name(p.fn_info(src).name)
}

/// The trait-contract check of an impl method's regions (W-BORROW, rustc
/// compare_impl_method): the trait's signature must be a subtype of the
/// impl's for every choice of the trait's lifetimes. The trait's
/// universals are placeholders, the impl's are free; `trait param <: impl
/// param` and `impl ret <: trait ret` give outlives edges, and a
/// placeholder that must then outlive another (or `'static`) without a
/// trait fact or implied bound is L0734. The impl may promise more (a
/// `'static` result where the trait borrows), never less.
pub(super) fn impl_contract(p: &Program, f: LocalDefId) -> Option<Diag> {
    let own = p.regions.fns.get(&f)?;
    let info = p.fn_info(f);
    let tmeth = impl_trait_method(p, f)?;
    let tsig = p.regions.trait_methods.get(&tmeth)?;
    if tsig.params.len() != own.params.len() {
        return None;
    }
    let nt = tsig.n_univ as usize;
    let n = 1 + nt + own.n_univ as usize;
    // A trait's own lifetime params (the trait method's first universals)
    // are what the impl header gives them: `'static` (`impl Tr<'static>`),
    // or the impl's lifetime passed for them (`impl<'d> Tr<'d>`), which
    // stays a placeholder of the contract.
    let impl_def = p.fn_defs.get(f.0 as usize).and_then(|&d| p.defs.get(d)).and_then(|d| d.parent);
    let trait_lts = impl_def.and_then(|d| p.regions.impl_heads.get(&d)).map(|h| h.trait_lifetimes.clone()).unwrap_or_default();
    let mut cx = Contract { p, nt, trait_lts, edges: Vec::new(), mismatch: false };
    for (&t, &i) in tsig.params.iter().zip(&own.params) {
        cx.walk(t, i, Variance::Co, true);
    }
    cx.walk(own.ret, tsig.ret, Variance::Co, false);
    if cx.mismatch {
        return Some(Diag::new(
            "L0734",
            info.def(&p.ast).name_span,
            format!("lifetime mismatch: method `{}` writes a fn pointer type whose lifetimes differ from the trait's", p.display_name(info.name)),
            "Write the fn pointer types of the trait method's signature.",
        ));
    }
    // Known relations among the trait's lifetimes: its facts and the
    // implied bounds of its signature types, closed transitively.
    let mut known = vec![false; (nt + 1) * (nt + 1)];
    for a in 0..=nt {
        known[a * (nt + 1) + a] = true;
        known[a] = true;
    }
    let add_known = |a: Region, b: Region, known: &mut Vec<bool>| {
        let idx = |r: Region| match r {
            Region::Static => Some(0),
            Region::Param(k) if (k as usize) < nt => Some(1 + k as usize),
            _ => None,
        };
        if let (Some(x), Some(y)) = (idx(a), idx(b)) {
            known[x * (nt + 1) + y] = true;
        }
    };
    for &(a, b) in &tsig.facts {
        add_known(a, b, &mut known);
    }
    for &t in tsig.params.iter().chain(std::iter::once(&tsig.ret)) {
        let mut facts = Vec::new();
        implied_regioned(&p.tys, t, &mut Vec::new(), &mut facts);
        for (a, b) in facts {
            add_known(a, b, &mut known);
        }
    }
    let w = nt + 1;
    for k in 0..w {
        for a in 0..w {
            if known[a * w + k] {
                for b in 0..w {
                    if known[k * w + b] {
                        known[a * w + b] = true;
                    }
                }
            }
        }
    }
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for &(a, b) in &cx.edges {
        adj[a].push(b);
    }
    for pl in 1..=nt {
        let mut seen = vec![false; n];
        let mut stack = vec![pl];
        seen[pl] = true;
        while let Some(x) = stack.pop() {
            for &y in &adj[x] {
                if !seen[y] {
                    seen[y] = true;
                    stack.push(y);
                }
            }
        }
        for q in 0..=nt {
            if q != pl && seen[q] && !known[pl * w + q] {
                return Some(Diag::new(
                    "L0734",
                    info.def(&p.ast).name_span,
                    format!("lifetime mismatch: method `{}` does not fit the lifetimes of the trait's signature", p.display_name(info.name)),
                    "Match the trait method's signature: return at least what it promises, and take at least what it accepts.",
                ));
            }
        }
    }
    None
}

/// The edge walk of `impl_contract` over two regioned types.
struct Contract<'p> {
    p: &'p Program,
    /// Trait universal count: node 0 is `'static`, `1..=nt` the trait's,
    /// the impl's after them.
    nt: usize,
    /// The impl-side region of each of the trait's own lifetime params.
    trait_lts: Vec<Region>,
    edges: Vec<(usize, usize)>,
    /// Two fn pointer types whose free slots differ (W-BORROW3), or two
    /// dyn types whose late-bound regions differ (R11).
    mismatch: bool,
}

impl Contract<'_> {
    /// The node of region `r` on the trait side or the impl side.
    fn node(&self, r: Region, trait_side: bool) -> Option<usize> {
        match r {
            Region::Static => Some(0),
            // A trait lifetime the header fixes to `'static` is `'static`.
            Region::Param(k) if trait_side && self.trait_lts.get(k as usize) == Some(&Region::Static) => Some(0),
            Region::Param(k) if trait_side => Some(1 + k as usize),
            // An impl lifetime the header passes as the trait's `k`-th
            // lifetime is that one, a placeholder of the contract.
            Region::Param(m) if let Some(k) = self.trait_lts.iter().position(|&x| x == Region::Param(m)) => Some(1 + k),
            Region::Param(k) => Some(1 + self.nt + k as usize),
            _ => None,
        }
    }

    /// Edges for `a <: b` at variance `v`; `a_trait` says which side `a`
    /// comes from (the other side is `b`).
    fn walk(&mut self, a: Ty, b: Ty, v: Variance, a_trait: bool) {
        let tys = &self.p.tys;
        match (tys.kind(a), tys.kind(b)) {
            (TyKind::Ref(ra, ma, ia), TyKind::Ref(rb, mb, ib)) if ma == mb => {
                if bound(ra) != bound(rb) {
                    self.mismatch = true;
                } else if !bound(ra) {
                    self.slot(ra, rb, v, a_trait);
                }
                let iv = if ma.is_mut() { Variance::Inv } else { Variance::Co };
                self.walk(ia, ib, v.then(iv), a_trait);
            }
            (TyKind::Adt(da, xa), TyKind::Adt(db, xb)) if da == db => {
                let (xs, ys) = (tys.args(xa).to_vec(), tys.args(xb).to_vec());
                let (mut k, mut j) = (0usize, 0usize);
                for (x, y) in xs.into_iter().zip(ys) {
                    match (x, y) {
                        (GenericArg::Lifetime(rx), GenericArg::Lifetime(ry)) => {
                            let rv = self.p.regions.adts(self.p).region_modes(da, k).0;
                            if bound(rx) != bound(ry) {
                                self.mismatch = true;
                            } else if !bound(rx) {
                                self.slot(rx, ry, v.then(rv), a_trait);
                            }
                            k += 1;
                        }
                        (GenericArg::Ty(x), GenericArg::Ty(y)) => {
                            let (pv, _) = self.p.regions.adts(self.p).arg_modes(self.p, da, j);
                            self.walk(x, y, v.then(pv), a_trait);
                            j += 1;
                        }
                        _ => j += 1,
                    }
                }
            }
            (TyKind::Tuple(x), TyKind::Tuple(y)) => {
                for (x, y) in tys.tys_of(x).to_vec().into_iter().zip(tys.tys_of(y).to_vec()) {
                    self.walk(x, y, v, a_trait);
                }
            }
            (TyKind::Array(x, _), TyKind::Array(y, _)) | (TyKind::Slice(x), TyKind::Slice(y)) => self.walk(x, y, v, a_trait),
            (TyKind::Dyn(_, ra), TyKind::Dyn(_, rb)) => {
                if bound(ra) != bound(rb) {
                    self.mismatch = true;
                } else if !bound(ra) {
                    self.slot(ra, rb, v.then(Variance::Co), a_trait);
                }
                let (xs, ys) = (dyn_arg_tys(tys, a), dyn_arg_tys(tys, b));
                if xs.len() != ys.len() {
                    self.mismatch = true;
                }
                for (x, y) in xs.into_iter().zip(ys) {
                    self.walk(x, y, Variance::Inv, a_trait);
                }
            }
            (TyKind::FnPtr(sa), TyKind::FnPtr(sb)) => {
                let (sa, sb) = (tys.sig(sa).value, tys.sig(sb).value);
                if sa.free_slots != sb.free_slots {
                    self.mismatch = true;
                } else if sa.free_slots != 0 {
                    self.slot(sa.free_region, sb.free_region, Variance::Inv, a_trait);
                }
            }
            _ => {}
        }
    }

    fn slot(&mut self, ra: Region, rb: Region, v: Variance, a_trait: bool) {
        let (Some(x), Some(y)) = (self.node(ra, a_trait), self.node(rb, !a_trait)) else { return };
        match v {
            Variance::Co => self.edges.push((x, y)),
            Variance::Contra => self.edges.push((y, x)),
            Variance::Inv => {
                self.edges.push((x, y));
                self.edges.push((y, x));
            }
            Variance::Bi => {}
        }
        // `'static` outlives everything: no edges out of it are needed.
        self.edges.retain(|&(a, _)| a != 0);
    }
}

/// Implied outlives facts of a regioned type: every region inside a
/// reference outlives the reference's own region.
fn implied_regioned(tys: &impl TyIntern, t: Ty, outer: &mut Vec<Region>, out: &mut Vec<(Region, Region)>) {
    let note = |r: Region, outer: &Vec<Region>, out: &mut Vec<(Region, Region)>| {
        for &o in outer {
            out.push((r, o));
        }
    };
    match tys.kind(t) {
        TyKind::Ref(r, _, inner) if bound(r) => implied_regioned(tys, inner, outer, out),
        TyKind::Ref(r, _, inner) => {
            note(r, outer, out);
            outer.push(r);
            implied_regioned(tys, inner, outer, out);
            outer.pop();
        }
        TyKind::Adt(_, args) => {
            for g in tys.args(args).to_vec() {
                match g {
                    GenericArg::Lifetime(r) => note(r, outer, out),
                    GenericArg::Ty(e) => implied_regioned(tys, e, outer, out),
                    GenericArg::Const(_) => {}
                }
            }
        }
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts).to_vec() {
                implied_regioned(tys, e, outer, out);
            }
        }
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => implied_regioned(tys, e, outer, out),
        TyKind::Dyn(_, r) => note(r, outer, out),
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::{Variance, tarjan};

    /// Components come out sinks first, and a cycle is one component.
    #[test]
    fn tarjan_orders_sinks_first() {
        // 0 -> 1 -> 2 -> 1, 0 -> 3
        let edges: Vec<(u32, u32)> = vec![(0, 1), (1, 2), (2, 1), (0, 3)];
        let n = 4;
        let mut start = vec![0u32; n + 1];
        for &(a, _) in &edges {
            start[a as usize + 1] += 1;
        }
        for i in 0..n {
            start[i + 1] += start[i];
        }
        let mut adj = vec![0u32; edges.len()];
        let mut fill = start.clone();
        for &(a, b) in &edges {
            adj[fill[a as usize] as usize] = b;
            fill[a as usize] += 1;
        }
        let (comp, nc) = tarjan(n, &start, &adj);
        assert_eq!(nc, 3);
        assert_eq!(comp[1], comp[2], "the cycle is one component");
        assert!(comp[0] > comp[1] && comp[0] > comp[3], "the source completes after its successors");
    }

    /// The variance algebra matches Rust's composition rules.
    #[test]
    fn variance_compose_and_join() {
        use Variance::*;
        assert_eq!(Co.then(Contra), Contra);
        assert_eq!(Contra.then(Contra), Co);
        assert_eq!(Contra.then(Inv), Inv);
        assert_eq!(Bi.then(Inv), Bi);
        assert_eq!(Co.join(Contra), Inv);
        assert_eq!(Bi.join(Contra), Contra);
        assert_eq!(Co.join(Co), Co);
    }
}

