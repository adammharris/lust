// `dyn Trait` (docs/ARCH.md section 2.8): dyn compatibility, the vtable
// layout of each user trait, object method lookup for dyn receivers
// (section 2.10), and the slot paths of trait upcasting.
//
// One `DynInfo` per user trait is computed after the trait tables
// exist (`compute_dyn_infos`, from `finish_collect`). Everything else
// reads it: the dyn type checks at signature and body sites, the
// method probe for dyn receivers, the coercion checks, mono's vtable
// builder, lowering (slot paths), and codegen (vtable statics).
//
// Vtable layout, one array of pointer-sized words per (concrete type,
// principal trait ref):
//
//   [0]  drop glue for the concrete type, or 0 when it needs none
//   [1]  size of the concrete type (Rust layout)
//   [2]  align of the concrete type
//   [3]  the concrete type's Debug fmt shim, or 0 when the principal
//        trait has no `Debug` supertrait (`VT_FMT_DEBUG`)
//   [4]  the same for Display (`VT_FMT_DISPLAY`)
//   [5 .. 5+S)  one vtable pointer per direct supertrait that has a
//               vtable, in declaration order (the `super_N` slots)
//   [5+S ..)    one entry per vtable method, in declaration order
//
// A `dyn Any` vtable has no super slots and no methods: words 5 and 6
// hold the value's type id instead (`VT_ANY_ID`, check/any.rs).
//
// A method entry is a per-vtable shim that forwards through
// `lust_fns[slot]`, never a body address, so a daemon overlay that
// swaps a method body cannot leave a stale entry (ARCH 4.5). A
// supertrait method is reached through its `super_N` chain, which is
// also the upcast path: upcasting `&dyn Sub` to `&dyn Super` loads one
// super slot per level, fixed at compile time.
use crate::check::collect::Program;
use crate::def::{DefId, LocalDefId};
use crate::diag::{Diag, Span};
use crate::intern::{FxMap, Sym};
use crate::ty::*;

/// Words before the first super slot: drop, size, align, and the two
/// fmt shims below.
pub const VT_HEADER: u32 = 5;
/// The header words `size_of_val` and `align_of_val` read.
pub const VT_SIZE: u32 = 1;
pub const VT_ALIGN: u32 = 2;
/// The header words that call the concrete type's `Debug::fmt` and
/// `Display::fmt` glue (`int (void *self, lust_Formatter *f)`), or 0
/// when the principal trait does not require that fmt trait through a
/// supertrait. A fixed slot lets the fmt glue dispatch without knowing
/// the principal trait (cgen/fmt.rs).
pub const VT_FMT_DEBUG: u32 = 3;
pub const VT_FMT_DISPLAY: u32 = 4;
/// The two words of a `dyn Any` vtable that hold the value's type id
/// (check/any.rs), low word first. `Any` has no super slots and no
/// vtable methods, so they follow the header.
pub const VT_ANY_ID: u32 = VT_HEADER;

/// How a vtable method takes its receiver.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DynRecv {
    Ref,
    RefMut,
}

/// One vtable method of a trait.
#[derive(Clone, Debug)]
pub struct DynMethod {
    pub def: DefId,
    pub name: Sym,
    pub recv: DynRecv,
    /// The method has `where Self: 'static`: a call through dyn needs a
    /// `'static` object lifetime (rustc E0521 otherwise).
    pub needs_static: bool,
}

/// The dyn view of one user trait.
#[derive(Clone, Debug, Default)]
pub struct DynInfo {
    /// Why the trait is not dyn compatible (rustc E0038), first reason
    /// found: the message tail and the offending item's span.
    pub violation: Option<(String, Span)>,
    /// A dyn form the subset cannot build a vtable for yet.
    pub unsupported: Option<String>,
    /// Direct supertraits with a vtable, in declaration order, as trait
    /// refs over this trait's params (Self is `Param(0)`).
    pub supers: Vec<TraitRef>,
    /// Auto traits the trait requires through its supertraits.
    pub auto: AutoTraits,
    /// Vtable methods in declaration order.
    pub methods: Vec<DynMethod>,
    /// Methods that exist but cannot be called through dyn: the name,
    /// its def, and why.
    pub uncallable: Vec<(Sym, DefId, &'static str)>,
    /// The trait or a supertrait bounds `Self` by `'static`: every dyn
    /// type with this principal is `'static` (see `dyn_is_static`).
    pub static_bound: bool,
    /// The trait requires `Debug` (directly or through a supertrait):
    /// the dyn type implements `Debug` through `VT_FMT_DEBUG`.
    pub fmt_debug: bool,
    /// The same for `Display`, through `VT_FMT_DISPLAY`.
    pub fmt_display: bool,
}

impl DynInfo {
    /// The word index of super slot `i`.
    pub fn super_slot(&self, i: usize) -> u32 {
        VT_HEADER + i as u32
    }
    /// The word index of vtable method `j`.
    pub fn method_slot(&self, j: usize) -> u32 {
        VT_HEADER + self.supers.len() as u32 + j as u32
    }
}

/// One materialized vtable (built by mono, emitted by codegen).
#[derive(Clone, Debug)]
pub struct VtableData {
    /// The concrete type behind the pointer (global store).
    pub self_ty: Ty,
    /// The existential principal trait ref (global store).
    pub principal: TraitRef,
    /// The callable fn for each vtable method, in `DynInfo::methods` order.
    pub methods: Vec<LocalDefId>,
    /// The vtable for each super slot, in `DynInfo::supers` order.
    pub supers: Vec<u32>,
}

/// The dyn info of every user trait. Runs once trait tables exist.
pub fn compute_dyn_infos(p: &Program) -> FxMap<DefId, DynInfo> {
    let mut memo: FxMap<DefId, DynInfo> = FxMap::default();
    // `dyn Any` (check/any.rs): no vtable methods; its vtable holds the
    // value's type id after the header (`VT_ANY_ID`). `trait Any: 'static`.
    memo.insert(p.gx.lang.any, DynInfo { static_bound: true, ..DynInfo::default() });
    // `dyn Debug` and `dyn Display`: no vtable methods; the dyn type
    // formats through the header shim (`VT_FMT_DEBUG`, `VT_FMT_DISPLAY`).
    memo.insert(p.gx.lang.debug, DynInfo { fmt_debug: true, ..DynInfo::default() });
    memo.insert(p.gx.lang.display, DynInfo { fmt_display: true, ..DynInfo::default() });
    let mut defs: Vec<DefId> = p.gx.trait_names.values().copied().collect();
    defs.sort_by_key(|d| d.hash.0);
    for d in defs {
        info_of(p, d, &mut memo, &mut Vec::new());
    }
    // A trait's own `'static` bound comes from the AST (collect keeps it
    // only as a predicate); supertraits pass it down. The walk has no
    // depth limit: a stopped walk would answer "not `'static`".
    let own: Vec<DefId> = p
        .ast
        .items
        .iter()
        .filter_map(|item| match &item.kind {
            crate::ast::ItemKind::Trait(t) if trait_static_bound(p, t) => p.gx.trait_names.get(&t.name).copied(),
            _ => None,
        })
        .chain(std::iter::once(p.gx.lang.any))
        .collect();
    // `seen` ends cycles (reported elsewhere) and skips a shared
    // supertrait already searched without a hit.
    fn via(memo: &FxMap<DefId, DynInfo>, own: &[DefId], d: DefId, seen: &mut Vec<DefId>) -> bool {
        if own.contains(&d) {
            return true;
        }
        if seen.contains(&d) {
            return false;
        }
        seen.push(d);
        memo.get(&d).is_some_and(|i| i.supers.iter().any(|s| via(memo, own, s.def, seen)))
    }
    let flags: Vec<(DefId, bool)> = memo.keys().map(|&d| (d, via(&memo, &own, d, &mut Vec::new()))).collect();
    for (d, f) in flags {
        memo.get_mut(&d).unwrap().static_bound = f;
    }
    memo
}

/// True when a trait declaration bounds `Self` by `'static` (`trait T:
/// 'static`, `where Self: 'static`).
fn trait_static_bound(p: &Program, t: &crate::ast::TraitDef) -> bool {
    use crate::ast::TraitBound;
    t.bounds.iter().any(|b| matches!(b, TraitBound::Lifetime(lt) if p.name(lt.name) == "static")) || where_self_static(p, &t.where_clause)
}

/// Lang traits whose definition requires `Self: Sized` in std.
fn lang_requires_sized(p: &Program, def: DefId) -> bool {
    let l = &p.gx.lang;
    [l.sized, l.copy, l.clone, l.default, l.from, l.into, l.from_iterator].contains(&def)
}

/// True when a trait predicate on `Self` implies `Self: Sized`, through
/// lang facts and user supertraits.
fn implies_sized(p: &Program, def: DefId, seen: &mut Vec<DefId>) -> bool {
    if lang_requires_sized(p, def) {
        return true;
    }
    if seen.contains(&def) {
        return false;
    }
    seen.push(def);
    let Some(rec) = p.gx.index.trait_record(def) else { return false };
    if !rec.local {
        return false;
    }
    rec.generics.predicates.iter().any(|pred| match pred {
        Predicate::Trait(b) => is_self(&p.tys, p.tys.args(b.value.args)[0]) && implies_sized(p, b.value.def, seen),
        _ => false,
    })
}

fn is_self(tys: &impl TyIntern, g: GenericArg) -> bool {
    g.as_ty().is_some_and(|t| matches!(tys.kind(t), TyKind::Param(ParamId(0))))
}

/// True when `Self` (`Param(0)`) occurs in `t` outside the Self slot of
/// a projection (`Self::Assoc` names the erased type's binding, which a
/// dyn type would supply).
fn mentions_self(tys: &impl TyIntern, t: Ty) -> bool {
    if !tys.flags(t).contains_param() {
        return false;
    }
    let args_mention = |a: ArgsId, skip_self: bool| {
        tys.args(a).iter().enumerate().any(|(i, g)| match g.as_ty() {
            Some(e) => !(skip_self && i == 0 && is_self(tys, *g)) && mentions_self(tys, e),
            None => false,
        })
    };
    match tys.kind(t) {
        TyKind::Param(q) => q.0 == 0,
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => mentions_self(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| mentions_self(tys, e)),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) => args_mention(a, false),
        TyKind::Projection(_, a) => args_mention(a, true),
        TyKind::FnPtr(sig) => {
            let s = tys.sig(sig).value;
            mentions_self(tys, s.output) || tys.tys_of(s.inputs).iter().any(|&e| mentions_self(tys, e))
        }
        TyKind::Dyn(b, _) => tys.dyn_bounds(b).principal.is_some_and(|pr| args_mention(pr.value.args, true)),
        _ => false,
    }
}

/// Fills `memo[def]`. Supertraits are computed first, so their
/// violations, unsupported forms, and auto traits fold into this one.
fn info_of(p: &Program, def: DefId, memo: &mut FxMap<DefId, DynInfo>, stack: &mut Vec<DefId>) {
    if memo.contains_key(&def) || stack.contains(&def) {
        return;
    }
    stack.push(def);
    let mut info = DynInfo::default();
    let Some(rec) = p.gx.index.trait_record(def).cloned() else {
        stack.pop();
        return;
    };
    let tname = p.name(rec.name).to_string();
    let lang = &p.gx.lang;
    // Trait-level facts: supertraits and `Self: Sized`.
    for pred in &rec.generics.predicates {
        let Predicate::Trait(b) = pred else { continue };
        let args = p.tys.args(b.value.args).to_vec();
        if !is_self(&p.tys, args[0]) {
            continue;
        }
        let sup = b.value.def;
        if implies_sized(p, sup, &mut Vec::new()) {
            info.violation.get_or_insert((format!("it requires `Self: Sized`, which a `dyn {tname}` value is not"), rec.span));
            continue;
        }
        if args[1..].iter().any(|g| g.as_ty().is_some_and(|t| mentions_self(&p.tys, t))) {
            info.violation.get_or_insert((format!("a supertrait of `{tname}` uses `Self` as a type parameter"), rec.span));
            continue;
        }
        if lang.is_auto(sup) {
            if sup == lang.send {
                info.auto.send = true;
            } else if sup == lang.sync {
                info.auto.sync = true;
            } else {
                info.auto.unpin = true;
            }
            continue;
        }
        // `trait Language: RefUnwindSafe`: an auto trait of every dyn type
        // with this principal, as `Send` is (check/unwind.rs).
        match crate::check::unwind::unwind_trait(p, sup) {
            Some(false) => {
                info.auto.unwind_safe = true;
                continue;
            }
            Some(true) => {
                info.auto.ref_unwind_safe = true;
                continue;
            }
            None => {}
        }
        // The fmt traits are not vtable supertraits: the dyn type
        // implements them through the fixed header shims, as rustc's
        // object type implements every supertrait. For a trait of
        // this crate, and for core's `Error` (the one std principal
        // whose supertraits are the fmt pair and whose methods are
        // plain source in library/core/src/error.rs, F3): any other
        // std principal keeps the L0702 reject below.
        // The splice range of a std module reads as the crate the
        // user program selected (std), so `Error` is matched by its
        // shipped span and name, not by the range's crate tag.
        let crate_at = p.shipped_crate_at(rec.span);
        let fmt_super_ok = crate_at.is_none() || p.name(rec.name).split('$').next_back() == Some("Error");
        if fmt_super_ok && sup == lang.debug {
            info.fmt_debug = true;
            continue;
        }
        if fmt_super_ok && sup == lang.display {
            info.fmt_display = true;
            continue;
        }
        let Some(srec) = p.gx.index.trait_record(sup) else { continue };
        if !srec.local && sup != lang.any {
            info.unsupported.get_or_insert(format!("`dyn {tname}` with the std supertrait `{}`", p.name(srec.name)));
            continue;
        }
        info_of(p, sup, memo, stack);
        if let Some(si) = memo.get(&sup) {
            if let Some((why, _)) = &si.violation {
                info.violation.get_or_insert((format!("its supertrait `{}` is not dyn compatible: {why}", p.name(srec.name)), rec.span));
            }
            if let Some(u) = &si.unsupported {
                info.unsupported.get_or_insert(u.clone());
            }
            info.auto.send |= si.auto.send;
            info.auto.sync |= si.auto.sync;
            info.auto.unpin |= si.auto.unpin;
            info.auto.unwind_safe |= si.auto.unwind_safe;
            info.auto.ref_unwind_safe |= si.auto.ref_unwind_safe;
            info.fmt_debug |= si.fmt_debug;
            info.fmt_display |= si.fmt_display;
        }
        if !info.supers.iter().any(|s| *s == b.value) {
            info.supers.push(b.value);
        }
    }
    for (_, aname, is_type) in &rec.assoc_items {
        if !*is_type {
            info.violation.get_or_insert((format!("it contains the associated const `{}`", p.name(*aname)), rec.span));
        }
    }
    // Methods: dispatchable ones get vtable entries; `where Self:
    // Sized` ones are skipped, as in rustc.
    let n_params = rec.generics.params.len();
    let n_preds = rec.generics.predicates.len();
    for &(mdef, mname) in &rec.methods {
        let Some(tm) = p.gx.trait_methods.get(&mdef) else { continue };
        let span = tm.def(&p.ast).name_span;
        let mn = p.name(mname).to_string();
        let own_preds = tm.generics.predicates.get(n_preds..).unwrap_or(&[]);
        let exempt = own_preds.iter().any(|pred| match pred {
            Predicate::Trait(b) => is_self(&p.tys, p.tys.args(b.value.args)[0]) && implies_sized(p, b.value.def, &mut Vec::new()),
            _ => false,
        });
        if exempt {
            info.uncallable.push((mname, mdef, "it requires `Self: Sized`"));
            continue;
        }
        let bad = |why: String| Some((why, span));
        let mut v: Option<(String, Span)> = None;
        let recv = match tm.self_kind {
            None => {
                v = v.or(bad(format!("associated function `{mn}` has no `self` parameter")));
                None
            }
            Some(_) => match p.tys.kind(tm.params[0]) {
                TyKind::Param(ParamId(0)) => None,
                TyKind::Ref(_, m, inner) if matches!(p.tys.kind(inner), TyKind::Param(ParamId(0))) => {
                    Some(if m.is_mut() { DynRecv::RefMut } else { DynRecv::Ref })
                }
                _ => {
                    info.unsupported.get_or_insert(format!("calls through `dyn {tname}` to the receiver form of `{mn}`"));
                    None
                }
            },
        };
        if tm.generics.params.len() > n_params {
            v = v.or(bad(format!("method `{mn}` has generic type parameters")));
        }
        if tm.params.iter().skip(1).any(|&t| mentions_self(&p.tys, t)) {
            v = v.or(bad(format!("method `{mn}` references the `Self` type in a parameter")));
        }
        if mentions_self(&p.tys, tm.ret) {
            v = v.or(bad(format!("method `{mn}` references the `Self` type in its return type")));
        }
        let pred_mentions = |pred: &Predicate| match pred {
            Predicate::Trait(b) => p.tys.args(b.value.args).iter().any(|g| g.as_ty().is_some_and(|t| mentions_self(&p.tys, t))),
            Predicate::AssocEq(b) => {
                mentions_self(&p.tys, b.value.ty)
                    || p.tys.args(b.value.trait_args).iter().any(|g| g.as_ty().is_some_and(|t| mentions_self(&p.tys, t)))
            }
            // `where Self: 'static` is the `needs_static` flag below.
            Predicate::TypeOutlives(t, Region::Static) if is_self(&p.tys, GenericArg::Ty(*t)) => false,
            Predicate::TypeOutlives(t, _) => mentions_self(&p.tys, *t),
            Predicate::Outlives(..) => false,
        };
        // rustc keeps the trait dyn compatible under `where Self: Send`
        // (an auto trait) and under any type-outlives bound. Collect
        // drops `'static` bounds (`self_static_bound` reads them for dyn
        // calls); lust does not check the others at dyn calls, so they
        // are unsupported, not violations.
        let rustc_allows = |pred: &&Predicate| match pred {
            Predicate::Trait(b) => {
                let a = p.tys.args(b.value.args);
                a.len() == 1 && is_self(&p.tys, a[0]) && lang.is_auto(b.value.def)
            }
            Predicate::TypeOutlives(..) => true,
            _ => false,
        };
        if own_preds.iter().any(pred_mentions) {
            if own_preds.iter().filter(|q| pred_mentions(q)).all(|q| rustc_allows(&q)) {
                info.unsupported.get_or_insert(format!("`dyn {tname}` with the `Self` bound in the `where` clause of `{mn}`"));
            } else {
                v = v.or(bad(format!("method `{mn}` references the `Self` type in its `where` clause")));
            }
        }
        if let Some(v) = v {
            info.violation.get_or_insert(v);
            continue;
        }
        match recv {
            Some(recv) => {
                let needs_static = where_self_static(p, &tm.def(&p.ast).where_clause);
                info.methods.push(DynMethod { def: mdef, name: mname, recv, needs_static })
            }
            None if tm.self_kind.is_some() => {
                info.uncallable.push((mname, mdef, "it takes `self` by value, and a `dyn` value has no size"))
            }
            None => {}
        }
    }
    stack.pop();
    memo.insert(def, info);
}

/// The trait name for messages.
/// True when a `where` clause bounds `Self` by `'static`. Collect drops
/// lifetime bounds, so this reads the AST.
fn where_self_static(p: &Program, w: &crate::ast::WhereClause) -> bool {
    use crate::ast::{TraitBound, TyExpr, WherePred};
    w.preds.iter().any(|pred| match pred {
        WherePred::Type { ty, bounds, .. } => {
            matches!(p.ast.ty(*ty), TyExpr::Path(segs) if segs.len() == 1 && segs[0].name == p.known.self_type)
                && bounds.iter().any(|b| matches!(b, TraitBound::Lifetime(lt) if p.name(lt.name) == "static"))
        }
        WherePred::Lifetime { .. } => false,
    })
}

pub fn trait_name(p: &Program, def: DefId) -> String {
    p.gx.index.trait_record(def).map_or_else(|| "?".to_string(), |r| p.name(r.name).to_string())
}

/// True when trait `principal` is `want` or has `want` as a supertrait
/// (transitively, through trait records only, so it also answers at
/// collect time, before `dyn_infos` exist). By def only: the fmt traits
/// it serves take no arguments beyond `Self`.
pub fn principal_has_supertrait(p: &Program, principal: DefId, want: DefId) -> bool {
    fn go(p: &Program, cur: DefId, want: DefId, seen: &mut Vec<DefId>) -> bool {
        if cur == want {
            return true;
        }
        if seen.contains(&cur) {
            return false;
        }
        seen.push(cur);
        let Some(rec) = p.gx.index.trait_record(cur) else { return false };
        rec.generics.predicates.iter().any(|pred| match pred {
            Predicate::Trait(b) if b.count == 0 => {
                is_self(&p.tys, p.tys.args(b.value.args)[0]) && go(p, b.value.def, want, seen)
            }
            _ => false,
        })
    }
    go(p, principal, want, &mut Vec::new())
}

/// The vtable key of a dyn type: its principal, or for a dyn with only
/// auto traits (`dyn Send + Sync`) the `Send` trait def with no args, a
/// key no principal can have (auto traits are never principals). That
/// vtable has no methods: drop, size, align, and empty fmt words.
pub fn vtable_key(p: &Program, tys: &impl TyIntern, t: Ty) -> Option<TraitRef> {
    match tys.kind(t) {
        TyKind::Dyn(b, _) => Some(match tys.dyn_bounds(b).principal {
            Some(pr) => pr.value,
            None => auto_only_key(p),
        }),
        _ => None,
    }
}

/// The vtable key of every dyn type with only auto traits (`vtable_key`).
pub fn auto_only_key(p: &Program) -> TraitRef {
    TraitRef { def: p.gx.lang.send, args: EMPTY_ARGS, bindings: EMPTY_BINDINGS }
}

/// The principal trait ref of a dyn type, if `t` is one.
pub fn principal_of(tys: &impl TyIntern, t: Ty) -> Option<TraitRef> {
    match tys.kind(t) {
        TyKind::Dyn(b, _) => tys.dyn_bounds(b).principal.map(|pr| pr.value),
        _ => None,
    }
}

/// The auto traits a dyn type has: written bits plus the ones its
/// principal's supertraits require. Before `dyn_infos` exist (a static's
/// `Sync` check at collect time) the supertraits are walked directly.
pub fn dyn_auto(p: &Program, tys: &impl TyIntern, t: Ty) -> AutoTraits {
    let TyKind::Dyn(b, _) = tys.kind(t) else { return AutoTraits::default() };
    let b = tys.dyn_bounds(b);
    let implied = match b.principal.map(|pr| pr.value.def) {
        Some(d) => match p.gx.dyn_infos.get(&d) {
            Some(i) => i.auto,
            None => {
                let l = &p.gx.lang;
                let has = |want| principal_has_supertrait(p, d, want);
                let has_unwind = |refs| crate::check::unwind::unwind_trait_def(p, refs).is_some_and(has);
                AutoTraits { send: has(l.send), sync: has(l.sync), unpin: has(l.unpin), unwind_safe: has_unwind(false), ref_unwind_safe: has_unwind(true) }
            }
        },
        None => AutoTraits::default(),
    };
    AutoTraits {
        send: b.auto.send || implied.send,
        sync: b.auto.sync || implied.sync,
        unpin: b.auto.unpin || implied.unpin,
        unwind_safe: b.auto.unwind_safe || implied.unwind_safe,
        ref_unwind_safe: b.auto.ref_unwind_safe || implied.ref_unwind_safe,
    }
}

/// The problem with the first dyn type inside `t`, as a diagnostic at
/// `span`: not dyn compatible (L0701) or not supported yet (L0702).
pub fn dyn_type_diag(p: &Program, tys: &impl TyIntern, t: Ty, span: Span) -> Option<Diag> {
    match tys.kind(t) {
        TyKind::Dyn(b, _) => {
            let pr = tys.dyn_bounds(b).principal?.value;
            if let Some(d) = tys.args(pr.args)[1..].iter().find_map(|g| g.as_ty().and_then(|e| dyn_type_diag(p, tys, e, span))) {
                return Some(d);
            }
            let info = p.gx.dyn_infos.get(&pr.def)?;
            let name = trait_name(p, pr.def);
            if let Some((why, item)) = &info.violation {
                return Some(
                    Diag::new(
                        "L0701",
                        span,
                        format!("the trait `{name}` is not dyn compatible: {why}"),
                        "Add `where Self: Sized` to the offending method to keep it out of the vtable, or use generics instead of `dyn`.",
                    )
                    .with_label(*item, "this item makes the trait not dyn compatible"),
                );
            }
            info.unsupported.as_ref().map(|u| crate::check::generics::dyn_not_yet(span, u))
        }
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) => dyn_type_diag(p, tys, e, span),
        // A dyn value has no size, so it cannot be an element (rustc E0277).
        TyKind::Slice(e) | TyKind::Array(e, _) => unsized_dyn_diag(p, tys, e, span).or_else(|| dyn_type_diag(p, tys, e, span)),
        TyKind::Tuple(ts) => {
            let elems = tys.tys_of(ts);
            let n = elems.len();
            elems.iter().enumerate().find_map(|(i, &e)| {
                let unsized_here = if i + 1 < n { unsized_dyn_diag(p, tys, e, span) } else { None };
                unsized_here.or_else(|| dyn_type_diag(p, tys, e, span))
            })
        }
        TyKind::Adt(d, a) => {
            // A dyn arg for a param that needs `Sized` (`Vec<dyn Tr>`);
            // `Box<T: ?Sized>`, `Rc<T: ?Sized>`, `Arc<T: ?Sized>`, their
            // `Weak`s, `RefCell<T: ?Sized>`, and `Mutex<T: ?Sized>` hold
            // dyn values, and their guards point at one.
            let owns_unsized = matches!(
                tys.builtin_of(t),
                Some(
                    BuiltinTy::Boxed
                        | BuiltinTy::Rc
                        | BuiltinTy::Weak
                        | BuiltinTy::Sync(
                            crate::ty::sync::SyncTy::Arc
                                | crate::ty::sync::SyncTy::ArcWeak
                                | crate::ty::sync::SyncTy::Mutex
                                | crate::ty::sync::SyncTy::MutexGuard
                        )
                        | BuiltinTy::RefCell
                        | BuiltinTy::RefGuard
                        | BuiltinTy::RefMutGuard
                )
            );
            let sized_param = |i: usize| {
                if owns_unsized {
                    return false;
                }
                let Some(adt) = p.adt_by_def(d) else { return true };
                let is_param_i = |t: Ty| matches!(p.tys.kind(t), TyKind::Param(q) if q.0 as usize == i);
                p.gx.adt_generics.get(adt.0 as usize).is_none_or(|g| {
                    g.predicates.iter().any(|pred| match pred {
                        Predicate::Trait(b) => {
                            let first = p.tys.args(b.value.args).first().and_then(|g| g.as_ty());
                            b.value.def == p.gx.lang.sized && first.is_some_and(is_param_i)
                        }
                        _ => false,
                    })
                })
            };
            tys.args(a).iter().enumerate().find_map(|(i, g)| {
                let e = g.as_ty()?;
                let unsized_here = if sized_param(i) { unsized_dyn_diag(p, tys, e, span) } else { None };
                unsized_here.or_else(|| dyn_type_diag(p, tys, e, span))
            })
        }
        TyKind::Projection(_, a) | TyKind::FnDef(_, a) | TyKind::Opaque(_, a) => {
            tys.args(a).iter().find_map(|g| g.as_ty().and_then(|e| dyn_type_diag(p, tys, e, span)))
        }
        TyKind::FnPtr(sig) => {
            let s = tys.sig(sig).value;
            tys.tys_of(s.inputs).iter().chain(std::iter::once(&s.output)).find_map(|&e| dyn_type_diag(p, tys, e, span))
        }
        _ => None,
    }
}

/// The size error for a bare dyn type in a position that needs a
/// sized type.
fn unsized_dyn_diag(p: &Program, tys: &impl TyIntern, t: Ty, span: Span) -> Option<Diag> {
    if !matches!(tys.kind(t), TyKind::Dyn(..)) {
        return None;
    }
    Some(Diag::new(
        "L0110",
        span,
        format!("the size for values of type `{}` cannot be known here", crate::check::collect::ty_name(p, tys, t)),
        "Put the dyn value behind a reference: `&dyn Trait`.",
    ))
}

/// True when trait `want` is `principal` or one of its supertraits
/// (by def; the object type implements each of them).
fn implied_by_principal(p: &Program, principal: DefId, want: DefId, seen: &mut Vec<DefId>) -> bool {
    if principal == want {
        return true;
    }
    // The fmt traits ride the header shims, not the super slots.
    if seen.is_empty()
        && ((want == p.gx.lang.debug && principal_has_supertrait(p, principal, want))
            || (want == p.gx.lang.display && principal_has_supertrait(p, principal, want)))
    {
        return true;
    }
    if seen.contains(&principal) {
        return false;
    }
    seen.push(principal);
    let Some(info) = p.gx.dyn_infos.get(&principal) else { return false };
    info.supers.iter().any(|s| implied_by_principal(p, s.def, want, seen))
}

/// The dyn type checks over every signature collect resolved: fn and
/// method signatures (trait methods included), fields, impl headers,
/// and `impl dyn Trait` blocks. A dyn coercion in a const or static
/// initializer is L0702 in `coerce_const_value` (the evaluator builds
/// no vtables). Body types are checked as they resolve.
pub fn check_signatures(p: &Program, errs: &mut Vec<Diag>) {
    use crate::check::generics::FnClass;
    // Every dyn type that resolves names a user trait, so a crate
    // without traits has none to check.
    if p.gx.trait_names.is_empty() {
        return;
    }
    let mut push = |d: Option<Diag>| {
        if let Some(d) = d
            && !errs.iter().any(|e| e.span == d.span && e.code == d.code)
        {
            errs.push(d);
        }
    };
    let sig_diag = |params: &[Ty], ret: Ty, def: &crate::ast::FnDef, push: &mut dyn FnMut(Option<Diag>)| sig_diags(p, params, ret, def, push);
    for (i, f) in p.fns.iter().enumerate() {
        let class = p.gx.fn_class.get(i).copied().unwrap_or_default();
        if !matches!(class, FnClass::Plain | FnClass::Template) || p.gx.trait_methods.contains_key(&p.fn_defs[i]) {
            continue;
        }
        sig_diag(&f.params, f.ret, f.def(&p.ast), &mut push);
    }
    let mut methods: Vec<_> = p.gx.trait_methods.values().collect();
    methods.sort_by_key(|m| m.def(&p.ast).name_span.lo);
    for tm in methods {
        sig_diag(&tm.params, tm.ret, tm.def(&p.ast), &mut push);
    }
    for (a, adt) in p.adts.iter().enumerate() {
        if p.gx.adt_instance_of.get(a).is_some_and(|i| i.is_some()) {
            continue;
        }
        for v in &adt.variants {
            for f in &v.fields {
                push(dyn_type_diag(p, &p.tys, f.ty, adt.span));
            }
        }
    }
    for (_, rec) in p.gx.index.all_impls() {
        if rec.local && rec.synthetic == crate::traits::index::Synthetic::None {
            for g in p.tys.args(rec.trait_ref.args) {
                if let Some(t) = g.as_ty() {
                    push(dyn_type_diag(p, &p.tys, t, rec.span));
                }
            }
            // rustc E0371: `dyn Tr` already implements `Tr` and every
            // supertrait of `Tr`; a written impl would overlap it.
            let self_ty = rec.self_ty(&p.tys);
            if let Some(pr) = principal_of(&p.tys, self_ty)
                && implied_by_principal(p, pr.def, rec.trait_def, &mut Vec::new())
            {
                let (tn, dn) = (trait_name(p, rec.trait_def), trait_name(p, pr.def));
                push(Some(Diag::new(
                    "L0704",
                    rec.span,
                    format!("`dyn {dn}` implements `{tn}` already: the object type implements its trait and every supertrait"),
                    "Remove this impl; calls through the dyn type use the vtable.",
                )));
            }
        }
    }
    for &(t, span) in &p.gx.dyn_impl_sites {
        push(dyn_type_diag(p, &p.tys, t, span));
    }
}

/// The dyn type checks of one signature: each parameter type at its
/// written type's span, then the return type.
fn sig_diags(p: &Program, params: &[Ty], ret: Ty, def: &crate::ast::FnDef, push: &mut dyn FnMut(Option<Diag>)) {
    let skip = usize::from(def.self_param.is_some());
    for (i, param) in def.params.iter().enumerate() {
        if let Some(&t) = params.get(i + skip) {
            push(dyn_type_diag(p, &p.tys, t, p.ast.ty_span(param.ty)));
        }
    }
    let rspan = def.ret.map_or(def.name_span, |t| p.ast.ty_span(t));
    push(dyn_type_diag(p, &p.tys, ret, rspan));
}

/// `check_signatures` for one plain fn or template only: a signature
/// delta runs it for the fn it edited (`delta_audit::redo_sig`).
pub fn check_fn_signature(p: &Program, f: crate::def::LocalDefId, errs: &mut Vec<Diag>) {
    if p.gx.trait_names.is_empty() {
        return;
    }
    let info = p.fn_info(f);
    let mut push = |d: Option<Diag>| {
        if let Some(d) = d
            && !errs.iter().any(|e| e.span == d.span && e.code == d.code)
        {
            errs.push(d);
        }
    };
    sig_diags(p, &info.params, info.ret, info.def(&p.ast), &mut push);
}

/// One object method candidate for a dyn receiver: the trait that owns
/// the method (existential ref, Self is `DYN_SELF`), and either its
/// vtable word index and receiver form, or why it cannot be called.
#[derive(Clone, Debug)]
pub struct ObjectCand {
    pub owner: TraitRef,
    pub def: DefId,
    pub call: Result<(u32, DynRecv), &'static str>,
    /// See `DynMethod::needs_static`.
    pub needs_static: bool,
}

/// The object method candidates named `name` across the principal and
/// its supertraits, each owning trait once (a diamond reaches one trait
/// twice), principal first then supertraits depth-first in declaration
/// order.
pub fn object_cands(p: &Program, tys: &mut impl TyIntern, principal: TraitRef, name: Sym) -> Vec<ObjectCand> {
    let mut out: Vec<ObjectCand> = Vec::new();
    let mut seen: Vec<TraitRef> = Vec::new();
    let mut work = vec![principal];
    while let Some(tr) = work.pop() {
        if seen.contains(&tr) {
            continue;
        }
        seen.push(tr);
        let Some(info) = p.gx.dyn_infos.get(&tr.def) else { continue };
        if let Some(j) = info.methods.iter().position(|m| m.name == name) {
            let m = &info.methods[j];
            out.push(ObjectCand { owner: tr, def: m.def, call: Ok((info.method_slot(j), m.recv)), needs_static: m.needs_static });
        } else if let Some(&(_, def, why)) = info.uncallable.iter().find(|u| u.0 == name) {
            out.push(ObjectCand { owner: tr, def, call: Err(why), needs_static: false });
        }
        let args: Vec<GenericArg> = tys.args(tr.args).to_vec();
        let supers: Vec<TraitRef> = info.supers.iter().map(|s| crate::traits::index::subst_trait_ref_pub(tys, *s, &args)).collect();
        for s in supers.into_iter().rev() {
            work.push(s);
        }
    }
    out
}

/// The super-slot word indexes from a vtable of `from` to one of `to`
/// (a supertrait reached by upcasting), outermost first. Empty when
/// they are the same trait ref; None when `to` is not a supertrait.
/// Bindings take no part (vtables are keyed without them): a caller
/// that coerces checks `to`'s bindings against the source's.
pub fn upcast_path(p: &Program, tys: &mut impl TyIntern, from: TraitRef, to: TraitRef) -> Option<Vec<u32>> {
    fn go(p: &Program, tys: &mut impl TyIntern, from: TraitRef, to: TraitRef, depth: u32) -> Option<Vec<u32>> {
        if from.def == to.def && from.args == to.args {
            return Some(Vec::new());
        }
        if depth > 64 {
            return None;
        }
        let info = p.gx.dyn_infos.get(&from.def)?;
        let args: Vec<GenericArg> = tys.args(from.args).to_vec();
        let supers: Vec<TraitRef> = info.supers.iter().map(|s| crate::traits::index::subst_trait_ref_pub(tys, *s, &args)).collect();
        for (i, s) in supers.into_iter().enumerate() {
            if let Some(mut rest) = go(p, tys, s, to, depth + 1) {
                rest.insert(0, info.super_slot(i));
                return Some(rest);
            }
        }
        None
    }
    go(p, tys, from, to, 0)
}

/// A dyn type with its region erased: the key form for inherent
/// methods and vtables (a `'static` bound changes no method set).
pub fn erase_dyn_region(tys: &mut impl TyIntern, t: Ty) -> Ty {
    match tys.kind(t) {
        TyKind::Dyn(b, Region::Static) => tys.intern(TyKind::Dyn(b, Region::Erased)),
        _ => t,
    }
}

// Object lifetimes. Checked types keep no lifetime names, so a dyn type's
// object lifetime is `'static` (written `+ 'static`, under `&'static`, a
// `'static` default such as `Box<dyn Tr>` in a signature, or a principal
// trait bounded by `'static`, see `dyn_is_static`) or erased. An erased
// one written in a signature (`d: &dyn Tr`, `-> &dyn Tr`) is a caller's
// lifetime; one in a body annotation is inferred, and rustc may pick
// `'static` for it. The borrow checker proves the `'static` uses whose
// object lifetime is a region slot of the types involved (a coercion or
// subtyping into a `'static` object, an `impl dyn Tr` method's receiver;
// region signatures keep rustc's defaults). The others (an `impl X for
// dyn Tr` picked by trait selection, a dyn call to a method with `where
// Self: 'static`) queue a `DynStatic` obligation and pass at body end only when no dyn value in the body can come
// from a non-`'static` source (`Ctx::dyn_static_clean`); otherwise they
// are L0705. That rejects some programs rustc accepts, never the
// reverse.

/// The depth at which the lifetime walks over a type stop. A walk that
/// reaches it has proved nothing, so it answers "cannot prove" (L0705
/// or L0612), never "no error".
pub const LIFETIME_WALK_LIMIT: u32 = 64;

/// True when a dyn type an impl header names as its Self type has a
/// `'static` object lifetime: `impl dyn Tr` and `impl X for dyn Tr` (the
/// default outside a reference), or a written `+ 'static`. `+ '_` takes
/// any lifetime, and so does a dyn behind an elided reference.
pub fn header_dyn_is_static(ast: &crate::ast::Ast, interner: &crate::intern::Interner, t: crate::ast::TyId) -> bool {
    use crate::ast::{TraitBound, TyExpr};
    match ast.ty(t) {
        TyExpr::Paren(inner) => header_dyn_is_static(ast, interner, *inner),
        TyExpr::Dyn { bounds, lifetime, .. } => {
            let written = lifetime.iter().chain(bounds.iter().filter_map(|b| match b {
                TraitBound::Lifetime(lt) => Some(lt),
                _ => None,
            }));
            written.map(|lt| interner.get(lt.name) == "static").next().unwrap_or(true)
        }
        _ => false,
    }
}

/// True when a dyn type's object lifetime is `'static`: written (`+
/// 'static`, `&'static dyn`), or implied by a `'static` bound on its
/// principal trait, which rustc takes as the default even behind `&'a`.
pub fn dyn_is_static(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Dyn(_, Region::Static) => true,
        TyKind::Dyn(..) => principal_of(tys, t).is_some_and(|pr| p.gx.dyn_infos.get(&pr.def).is_some_and(|i| i.static_bound)),
        _ => false,
    }
}

/// True when a dyn type in `t` has an erased object lifetime: written in
/// a signature, that is a caller's lifetime, not `'static`.
pub fn has_erased_dyn(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Dyn(..) => {
            !dyn_is_static(p, tys, t)
                || principal_of(tys, t).is_some_and(|pr| tys.args(pr.args).iter().any(|g| g.as_ty().is_some_and(|e| has_erased_dyn(p, tys, e))))
        }
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => has_erased_dyn(p, tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| has_erased_dyn(p, tys, e)),
        TyKind::Adt(_, a) | TyKind::Closure(_, a) | TyKind::FnDef(_, a) | TyKind::Projection(_, a) => {
            tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| has_erased_dyn(p, tys, e)))
        }
        TyKind::FnPtr(sig) => {
            let s = tys.sig(sig).value;
            has_erased_dyn(p, tys, s.output) || tys.tys_of(s.inputs).iter().any(|&e| has_erased_dyn(p, tys, e))
        }
        _ => false,
    }
}

/// True when the `'static` regions of an impl header picked for `t` need
/// no proof in the body: `t` has no erased dyn object lifetime and no
/// reference (whose lifetime check erases). `impl Lg for Option<Rc<dyn
/// Lg>>` picked for a field's `Option<Rc<dyn Lg>>`.
pub fn static_regions_known(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    fn has_ref(tys: &impl TyIntern, t: Ty) -> bool {
        let args_ref = |a: crate::ty::ArgsId| tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| has_ref(tys, e)));
        match tys.kind(t) {
            TyKind::Ref(..) => true,
            TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => has_ref(tys, e),
            TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| has_ref(tys, e)),
            TyKind::Adt(_, a) | TyKind::Closure(_, a) | TyKind::FnDef(_, a) | TyKind::Projection(_, a) | TyKind::Opaque(_, a) => args_ref(a),
            TyKind::Dyn(..) => principal_of(tys, t).is_some_and(|pr| args_ref(pr.args)),
            TyKind::FnPtr(sig) => {
                let s = tys.sig(sig).value;
                has_ref(tys, s.output) || tys.tys_of(s.inputs).iter().any(|&e| has_ref(tys, e))
            }
            _ => false,
        }
    }
    !has_erased_dyn(p, tys, t) && !has_ref(tys, t)
}

/// True when a dyn type with an erased object lifetime sits in an
/// invariant position of the return type `t`: under `&mut` or `*mut`
/// (other than a dyn pointee of the outer reference or `RefMut`, which a
/// return coerces), a user Adt (lust computes no variance), a fn pointer, or
/// trait args. A body value that flows there gets the caller's object
/// lifetime, so it cannot also be `'static` (`Ctx::dyn_static_clean`).
pub fn has_erased_dyn_invariant(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    use crate::ty::sync::SyncTy;
    fn go(p: &Program, tys: &impl TyIntern, t: Ty, inv: bool, depth: u32) -> bool {
        let args_go = |a: crate::ty::ArgsId, inv: bool| tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| go(p, tys, e, inv, depth + 1)));
        // Too deep to tell: count it as erased, so the body is not clean.
        if depth > LIFETIME_WALK_LIMIT {
            return true;
        }
        match tys.kind(t) {
            TyKind::Dyn(..) => (inv && !dyn_is_static(p, tys, t)) || principal_of(tys, t).is_some_and(|pr| args_go(pr.args, true)),
            TyKind::Ref(_, m, e) | TyKind::RawPtr(m, e) => go(p, tys, e, inv || m.is_mut(), depth + 1),
            TyKind::Slice(e) | TyKind::Array(e, _) => go(p, tys, e, inv, depth + 1),
            TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| go(p, tys, e, inv, depth + 1)),
            TyKind::Adt(_, a) => {
                let covariant = matches!(
                    tys.builtin_of(t),
                    Some(
                        BuiltinTy::Option
                            | BuiltinTy::Result
                            | BuiltinTy::Vec
                            | BuiltinTy::Boxed
                            | BuiltinTy::Rc
                            | BuiltinTy::Weak
                            | BuiltinTy::RefGuard
                            | BuiltinTy::Sync(SyncTy::Arc | SyncTy::ArcWeak | SyncTy::RwLockReadGuard)
                    )
                );
                args_go(a, inv || !covariant)
            }
            TyKind::FnPtr(sig) => {
                let s = tys.sig(sig).value;
                go(p, tys, s.output, true, depth + 1) || tys.tys_of(s.inputs).iter().any(|&e| go(p, tys, e, true, depth + 1))
            }
            TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => args_go(a, true),
            _ => false,
        }
    }
    match tys.kind(t) {
        TyKind::Ref(_, _, e) if matches!(tys.kind(e), TyKind::Dyn(..)) => go(p, tys, e, false, 1),
        // A `RefMut` over `dyn Tr` coerces as `&mut dyn Tr` does.
        TyKind::Adt(_, a)
            if tys.builtin_of(t) == Some(BuiltinTy::RefMutGuard)
                && let Some(e) = tys.args(a).iter().find_map(|g| g.as_ty())
                && matches!(tys.kind(e), TyKind::Dyn(..)) =>
        {
            go(p, tys, e, false, 1)
        }
        _ => go(p, tys, t, false, 0),
    }
}

/// True when a value of type `t` may hold a borrow, so a dyn value made
/// from it may not live for `'static` (rustc E0597, E0310): a reference,
/// a type param, a closure with such a capture, a dyn type with an
/// erased object lifetime, a borrowing std iterator, or anything
/// holding one.
pub fn may_borrow(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    may_borrow_in(p, tys, &[], t)
}

/// `may_borrow` under the param env `env`: a type parameter or
/// projection the env bounds by `'static` (written, or implied by a
/// `'static` trait) holds no borrow. Used where the value must be
/// `'static` (an unsizing to a `'static` dyn type).
pub fn may_borrow_in(p: &Program, tys: &impl TyIntern, env: &[Predicate], t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => {
            !env.iter().any(|q| matches!(q, Predicate::TypeOutlives(x, Region::Static) if *x == t))
        }
        TyKind::Ref(..) | TyKind::Opaque(..) | TyKind::Infer(_) => true,
        // A closure holds its captures: by-ref captures are references.
        TyKind::Closure(_, a) => tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| may_borrow_in(p, tys, env, e))),
        TyKind::Dyn(..) => !dyn_is_static(p, tys, t),
        TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => may_borrow_in(p, tys, env, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| may_borrow_in(p, tys, env, e)),
        // A user Adt with lifetime params (`B<'b>`): check erases them.
        TyKind::Adt(d, a) => {
            tys.is_chars_ty(t)
                || p.gx.adt_lifetimes.get(&d).is_some_and(|v| !v.is_empty())
                || tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| may_borrow_in(p, tys, env, e)))
        }
        TyKind::FnDef(_, a) => tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| may_borrow_in(p, tys, env, e))),
        _ => false,
    }
}

/// `may_borrow_in` without the borrows the borrow checker sees in its
/// region slots: references and dyn object lifetimes. A source that only
/// borrows through those (`&'static str` in a body annotation, a `Box<dyn
/// Tr>` let whose object lifetime rustc infers) may still become a
/// `'static` dyn value: borrowck makes each of their regions outlive
/// `'static` at the coercion (`Rvalue::MakeDyn`) or the call whose bound
/// needs it. A type param, projection, opaque, inference variable, or
/// borrowing std iterator stays check's to reject.
pub fn may_borrow_untracked_in(p: &Program, tys: &impl TyIntern, env: &[Predicate], t: Ty) -> bool {
    fn go(p: &Program, tys: &impl TyIntern, env: &[Predicate], t: Ty, depth: u32) -> bool {
        let args_go = |a: ArgsId| tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| go(p, tys, env, e, depth + 1)));
        if depth > LIFETIME_WALK_LIMIT {
            return true;
        }
        match tys.kind(t) {
            TyKind::Param(_) | TyKind::Projection(..) => may_borrow_in(p, tys, env, t),
            TyKind::Opaque(..) | TyKind::Infer(_) => true,
            TyKind::Dyn(..) => principal_of(tys, t).is_some_and(|pr| args_go(pr.args)),
            TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => go(p, tys, env, e, depth + 1),
            TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| go(p, tys, env, e, depth + 1)),
            TyKind::Closure(_, a) => args_go(a),
            TyKind::Adt(_, a) | TyKind::FnDef(_, a) => tys.is_chars_ty(t) || args_go(a),
            _ => false,
        }
    }
    go(p, tys, env, t, 0)
}

/// True when `t` holds a reference typed `&'static` (lust keeps that
/// region only on references to dyn types).
pub fn has_static_ref(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(Region::Static, ..) => true,
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => has_static_ref(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| has_static_ref(tys, e)),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Projection(_, a) | TyKind::Opaque(_, a) => {
            tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| has_static_ref(tys, e)))
        }
        TyKind::Dyn(..) => principal_of(tys, t).is_some_and(|pr| tys.args(pr.args).iter().any(|g| g.as_ty().is_some_and(|e| has_static_ref(tys, e)))),
        TyKind::FnPtr(sig) => {
            let s = tys.sig(sig).value;
            has_static_ref(tys, s.output) || tys.tys_of(s.inputs).iter().any(|&e| has_static_ref(tys, e))
        }
        _ => false,
    }
}

/// True when an impl header type satisfies a `'static` bound (`trait
/// Tr: 'static`): no reference (an elided one in a header is a lifetime
/// parameter, and lust drops a written `'static` on a non-dyn
/// reference), no dyn type with a shorter object lifetime, and no type
/// parameter without a `'static` bound in the impl's env. `dyn_self`:
/// the header's own dyn Self, which defaults to `'static`.
pub fn header_type_static(p: &Program, env: &[Predicate], t: Ty, dyn_self: bool) -> bool {
    fn go(p: &Program, env: &[Predicate], t: Ty, top: bool, depth: u32) -> bool {
        let args_ok = |a: ArgsId| p.tys.args(a).iter().all(|g| g.as_ty().is_none_or(|e| go(p, env, e, false, depth + 1)));
        if depth > LIFETIME_WALK_LIMIT {
            return false;
        }
        match p.tys.kind(t) {
            TyKind::Ref(..) => false,
            TyKind::Param(_) | TyKind::Projection(..) => env.iter().any(|q| matches!(q, Predicate::TypeOutlives(x, Region::Static) if *x == t)),
            TyKind::Dyn(..) => (top || dyn_is_static(p, &p.tys, t)) && principal_of(&p.tys, t).is_none_or(|pr| args_ok(pr.args)),
            TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => go(p, env, e, false, depth + 1),
            TyKind::Tuple(ts) => p.tys.tys_of(ts).iter().all(|&e| go(p, env, e, false, depth + 1)),
            TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) => args_ok(a),
            _ => true,
        }
    }
    go(p, env, t, dyn_self, 0)
}

/// True when a dyn type occurs anywhere in `t`.
pub fn mentions_dyn(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Dyn(..) => true,
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => mentions_dyn(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| mentions_dyn(tys, e)),
        TyKind::Adt(_, a) => tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| mentions_dyn(tys, e))),
        _ => false,
    }
}

/// The full trait ref a dyn principal stands for at one concrete Self.
pub fn with_self(tys: &mut impl TyIntern, tr: TraitRef, self_ty: Ty) -> TraitRef {
    let mut args: Vec<GenericArg> = tys.args(tr.args).to_vec();
    args[0] = GenericArg::Ty(self_ty);
    let args = tys.intern_args(&args);
    TraitRef { args, ..tr }
}


impl super::Ctx<'_> {
    /// The source `x` of an unsizing coercion to a `'static` dyn type
    /// that may borrow only through regions the borrow checker tracks
    /// (`may_borrow_untracked_in`): the borrow checker proves the bound.
    /// False when check must decide it.
    pub(super) fn bck_static_source(&mut self, x: Ty) -> bool {
        !may_borrow_untracked_in(self.p, &self.tys, self.env(), x)
    }
}

impl super::Ctx<'_> {
    /// True when the borrow checker must see the regions of body
    /// annotation `t` (`record_annotation`, closure param and return
    /// annotations): it names a lifetime, or a type alias whose body holds
    /// `'static` regions (`generics::names_static_alias`).
    pub(super) fn annotation_has_regions(&mut self, t: crate::ast::TyId) -> bool {
        let p = self.p;
        let local = self.body_scope.local_aliases.clone();
        let alias = |n: crate::intern::Sym| {
            local.iter().rev().find(|(m, _)| *m == n).map(|&(_, t)| t).or_else(|| p.aliases.get(&n).copied())
        };
        super::generics::names_lifetime(&p.ast, &p.interner, t)
            || super::generics::names_static_alias(&p.ast, &p.gx.adt_lifetimes, &alias, &mut self.tys, t)
    }
}
