// Method resolution for generic and trait receivers
// (docs/ARCH.md section 2.10; W-TRAITS-CORE in wave A,
// W-CHECK-G after). The builtin and plain inherent dispatch stays
// in `check/mod.rs`; this module is the candidate search used when
// a receiver is a generic Adt application, a type parameter, a
// projection, or a dyn type, and for every trait method.
//
// Probe order is section 2.10 step 2, interleaved with the
// inherent probes `method_call` already makes. It follows rustc:
// candidates match by receiver type, not by Self type. For each
// autoderef step `U` (builtin derefs only in this wave:
// references) the by-value probe takes every method whose
// receiver type is `U`: the by-value methods of `U` itself, and,
// when `U` is `&T` or `&mut T`, the `&self` or `&mut self`
// methods of `T`. Autoref probes (`&U`, then `&mut U`) come
// after. Inherent candidates win over trait candidates in one
// probe; two trait hits in one probe are ambiguous. Every probe
// records its candidate-set reads: inherent probes go through
// the `MethodSet` query, trait probes record `ImplSet` reads
// inside selection.
use super::*;
use crate::ast::{ExprId, SelfKind};
use crate::check::generics::TraitMethodTemplate;
use crate::def::DefId;
use crate::traits::solve::Selection;

/// What a generic method probe found at one receiver form.
pub(super) enum Probe {
    /// The call is resolved; the payload is its return type.
    Hit(Ty),
    /// No candidate in this probe.
    Miss,
    /// The call failed (an error was reported).
    Failed,
}

/// The receiver type a probe form presents to a method whose
/// Self type at this autoderef step is `step`.
fn receiver_for_form(cx: &mut Ctx, step: Ty, form: ReceiverForm) -> Ty {
    match form {
        ReceiverForm::Value => step,
        ReceiverForm::Ref => cx.tys.mk_ref(false, step),
        ReceiverForm::RefMut => cx.tys.mk_ref(true, step),
    }
}

fn autoref_of(form: ReceiverForm) -> Autoref {
    match form {
        ReceiverForm::Value => Autoref::None,
        ReceiverForm::Ref => Autoref::Ref,
        ReceiverForm::RefMut => Autoref::RefMut,
    }
}

/// One receiver-type probe variant at one autoderef step: the
/// Self type whose inherent impls and trait impls are probed,
/// the receiver type a matching method must have, the
/// adjustment lowering applies after the step's derefs, and
/// the `self` form filter for candidate sets. The by-value
/// probe at a reference step has two variants: Self = the step
/// type (by-value methods) and Self = the pointee (`&self`
/// methods, whose receiver type is the step type itself). A
/// pointee hit records one extra deref plus autoref, so the
/// receiver is reborrowed (`&mut *r`), never moved.
#[derive(Clone, Copy)]
pub(super) struct RcvProbe {
    pub self_ty: Ty,
    pub recv_ty: Ty,
    pub autoref: Autoref,
    pub extra_derefs: u8,
    pub filter: ReceiverForm,
}

impl RcvProbe {
    /// The primary variant at one autoderef step and form.
    pub(super) fn at(cx: &mut Ctx, step: Ty, form: ReceiverForm) -> RcvProbe {
        RcvProbe { self_ty: step, recv_ty: receiver_for_form(cx, step, form), autoref: autoref_of(form), extra_derefs: 0, filter: form }
    }
}

/// True when a trait is in scope for method calls on any receiver
/// here: a std prelude trait, or a trait defined in or imported into
/// the current fn's module (per the resolver tables). A bound brings a
/// trait in only for its own type parameter: use `trait_in_scope_at`
/// where the Self type is known. Without resolver tables
/// (collect-only test paths) every local trait counts as in scope,
/// as before.
pub(super) fn trait_in_scope_pub(cx: &mut Ctx, trait_def: DefId) -> bool {
    trait_in_scope(cx, trait_def)
}

/// `trait_in_scope`, or a bound of this body's env names the trait
/// with `self_ty` as its Self and `self_ty` is a type parameter
/// (rustc's inherent candidates from the param env). So `T: Add`
/// gives `x.add(y)` and `T::add` for `x: T`, but not `1i32.add(2)`;
/// a bound on a projection or an opaque type brings nothing in.
pub(super) fn trait_in_scope_at(cx: &mut Ctx, trait_def: DefId, self_ty: Ty) -> bool {
    trait_in_scope(cx, trait_def) || param_bound_names(cx, trait_def, self_ty)
}

/// True when `self_ty` is a type parameter that a bound of this
/// body's env (elaborated, so supertraits count) gives `trait_def`.
pub(super) fn param_bound_names(cx: &mut Ctx, trait_def: DefId, self_ty: Ty) -> bool {
    let t = cx.resolve(self_ty);
    if !matches!(cx.tys.kind(t), TyKind::Param(_)) {
        return false;
    }
    let env = cx.env();
    env.iter().any(|pred| matches!(pred, Predicate::Trait(b) if b.value.def == trait_def && cx.tys.args(b.value.args).first().and_then(|g| g.as_ty()) == Some(t)))
}

fn trait_in_scope(cx: &mut Ctx, trait_def: DefId) -> bool {
    // A `use` in an enclosing block (`use Trait as _;` in a fn body)
    // brings the trait in for the whole block, nested items and
    // closures included, as in rustc. The answer depends only on
    // this body, so no module read is recorded for it.
    if cx.trait_scopes.iter().any(|layer| layer.contains(&trait_def)) {
        return true;
    }
    // Inside a trait impl (its methods, their closures and nested fns)
    // the impl's own trait is in scope for every receiver, as rustc's
    // current trait ref: `self.write_all(..)` in `impl io::Write for S`.
    if cx.enclosing_impl_trait_pub() == Some(trait_def) {
        return true;
    }
    let p = cx.p;
    // A user trait defined in or imported into this module under any
    // name (including `as _`). The query records a `TraitInScope` read:
    // a `use` edit flips the answer without touching any binding this
    // body names.
    if p.gx.trait_names.values().any(|&d| d == trait_def) && p.trait_in_module(&mut cx.out.reads, cx.module, trait_def) {
        return true;
    }
    let lang = &p.gx.lang;
    // Display and Debug are in scope as in rustc: a `use` of the std
    // path or the impl's own trait (W-STD-B, check/fmt.rs); bounds below.
    if (trait_def == lang.display && cx.fmt_trait_in_scope(crate::ast::FmtKind::Display))
        || (trait_def == lang.debug && cx.fmt_trait_in_scope(crate::ast::FmtKind::Debug))
        || (trait_def == lang.borrow && cx.std_trait_imported("borrow", "Borrow"))
        || (trait_def == lang.borrow_mut && cx.std_trait_imported("borrow", "BorrowMut"))
        || (trait_def == lang.any && cx.std_trait_imported("any", "Any"))
        || (trait_def == lang.range_bounds && cx.std_trait_imported("ops", "RangeBounds"))
        // Only the `Hash` derive macro is in the prelude, not the trait.
        || (trait_def == lang.hash && cx.hash_trait_in_scope(trait_def, "Hash"))
        || (trait_def == lang.hasher && cx.hash_trait_in_scope(trait_def, "Hasher"))
        || (trait_def == lang.build_hasher && cx.hash_trait_in_scope(trait_def, "BuildHasher"))
    {
        return true;
    }
    if [
        lang.copy,
        lang.clone,
        lang.partial_eq,
        lang.eq,
        lang.partial_ord,
        lang.ord,
        lang.default,
        lang.drop,
        lang.iterator,
        lang.into_iterator,
        lang.from_iterator,
        // Prelude traits of user iterators and collections (W-STD-B).
        lang.exact_size_iterator,
        lang.double_ended_iterator,
        lang.extend,
        lang.from_str,
        lang.from,
        lang.into,
        // Prelude since Rust 2021 (fx-tryfrom).
        lang.try_from,
        lang.try_into,
        // Prelude conversion traits (W-STD-B).
        lang.as_ref,
        lang.as_mut,
        lang.to_owned,
        lang.to_string,
    ]
    .contains(&trait_def)
    {
        return true;
    }
    // The operator traits, `Deref`, and `Index` are not in the prelude: a
    // method call by name (`1i32.add(2)`, `s.deref()`) needs the trait
    // imported, by name or by a glob of `std::ops`. Operator syntax does
    // not ask; a bound counts for its own param (`trait_in_scope_at`).
    if let Some(name) = ops_trait_name(lang, trait_def) && (cx.std_trait_imported("ops", name) || cx.std_glob("ops")) {
        return true;
    }
    in_template_env(cx, trait_def)
}

/// The `core::ops` name of lang trait `d` when it is one of the operator,
/// `Deref`, or `Index` traits.
fn ops_trait_name(lang: &crate::check::generics::LangTraits, d: DefId) -> Option<&'static str> {
    let table = [
        (lang.deref, "Deref"),
        (lang.deref_mut, "DerefMut"),
        (lang.index, "Index"),
        (lang.index_mut, "IndexMut"),
        (lang.add, "Add"),
        (lang.sub, "Sub"),
        (lang.mul, "Mul"),
        (lang.div, "Div"),
        (lang.rem, "Rem"),
        (lang.neg, "Neg"),
        (lang.not, "Not"),
        (lang.bit_and, "BitAnd"),
        (lang.bit_or, "BitOr"),
        (lang.bit_xor, "BitXor"),
        (lang.shl, "Shl"),
        (lang.shr, "Shr"),
        (lang.add_assign, "AddAssign"),
        (lang.sub_assign, "SubAssign"),
        (lang.mul_assign, "MulAssign"),
        (lang.div_assign, "DivAssign"),
        (lang.rem_assign, "RemAssign"),
        (lang.bit_and_assign, "BitAndAssign"),
        (lang.bit_or_assign, "BitOrAssign"),
        (lang.bit_xor_assign, "BitXorAssign"),
        (lang.shl_assign, "ShlAssign"),
        (lang.shr_assign, "ShrAssign"),
    ];
    table.iter().find(|&&(t, _)| t == d).map(|&(_, n)| n)
}

/// True in an instance body when a bound of its template names trait
/// `trait_def`. An instance re-checks its template with concrete types
/// and an empty env; the template check already held the call to the
/// bound's own param (`trait_in_scope_at`), so the bound still speaks
/// for scope here.
pub(super) fn in_template_env(cx: &mut Ctx, trait_def: DefId) -> bool {
    let p = cx.p;
    if let Some(info) = p.gx.instances.get(&cx.fid)
        && let Some(tl) = info.template_local
        && let Some(fs) = p.gx.fn_scopes.get(tl.0 as usize)
    {
        return fs.env.iter().any(|pred| matches!(pred, Predicate::Trait(b) if b.value.def == trait_def));
    }
    false
}

/// Confirms one method candidate (inherent template, impl
/// template, or trait default template) at a call site:
/// instantiate it, unify the receiver, check the args, and
/// record the resolution. `prefix` are the already-known leading
/// generic args (impl or trait args from selection); `explicit`
/// are the method's own turbofish args. `confirm_method_args` also
/// gives the template's instantiated generic args.
#[allow(clippy::too_many_arguments)]
fn confirm_method(
    cx: &mut Ctx,
    e: ExprId,
    template: LocalDefId,
    generics: &Generics,
    prefix: &[GenericArg],
    explicit: &[Option<GenericArg>],
    probe: RcvProbe,
    derefs: u8,
    args: &[ExprId],
    name_span: Span,
) -> Option<Ty> {
    confirm_method_args(cx, e, template, generics, prefix, explicit, probe, derefs, args, name_span).map(|(t, _)| t)
}

#[allow(clippy::too_many_arguments)]
fn confirm_method_args(
    cx: &mut Ctx,
    e: ExprId,
    template: LocalDefId,
    generics: &Generics,
    prefix: &[GenericArg],
    explicit: &[Option<GenericArg>],
    probe: RcvProbe,
    derefs: u8,
    args: &[ExprId],
    name_span: Span,
) -> Option<(Ty, Vec<GenericArg>)> {
    let snap_vars = cx.snapshot_vars();
    let obl_len = cx.obl_len();
    let sites_len = cx.generic_sites.len();
    let err_len = cx.errs.len();
    let mut full_explicit: Vec<Option<GenericArg>> = prefix.iter().map(|&g| Some(g)).collect();
    full_explicit.extend_from_slice(explicit);
    // A written method turbofish must supply every own param
    // (rustc E0107). With a selection prefix the written args are
    // `explicit`; on the inherent path they are `explicit` after
    // the impl-param padding (`method_explicit`).
    {
        let (offset, written) = if prefix.is_empty() {
            let parent_n = cx.inherent_parent_n(template);
            (parent_n, &explicit[parent_n.min(explicit.len())..])
        } else {
            (prefix.len(), explicit)
        };
        let supplied = if written.is_empty() { None } else { Some(written.iter().filter(|x| x.is_some()).count()) };
        let generics = generics.clone();
        cx.check_turbofish_min(&generics, offset, supplied, name_span);
    }
    let (mut params, ret, targs) = cx.instantiate_template(e, template, generics, &full_explicit, name_span);
    if !prefix.is_empty() {
        cx.obl.deepen_from(obl_len, 1);
    }
    let want_recv = *params.first()?;
    if !cx.unify(want_recv, probe.recv_ty) {
        cx.rollback_vars(snap_vars);
        cx.obl_truncate(obl_len);
        cx.generic_sites.truncate(sites_len);
        cx.errs.truncate(err_len);
        return None;
    }
    // As rustc confirms a method: normalize after the receiver binds
    // the impl's params (check/project.rs).
    cx.normalize_params(&mut params, name_span);
    cx.set_res(e, Res::Method { f: template, derefs: derefs + probe.extra_derefs, autoref: probe.autoref });
    if let Some((ce, want)) = cx.call_expected
        && ce == e
    {
        cx.expected_output_first(ret, Some(want), args);
    }
    cx.check_args(&params[1.min(params.len())..], args, name_span);
    Some((cx.normalize_use(ret, name_span), targs))
}

/// rustc types a call to a trait impl's method with the trait item's
/// signature, so the trait item's bounds hold at the call even when the
/// impl method states looser ones (`trait fn take<T: Clone>`, `impl fn
/// take<T>`: `A.take(NoClone)` is E0277). Pushes the trait item's
/// predicates with the trait ref's args (`tr_args`, Self first) and the
/// impl method's own args (`own`), matched by position over type and
/// const params (an impl may differ in its lifetime params).
pub(super) fn push_trait_item_bounds(cx: &mut Ctx, tmpl: &TraitMethodTemplate, tr_args: &[GenericArg], own: &[GenericArg], span: Span) {
    let tr_args: Vec<GenericArg> = tr_args
        .iter()
        .map(|&g| match g {
            GenericArg::Ty(t) => GenericArg::Ty(cx.deep(t)),
            other => other,
        })
        .collect();
    let mut own_tc = own.iter().copied().filter(|g| !matches!(g, GenericArg::Lifetime(_)));
    let mut args: Vec<GenericArg> = Vec::with_capacity(tmpl.generics.params.len());
    for (i, param) in tmpl.generics.params.iter().enumerate() {
        args.push(match (tr_args.get(i), &param.kind) {
            (Some(&g), _) => g,
            (None, ParamKind::Lifetime) => GenericArg::Lifetime(Region::Erased),
            (None, ParamKind::Type) => own_tc.next().filter(|g| matches!(g, GenericArg::Ty(_))).unwrap_or_else(|| GenericArg::Ty(cx.new_var(false))),
            (None, ParamKind::Const(_)) => own_tc.next().filter(|g| matches!(g, GenericArg::Const(_))).unwrap_or_else(|| GenericArg::Const(cx.fresh_const_var())),
        });
    }
    let preds = tmpl.generics.predicates.clone();
    cx.push_predicates_with(&preds, &args, span, &[]);
}

/// The method-call turbofish args aligned to a template's combined
/// generics: the impl's params come first in the template, so the
/// method's own written args follow that many unwritten slots
/// (rustc binds `x.m::<U>(..)` to the method's params only).
fn method_explicit(cx: &Ctx, template: LocalDefId, explicit: &[Option<GenericArg>]) -> Vec<Option<GenericArg>> {
    let parent_n = cx.p.gx.inherent_self_pats.get(&template).map_or(0, |(_, g)| g.params.len());
    let mut out: Vec<Option<GenericArg>> = vec![None; parent_n];
    out.extend_from_slice(explicit);
    out
}

/// Probes inherent method templates of one probe variant's Self
/// type. Plain inherent methods are `plain_inherent_probe`;
/// this covers the generic ones that path would
/// mis-instantiate. Every registered template is tried: the
/// receiver unify in `confirm_method` keeps only the ones whose
/// impl Self pattern matches this receiver.
#[allow(clippy::too_many_arguments)]
/// The inherent fns of `(adt_def, name)` that take `self`: an
/// associated fn (`fn get(this: &LazyLock<T, F>)`) is no method
/// candidate in rustc, so the probe goes on past it (to a deref
/// target's `get`). None when no method of the name remains.
fn inherent_method_cands(p: &Program, adt_def: DefId, name: Sym) -> Option<Vec<LocalDefId>> {
    let cands: Vec<LocalDefId> = p.gx.inherent_methods.get(&(adt_def, name))?.iter().copied().filter(|&f| p.fn_info(f).self_kind.is_some()).collect();
    (!cands.is_empty()).then_some(cands)
}

pub(super) fn inherent_template_probe(
    cx: &mut Ctx,
    e: ExprId,
    probe: RcvProbe,
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
) -> Probe {
    let p = cx.p;
    let Some((adt_def, _)) = cx.tys.adt_parts(probe.self_ty) else { return Probe::Miss };
    if cx.private_inherent.iter().any(|&(x, a)| x == e && p.def_of_adt(a) == adt_def) {
        return Probe::Miss;
    }
    let Some(templates) = inherent_method_cands(p, adt_def, name) else { return Probe::Miss };
    let templates: Vec<(LocalDefId, crate::check::generics::FnTemplate)> = templates
        .into_iter()
        .filter_map(|t| p.gx.fn_templates.get(t.0 as usize).cloned().flatten().map(|tmpl| (t, tmpl)))
        .collect();
    if templates.is_empty() {
        return Probe::Miss;
    }
    // Record only this probe form, like the plain probe. Recording
    // every form would make probing appear to continue past a hit
    // (the graph reads test spells that contract out).
    let head = Head::of(&cx.tys, probe.self_ty);
    let _ = p.method_set(&mut cx.out.reads, head, name, probe.filter);
    for (template, tmpl) in templates {
        let aligned = method_explicit(cx, template, explicit);
        if let Some(ret) = confirm_method(cx, e, template, &tmpl.generics.clone(), &[], &aligned, probe, derefs, args, name_span) {
            return Probe::Hit(ret);
        }
    }
    Probe::Miss
}

/// How many inherent method templates of the probe's Self type accept
/// its receiver type, by a receiver unify that is rolled back. More
/// than one means the call is ambiguous (rustc E0034: `copied` on an
/// `Option<_>` whose payload is not known yet fits both `Option<&T>`
/// and `Option<&mut T>`); `confirm_method` would take the first.
pub(super) fn inherent_template_fits(cx: &mut Ctx, e: ExprId, probe: RcvProbe, name: Sym, name_span: Span) -> usize {
    let p = cx.p;
    let Some((adt_def, _)) = cx.tys.adt_parts(probe.self_ty) else { return 0 };
    let Some(templates) = inherent_method_cands(p, adt_def, name) else { return 0 };
    let mut n = 0;
    for template in templates {
        let snap_vars = cx.snapshot_vars();
        let obl_len = cx.obl_len();
        let sites_len = cx.generic_sites.len();
        let err_len = cx.errs.len();
        let params = match p.gx.fn_templates.get(template.0 as usize).cloned() {
            Some(Some(tmpl)) => cx.instantiate_template(e, template, &tmpl.generics, &[], name_span).0,
            // A non-generic impl's method (`impl Option<String>`).
            _ => p.fn_info(template).params.clone(),
        };
        if params.first().is_some_and(|&want| cx.unify(want, probe.recv_ty)) {
            n += 1;
        }
        cx.rollback_vars(snap_vars);
        cx.obl_truncate(obl_len);
        cx.generic_sites.truncate(sites_len);
        cx.errs.truncate(err_len);
    }
    n
}

/// Probes the non-generic methods of the lang enums' std impls
/// (`impl Option<String> { fn as_deref .. }`): `inherent_template_probe`
/// covers the generic ones.
#[allow(clippy::too_many_arguments)]
pub(super) fn lang_plain_probe(cx: &mut Ctx, e: ExprId, probe: RcvProbe, derefs: u8, name: Sym, name_span: Span, args: &[ExprId]) -> Probe {
    let p = cx.p;
    let Some((adt_def, _)) = cx.tys.adt_parts(probe.self_ty) else { return Probe::Miss };
    let Some(cands) = inherent_method_cands(p, adt_def, name) else { return Probe::Miss };
    for f in cands {
        if p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
            continue;
        }
        let params = p.fn_info(f).params.clone();
        let ret = p.ret_view(f);
        let snap = cx.snapshot_vars();
        let obl_len = cx.obl_len();
        if params.first().is_none_or(|&want| !cx.unify(want, probe.recv_ty)) {
            cx.rollback_vars(snap);
            cx.obl_truncate(obl_len);
            continue;
        }
        cx.set_res(e, Res::Method { f, derefs: derefs + probe.extra_derefs, autoref: probe.autoref });
        cx.check_args(&params[1.min(params.len())..], args, name_span);
        return Probe::Hit(ret);
    }
    Probe::Miss
}

/// Probes the inherent methods std source defines on a primitive
/// receiver (`impl char` in `core::char`, TRIAGE T8), registered in
/// `prim_inherent_methods`. `base` is the receiver type after
/// `derefs` autoderef steps; the autoref follows the method's own
/// receiver form, as in `lang_plain_probe`.
pub(super) fn prim_inherent_probe(
    cx: &mut Ctx,
    e: ExprId,
    base: Ty,
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
) -> Probe {
    let p = cx.p;
    let Some(cands) = p.gx.prim_inherent_methods.get(&(base, name)).cloned() else { return Probe::Miss };
    for f in cands {
        if p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
            continue;
        }
        let params = p.fn_info(f).params.clone();
        let Some(&want) = params.first() else { continue };
        let (recv_ty, autoref) = match cx.tys.kind(want) {
            TyKind::Ref(_, Mut::Mut, inner) if inner == base => (want, Autoref::RefMut),
            TyKind::Ref(_, Mut::Shared, inner) if inner == base => (want, Autoref::Ref),
            _ => (base, Autoref::None),
        };
        let ret = p.ret_view(f);
        let snap = cx.snapshot_vars();
        let obl_len = cx.obl_len();
        if !cx.unify(want, recv_ty) {
            cx.rollback_vars(snap);
            cx.obl_truncate(obl_len);
            continue;
        }
        cx.set_res(e, Res::Method { f, derefs, autoref });
        cx.check_args(&params[1.min(params.len())..], args, name_span);
        return Probe::Hit(ret);
    }
    Probe::Miss
}

/// Probes trait methods for one receiver-type probe group (the
/// variants of one autoderef step that share a receiver type).
/// Hits are counted across the whole group, as rustc counts
/// candidates in one probe. `expected` is the call's expected
/// result type, when the context gives one: it fixes the input
/// of `Into` (whose method returns that input) and breaks
/// selection ties the way a return-type annotation does in
/// rustc.
#[allow(clippy::too_many_arguments)]
pub(super) fn trait_method_probe(
    cx: &mut Ctx,
    e: ExprId,
    probes: &[RcvProbe],
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
    expected: Option<Ty>,
) -> Probe {
    trait_probe_for(cx, e, None, probes, derefs, name, name_span, args, explicit, expected)
}

/// The checker state a trial check of call arguments adds to, so the
/// trial can be undone in full (`trait_probe_for`'s input trial,
/// `std_extend_item_open`). Closures checked in a trial are checked
/// again for real: their records and parameter locals go too.
pub(super) struct ArgTrial {
    vars: usize,
    obl: usize,
    errs: usize,
    sites: usize,
    picks: usize,
    dmeth: usize,
    closures: usize,
    calls: usize,
    shims: usize,
    locals: usize,
    binops: usize,
    open: usize,
    wait: usize,
    wait_asserts: usize,
    wait_assign_ops: usize,
    sum: usize,
    fmt: usize,
    extends: usize,
}

impl ArgTrial {
    pub(super) fn mark(cx: &mut Ctx) -> Self {
        ArgTrial {
            vars: cx.snapshot_vars(),
            obl: cx.obl_len(),
            errs: cx.errs.len(),
            sites: cx.generic_sites.len(),
            picks: cx.out.trait_picks.len(),
            dmeth: cx.deferred_methods.len(),
            closures: cx.closures.len(),
            calls: cx.out.closure_calls.len(),
            shims: cx.out.fn_shim_calls.len(),
            locals: cx.out.locals.len(),
            binops: cx.deferred_binops.len(),
            open: cx.open_binops.len(),
            wait: cx.wait_binops.len(),
            wait_asserts: cx.wait_asserts.len(),
            wait_assign_ops: cx.wait_assign_ops.len(),
            sum: cx.deferred_sum.len(),
            fmt: cx.deferred_fmt.len(),
            extends: cx.deferred_extend.len(),
        }
    }

    pub(super) fn rollback(self, cx: &mut Ctx) {
        cx.rollback_vars(self.vars);
        cx.obl_truncate(self.obl);
        cx.errs.truncate(self.errs);
        cx.generic_sites.truncate(self.sites);
        cx.out.trait_picks.truncate(self.picks);
        cx.deferred_methods.truncate(self.dmeth);
        cx.closures.truncate(self.closures);
        cx.out.closure_calls.truncate(self.calls);
        cx.out.fn_shim_calls.truncate(self.shims);
        cx.out.locals.truncate(self.locals);
        cx.deferred_binops.truncate(self.binops);
        cx.open_binops.truncate(self.open);
        cx.wait_binops.truncate(self.wait);
        cx.wait_asserts.truncate(self.wait_asserts);
        cx.wait_assign_ops.truncate(self.wait_assign_ops);
        cx.deferred_sum.truncate(self.sum);
        cx.deferred_fmt.truncate(self.fmt);
        cx.deferred_extend.truncate(self.extends);
    }
}

/// `Hash::hash` has no lang signature (its `H: Hasher` parameter has no
/// stub form), but its receiver is `&self`: a derived or std impl still
/// counts as a candidate next to a user trait's `hash` (rustc E0034).
pub(super) fn hash_method_kind(cx: &Ctx, trait_def: DefId, name: Sym) -> Option<SelfKind> {
    (trait_def == cx.p.gx.lang.hash && cx.name(name) == "hash").then_some(SelfKind::Ref)
}

/// `trait_method_probe` over every trait in scope, or over `only`
/// when a template pick or a where clause already fixed the trait
/// (scope was decided there). A confirmed hit is recorded as a
/// template pick (see `picks.rs`).
#[allow(clippy::too_many_arguments)]
pub(super) fn trait_probe_for(
    cx: &mut Ctx,
    e: ExprId,
    only: Option<DefId>,
    probes: &[RcvProbe],
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
    expected: Option<Ty>,
) -> Probe {
    let p = cx.p;
    let traits: Vec<DefId> = match only {
        Some(t) => vec![t],
        None => match p.gx.traits_by_method.get(&name) {
            Some(t) => t.clone(),
            None => return Probe::Miss,
        },
    };
    // First pass: probe every in-scope trait by selection, with
    // rollback, and count the hits at this form.
    // A hit: trait, its method template, the impl method (or
    // default) local, the instantiation prefix, the trait
    // input types selection fixed, the probe variant, and a
    // bridge pair when the selected impl is core's blanket
    // `Into` (the real method is the `From` impl's `from`; the
    // pair is that trait ref's Self and input types).
    #[allow(clippy::type_complexity)]
    let mut hits: Vec<(DefId, Option<TraitMethodTemplate>, LocalDefId, Vec<GenericArg>, Option<Vec<Ty>>, RcvProbe, Option<(Ty, Ty)>)> =
        Vec::new();
    // Traits whose selection stays ambiguous after the argument
    // trial: (trait, method template, inferred inputs, variant).
    let mut deferred: Vec<(DefId, TraitMethodTemplate, Vec<Ty>, RcvProbe)> = Vec::new();
    // Lang traits selection picks an impl for but that have no
    // impl method fn to call (a derived or synthetic impl, or a
    // core default method like `PartialOrd::lt`): rustc counts
    // them as candidates all the same, so they still make a call
    // ambiguous next to a real hit. Alone they stay a miss (the
    // builtin dispatch or the no-method error answers).
    let mut lang_hits: Vec<DefId> = Vec::new();
    for trait_def in traits {
        // A trait out of scope here may still come in through a bound,
        // but only at a probe whose Self is that bound's param.
        let in_scope = only.is_some() || trait_in_scope(cx, trait_def);
        if !in_scope && !probes.iter().any(|pr| param_bound_names(cx, trait_def, pr.self_ty)) {
            continue;
        }
        // rustc picks a std inherent item first here (check/std_inherent.rs).
        if only.is_none() && cx.std_first.contains(&e) && cx.is_user_trait(trait_def) {
            continue;
        }
        let Some(rec) = p.gx.index.trait_record(trait_def).cloned() else { continue };
        let Some(method_def) = rec.method_by_name(name) else { continue };
        // Lang traits have no method templates: the receiver
        // form comes from the lang signature table instead, and
        // the signature from the impl method itself once
        // selection picks it (below).
        let tmpl = p.gx.trait_methods.get(&method_def).cloned();
        if tmpl.as_ref().is_some_and(|t| t.self_kind.is_none()) {
            continue;
        }
        let lang_self_kind = if tmpl.is_none() {
            match p.gx.lang_method_sigs.get(&method_def) {
                Some(sig) => {
                    if sig.self_kind.is_none() {
                        continue;
                    }
                    sig.self_kind
                }
                None => hash_method_kind(cx, trait_def, name),
            }
        } else {
            None
        };
        // An instance replays the template's param-env pick with its
        // trait inputs (`U: Add2<u8>` gives `u16: Add2<u8>`).
        let replayed = if only.is_some() { cx.replayed_trait_ref(e, trait_def) } else { None };
        // Core's blanket `Into`/`TryInto` may hold for any receiver, so
        // rustc's probe stops at the first step and never autoderefs to
        // them: `Box<String>` into an `OsString` is E0277, not `String`'s
        // impl through the deref.
        if (trait_def == p.gx.lang.into || trait_def == p.gx.lang.try_into) && derefs > 0 {
            continue;
        }
        for &probe in probes {
            // rustc picks `into`/`try_into` at the by-value step for any
            // sized receiver (core's blanket `Into` for every `T` may
            // hold there), so an autoref `&S` is never their Self. The
            // blanket needs `T: Sized`, so an unsized place (`v[1..]`,
            // `*s`) skips that step and its Self is the autoref `&S`
            // (which may always hold, so never `&mut S`, and never at a
            // later step: `(&mut v[1..]).into()` stops at `&mut [T]`).
            if (trait_def == p.gx.lang.into || trait_def == p.gx.lang.try_into)
                && probe.autoref != Autoref::None
                && probe.self_ty == probe.recv_ty
                && !(derefs == 0
                    && probe.autoref == Autoref::Ref
                    && matches!(cx.kind(probe.self_ty), TyKind::Ref(_, _, s) if cx.into_self(s).1 != Autoref::None))
            {
                continue;
            }
            if !in_scope && !param_bound_names(cx, trait_def, probe.self_ty) {
                continue;
            }
            let step = probe.self_ty;
            let form = probe.filter;
            // Receiver-form pre-filter for plain receivers; typed
            // receivers are decided by unification in confirm.
            match tmpl.as_ref().and_then(|t| t.self_kind).or(lang_self_kind) {
                Some(SelfKind::Value) if form != ReceiverForm::Value => continue,
                Some(SelfKind::Ref) if form != ReceiverForm::Ref => continue,
                Some(SelfKind::RefMut) if form != ReceiverForm::RefMut => continue,
                // A typed receiver (`self: &Rc<Self>`) matches the one
                // variant whose receiver type it names, with this
                // variant's Self (every variant of a smart pointer step
                // shares the pointee as Self, so a trait impl for the
                // pointee would hit once per variant otherwise).
                Some(SelfKind::Typed) => {
                    let Some(want) = tmpl.as_ref().and_then(|t| t.params.first().copied()) else { continue };
                    let want = subst(&mut cx.tys, want, &[GenericArg::Ty(step)]);
                    let snap = cx.snapshot_vars();
                    let ok = cx.unify(want, probe.recv_ty);
                    cx.rollback_vars(snap);
                    if !ok {
                        continue;
                    }
                }
                _ => {}
            }
            let n_inputs = rec.generics.params.len().saturating_sub(1);
            let snap = cx.snapshot_vars();
            let obl_len = cx.obl_len();
            let mut input_vars: Vec<Ty> = Vec::new();
            let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(step)];
            for i in 0..n_inputs {
                // `Into::into` returns the trait input itself,
                // so an expected result type is that input.
                let t = if let Some(t) = replayed.and_then(|r| cx.tys.args(r.args).get(i + 1).and_then(|g| g.as_ty())) {
                    t
                } else if trait_def == p.gx.lang.into && i == 0 {
                    expected.unwrap_or_else(|| cx.new_var(false))
                } else if trait_def == p.gx.lang.try_into && i == 0 {
                    // `try_into` returns `Result` of the trait input:
                    // an expected `Result` type names it (fx-tryfrom).
                    expected
                        .and_then(|t| { let t = cx.deep(t); cx.tys.result_args(t) })
                        .map(|(ok, _)| ok)
                        .unwrap_or_else(|| cx.new_var(false))
                } else {
                    cx.new_var(false)
                };
                input_vars.push(t);
                tr_args.push(GenericArg::Ty(t));
            }
            let args_id = cx.tys.intern_args(&tr_args);
            let tr = TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS };
            let sel = cx.select_obligation(tr);
            // An impl whose where clauses cannot hold for this receiver
            // is no candidate (`impl<T: Tag> V for T` at a `Box<dyn V>`
            // step): rustc's probe filters them before it picks by
            // autoderef step, so a later step's object or impl
            // candidate still wins.
            if let Selection::Impl { nested, .. } = &sel
                && nested.iter().any(|pr| matches!(pr, Predicate::Trait(b) if b.count == 0 && cx.provably_false(b.value)))
            {
                cx.rollback_vars(snap);
                cx.obl_truncate(obl_len);
                continue;
            }
            let ambiguous = matches!(sel, Selection::Ambiguous);
            // A structural answer (`usize::MAX`: tuples, arrays, refs,
            // dyn objects) has no impl record, like a synthetic impl:
            // it counts as a lang candidate, never as a stub call.
            let was_impl = matches!(sel, Selection::Impl { .. } | Selection::ParamEvidence(usize::MAX));
            let found: Option<(LocalDefId, Vec<GenericArg>, Option<(Ty, Ty)>)> = match sel {
                Selection::Impl { id, args: impl_args, .. } => {
                    let rec_impl = p.gx.index.get(id);
                    let by_name = rec_impl.items.iter().copied().find(|&d| p.local_def(d.hash).is_some_and(|l| p.fn_info(l).name == name));
                    match by_name {
                        Some(d) => p.local_def(d.hash).map(|l| (l, impl_args.clone(), None)),
                        None => {
                            // Core's blanket `Into` has no method
                            // of its own: the call is the selected
                            // `From` impl's `from`, with the
                            // receiver as its argument.
                            // Core's blanket `TryInto` likewise has
                            // no method of its own: the call is the
                            // selected `TryFrom` impl's `try_from`,
                            // with the receiver as its argument
                            // (fx-tryfrom).
                            let bridged = if trait_def == p.gx.lang.try_into && input_vars.len() == 1 {
                                let u = cx.deep(input_vars[0]);
                                let fargs = cx.tys.intern_args(&[GenericArg::Ty(u), GenericArg::Ty(step)]);
                                let ftr = TraitRef { def: p.gx.lang.try_from, args: fargs, bindings: EMPTY_BINDINGS };
                                match cx.select_obligation(ftr) {
                                    Selection::Impl { id: id2, args: args2, .. } => {
                                        let rec2 = p.gx.index.get(id2);
                                        let fname = p
                                            .gx
                                            .index
                                            .trait_record(p.gx.lang.try_from)
                                            .and_then(|r| r.methods.first().map(|m| m.1));
                                        fname
                                            .and_then(|fname| {
                                                rec2.items
                                                    .iter()
                                                    .copied()
                                                    .find(|&d| p.local_def(d.hash).is_some_and(|l| p.fn_info(l).name == fname))
                                            })
                                            .and_then(|d| p.local_def(d.hash))
                                            .map(|l| (l, args2.clone(), Some((u, cx.deep(step)))))
                                    }
                                    Selection::ParamEvidence(i) if i != usize::MAX => p
                                        .gx
                                        .index
                                        .trait_record(p.gx.lang.try_from)
                                        .and_then(|r| r.methods.first().map(|m| m.0))
                                        .and_then(|m| param_env_hit(cx, m, ftr))
                                        .map(|(l, a)| (l, a, Some((u, cx.deep(step))))),
                                    _ => None,
                                }
                            } else if trait_def == p.gx.lang.into && input_vars.len() == 1 {
                                let u = cx.deep(input_vars[0]);
                                let fargs = cx.tys.intern_args(&[GenericArg::Ty(u), GenericArg::Ty(step)]);
                                let ftr = TraitRef { def: p.gx.lang.from, args: fargs, bindings: EMPTY_BINDINGS };
                                match cx.select_obligation(ftr) {
                                    Selection::Impl { id: id2, args: args2, .. } => {
                                        let rec2 = p.gx.index.get(id2);
                                        let fname = p
                                            .gx
                                            .index
                                            .trait_record(p.gx.lang.from)
                                            .and_then(|r| r.methods.first().map(|m| m.1));
                                        fname
                                            .and_then(|fname| {
                                                rec2.items
                                                    .iter()
                                                    .copied()
                                                    .find(|&d| p.local_def(d.hash).is_some_and(|l| p.fn_info(l).name == fname))
                                            })
                                            .and_then(|d| p.local_def(d.hash))
                                            .map(|l| (l, args2.clone(), Some((u, cx.deep(step)))))
                                    }
                                    // A template check: `U: From<T>` in the
                                    // bounds proves it; the call is `from`'s stub.
                                    Selection::ParamEvidence(i) if i != usize::MAX => p
                                        .gx
                                        .index
                                        .trait_record(p.gx.lang.from)
                                        .and_then(|r| r.methods.first().map(|m| m.0))
                                        .and_then(|m| param_env_hit(cx, m, ftr))
                                        .map(|(l, a)| (l, a, Some((u, cx.deep(step))))),
                                    _ => None,
                                }
                            } else {
                                None
                            };
                            // `ToString` at a generic Self: core's blanket over
                            // `T: Display` holds through the bounds, and the call
                            // is the method's stub, as for an env predicate. A
                            // concrete Self misses here: the builtin answers.
                            let generic_self = matches!(cx.tys.kind(cx.resolve(step)), TyKind::Param(_) | TyKind::Projection(..) | TyKind::Opaque(..));
                            let to_string_stub = (trait_def == p.gx.lang.to_string && generic_self)
                                .then(|| p.gx.trait_method_stubs.get(&method_def).copied())
                                .flatten()
                                .map(|stub| {
                                    let args: Vec<GenericArg> = cx.tys.args(tr.args).to_vec();
                                    let args = args.into_iter().map(|g| if let GenericArg::Ty(t) = g { GenericArg::Ty(cx.deep(t)) } else { g }).collect();
                                    (stub, args, None)
                                });
                            bridged.or(to_string_stub).or_else(|| {
                                // The trait default body, as a template.
                                p.local_def(method_def.hash).map(|l| {
                                    let raw: Vec<GenericArg> = cx.tys.args(tr.args).to_vec();
                                    let deep_args: Vec<GenericArg> = raw
                                        .iter()
                                        .map(|&g| match g {
                                            GenericArg::Ty(t) => GenericArg::Ty(cx.deep(t)),
                                            other => other,
                                        })
                                        .collect();
                                    (l, deep_args, None)
                                })
                            })
                        }
                    }
                }
                // Only a real env predicate proves a call through the
                // trait's stub. The stub of a lang method has no body (its
                // FnInfo borrows an unrelated fn's def), so an instance that
                // reached it would run that fn.
                Selection::ParamEvidence(i) if i != usize::MAX => param_env_hit(cx, method_def, tr).map(|(l, a)| (l, a, None)),
                _ => None,
            };
            let zonked_inputs: Option<Vec<Ty>> = if found.is_some() && !input_vars.is_empty() {
                Some(input_vars.iter().map(|&v| cx.deep(v)).collect())
            } else {
                None
            };
            // Roll the probe back either way; the winner re-selects.
            cx.rollback_vars(snap);
            cx.obl_truncate(obl_len);
            if let Some((local, prefix, bridge)) = found {
                hits.push((trait_def, tmpl.clone(), local, prefix, zonked_inputs, probe, bridge));
                continue;
            }
            if was_impl
                && !rec.local
                && trait_def != p.gx.lang.into
                && trait_def != p.gx.lang.try_into
                && !matches!(trait_def, d if d == p.gx.lang.fn_ || d == p.gx.lang.fn_mut || d == p.gx.lang.fn_once)
                && (p.gx.lang_method_sigs.get(&method_def).is_some_and(|s| s.self_kind.is_some())
                    || hash_method_kind(cx, trait_def, name).is_some())
                && !lang_hits.contains(&trait_def)
            {
                lang_hits.push(trait_def);
            }
            // Ambiguous selection with fresh trait inputs is common
            // with one impl per input (`Convert<u8>` and
            // `Convert<u16>` for one Self): the written arguments
            // fix the inputs through the trait method's own
            // signature. Trial-check the arguments against that
            // signature (rolled back in full), then select again
            // with the inferred inputs.
            if ambiguous && let Some(t) = &tmpl {
                let trial = ArgTrial::mark(cx);
                let mut input_vars: Vec<Ty> = Vec::new();
                let mut full: Vec<GenericArg> = vec![GenericArg::Ty(step)];
                for _ in 0..n_inputs {
                    let v = cx.new_var(false);
                    input_vars.push(v);
                    full.push(GenericArg::Ty(v));
                }
                let n_trait_params = rec.generics.params.len();
                for (i, param) in t.generics.params.iter().enumerate().skip(n_trait_params) {
                    let given = explicit.get(i - n_trait_params).copied().flatten();
                    full.push(match (given, &param.kind) {
                        (Some(g), _) => g,
                        (None, ParamKind::Type) => GenericArg::Ty(cx.new_var(false)),
                        (None, ParamKind::Lifetime) => GenericArg::Lifetime(Region::Erased),
                        (None, ParamKind::Const(_)) => GenericArg::Const(cx.fresh_const_var()),
                    });
                }
                let params: Vec<Ty> = t.params.iter().map(|&pt| subst(&mut cx.tys, pt, &full)).collect();
                let want_form = probe.recv_ty;
                let zonked: Option<Vec<Ty>> = if !params.is_empty() && cx.unify(params[0], want_form) {
                    cx.check_args(&params[1..], args, name_span);
                    // A known expected type fixes inputs that
                    // only the return type mentions. A return
                    // type that is still a projection cannot be
                    // unified yet and does not count against
                    // the trial.
                    let ret_ok = match expected {
                        Some(exp) => {
                            let r = subst(&mut cx.tys, t.ret, &full);
                            let r = cx.normalize_here(r);
                            let is_proj = {
                                let d = cx.deep(r);
                                cx.tys.flags(d).contains_projection()
                            };
                            is_proj || cx.unify(r, exp)
                        }
                        None => true,
                    };
                    if ret_ok { Some(input_vars.iter().map(|&v| cx.deep(v)).collect()) } else { None }
                } else {
                    None
                };
                trial.rollback(cx);
                if let Some(inputs) = zonked {
                    let snap = cx.snapshot_vars();
                    let obl_len = cx.obl_len();
                    let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(step)];
                    tr_args.extend(inputs.iter().map(|&t| GenericArg::Ty(t)));
                    let args_id = cx.tys.intern_args(&tr_args);
                    let tr = TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS };
                    let sel = cx.select_obligation(tr);
                    let still_ambiguous = sel == Selection::Ambiguous;
                    let found: Option<(LocalDefId, Vec<GenericArg>)> = match sel {
                        Selection::Impl { id, args: impl_args, .. } => {
                            let rec_impl = p.gx.index.get(id);
                            let by_name =
                                rec_impl.items.iter().copied().find(|&d| p.local_def(d.hash).is_some_and(|l| p.fn_info(l).name == name));
                            match by_name {
                                Some(d) => p.local_def(d.hash).map(|l| (l, impl_args.clone())),
                                None => p.local_def(method_def.hash).map(|l| (l, tr_args.clone())),
                            }
                        }
                        Selection::ParamEvidence(_) => param_env_hit(cx, method_def, tr),
                        _ => None,
                    };
                    cx.rollback_vars(snap);
                    cx.obl_truncate(obl_len);
                    if let Some((local, prefix)) = found {
                        hits.push((trait_def, tmpl.clone(), local, prefix, Some(inputs), probe, None));
                    } else if still_ambiguous {
                        deferred.push((trait_def, t.clone(), inputs, probe));
                    }
                }
            }
        }
    }
    // Typed receivers put several receiver variants of one step in one
    // group (`Rc<N>`, `&Rc<N>`, `&mut Rc<N>`): rustc probes them in that
    // order, so only the hits at the first autoref level that has any
    // compete (`self: Rc<Self>` wins over `self: &Rc<Self>`).
    // The rank is the receiver type against the group's step (the first
    // variant's receiver): the step itself, `&step`, or `&mut step`.
    if let Some(step) = probes.first().map(|pr| pr.recv_ty) {
        let (by_ref, by_mut) = (cx.tys.mk_ref(false, step), cx.tys.mk_ref(true, step));
        let rank = |r: Ty| {
            if r == by_ref {
                1u8
            } else if r == by_mut {
                2
            } else {
                0
            }
        };
        if let Some(best) = hits.iter().map(|h| rank(h.5.recv_ty)).min() {
            hits.retain(|h| rank(h.5.recv_ty) == best);
        }
    }
    // A lang candidate with no callable method fn still ties
    // with a real hit or a deferred call (rustc E0034).
    let lang_only: Vec<DefId> =
        lang_hits.iter().copied().filter(|d| !hits.iter().any(|h| h.0 == *d) && !deferred.iter().any(|h| h.0 == *d)).collect();
    if !lang_only.is_empty() && hits.len() + deferred.len() >= 1 {
        cx.err(
            "L0720",
            name_span,
            format!("multiple trait methods named `{}` apply here", cx.name(name)),
            "Call the method with a fully qualified path, such as `<Type as Trait>::method(...)`.",
        );
        for &a in args {
            cx.expr(a, None);
        }
        return Probe::Failed;
    }
    // Only ambiguous traits: one is the call (its impl is picked at
    // body end), two are ambiguous between traits (rustc E0034).
    if hits.is_empty() && deferred.len() == 1 {
        let (trait_def, t, inputs, probe) = deferred.pop().unwrap();
        return confirm_deferred(cx, e, trait_def, &t, &inputs, probe, derefs, name_span, args, explicit);
    }
    if hits.is_empty() && deferred.len() > 1 {
        cx.err(
            "L0720",
            name_span,
            format!("multiple trait methods named `{}` apply here", cx.name(name)),
            "Call the method with a fully qualified path, such as `<Type as Trait>::method(...)`.",
        );
        for &a in args {
            cx.expr(a, None);
        }
        return Probe::Failed;
    }
    match hits.len() {
        0 => Probe::Miss,
        1 => {
            let (trait_def, tmpl, local, prefix, zonked, probe, bridge) = hits.into_iter().next().unwrap();
            // `Drop::drop` may not be called by hand (rustc
            // E0040); the drop glue calls it, never a method
            // call. A user trait method also named `drop` is a
            // different trait and stays callable.
            if trait_def == p.gx.lang.drop {
                cx.err(
                    "L0110",
                    name_span,
                    "the `drop` method cannot be called directly",
                    "Let the value go out of scope instead.",
                );
                for &a in args {
                    cx.expr(a, None);
                }
                return Probe::Failed;
            }
            let step = probe.self_ty;
            // Re-select to commit the selection bindings and get
            // the confirmed instantiation prefix.
            let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(step)];
            match &zonked {
                Some(inputs) => tr_args.extend(inputs.iter().map(|&t| GenericArg::Ty(t))),
                None => {
                    let n_inputs = prefix.len().saturating_sub(1);
                    for _ in 0..n_inputs {
                        tr_args.push(GenericArg::Ty(cx.new_var(false)));
                    }
                }
            }
            let args_id = cx.tys.intern_args(&tr_args);
            let tr = TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS };
            let mut env_pick: Option<usize> = None;
            let mut impl_method = false;
            let prefix: Vec<GenericArg> = if let Some((u, from_step)) = bridge {
                // Bookkeep the `Into` obligation, then take the
                // instantiation prefix from the `From` impl whose
                // `from` method this call really is. A `try_into`
                // call bridges to `TryFrom` the same way (fx-tryfrom).
                let _ = cx.select_obligation(tr);
                let fdef = if trait_def == p.gx.lang.try_into { p.gx.lang.try_from } else { p.gx.lang.from };
                let fargs = cx.tys.intern_args(&[GenericArg::Ty(u), GenericArg::Ty(from_step)]);
                let ftr = TraitRef { def: fdef, args: fargs, bindings: EMPTY_BINDINGS };
                match cx.select_obligation(ftr) {
                    Selection::Impl { args: args2, .. } => args2,
                    _ => prefix,
                }
            } else {
                match cx.select_obligation(tr) {
                    Selection::ParamEvidence(i) => {
                        env_pick = Some(i);
                        prefix
                    }
                    Selection::Impl { args: impl_args, .. } => {
                        // Impl methods take impl args; trait defaults
                        // take the trait ref args.
                        if p.gx.index.impls_of_trait(trait_def).iter().any(|_| true) && local_is_impl_method(p, local, name) {
                            impl_method = true;
                            impl_args
                        } else {
                            let raw: Vec<GenericArg> = cx.tys.args(tr.args).to_vec();
                            raw.iter()
                                .map(|&g| match g {
                                    GenericArg::Ty(t) => GenericArg::Ty(cx.deep(t)),
                                    other => other,
                                })
                                .collect()
                        }
                    }
                    _ => prefix,
                }
            };
            let generics = match p.gx.fn_templates.get(local.0 as usize).cloned() {
                Some(Some(t)) => t.generics.clone(),
                _ => {
                    // A plain (non-generic) impl method.
                    let (params, ret) = {
                        let info = p.fn_info(local);
                        (info.params.clone(), p.ret_view(local))
                    };
                    let ret = cx.callee_ret(ret);
                    let want_recv = params[0];
                    if !cx.unify(want_recv, probe.recv_ty) {
                        return Probe::Miss;
                    }
                    cx.set_res(e, Res::Method { f: local, derefs: derefs + probe.extra_derefs, autoref: probe.autoref });
                    cx.check_args(&params[1..], args, name_span);
                    if impl_method && let Some(t) = &tmpl {
                        push_trait_item_bounds(cx, t, &tr_args, &[], name_span);
                    }
                    cx.record_pick_probe(e, trait_def, derefs + probe.extra_derefs, probe, None);
                    return Probe::Hit(cx.normalize_here(ret));
                }
            };
            match confirm_method_args(cx, e, local, &generics, &prefix, explicit, probe, derefs, args, name_span) {
                Some((ret, targs)) => {
                    if impl_method && let Some(t) = &tmpl {
                        push_trait_item_bounds(cx, t, &tr_args, &targs[prefix.len().min(targs.len())..], name_span);
                    }
                    cx.record_pick_probe(e, trait_def, derefs + probe.extra_derefs, probe, env_pick);
                    Probe::Hit(ret)
                }
                None => Probe::Miss,
            }
        }
        _ => {
            cx.err(
                "L0720",
                name_span,
                format!("multiple trait methods named `{}` apply here", cx.name(name)),
                "Call the method with a fully qualified path, such as `<Type as Trait>::method(...)`.",
            );
            for &a in args {
                cx.expr(a, None);
            }
            Probe::Failed
        }
    }
}

/// An `as_deref` or `as_deref_mut` call on an `Option` or `Result`
/// whose payload type is still open at the call (fx-option-rest):
/// core has one impl over `T: Deref`, so rustc fixes the payload
/// later in the body; lust's per-type impls all fit an open payload,
/// so the pick waits for body end (`finish_deferred_lang_methods`).
pub(super) struct DeferredLangMethod {
    pub e: ExprId,
    /// The receiver's Self type at the call (its vars may bind later).
    pub base: Ty,
    pub form: crate::driver::graph::ReceiverForm,
    pub derefs: u8,
    pub name: Sym,
    pub name_span: Span,
    /// The fresh return-type variable the call was typed with.
    pub ret: Ty,
    pub explicit: Vec<Option<GenericArg>>,
}

/// Body end for `DeferredLangMethod` calls: with the payload type
/// settled (by the body or by the call's expected result type), pick
/// the one per-type impl that fits, as the call-site probe would.
/// Still-open or still-ambiguous calls keep the L0610 the call site
/// would have reported; a settled payload with no fitting impl is
/// L0104, as for a payload known at the call.
pub(super) fn finish_deferred_lang_methods(cx: &mut Ctx) {
    let p = cx.p;
    for d in std::mem::take(&mut cx.deferred_lang_methods) {
        let base = cx.deep(d.base);
        let probe = RcvProbe::at(cx, base, d.form);
        let fits = inherent_template_fits(cx, d.e, probe, d.name, d.name_span);
        if fits == 1 {
            let hit = match inherent_template_probe(cx, d.e, probe, d.derefs, d.name, d.name_span, &[], &d.explicit) {
                Probe::Miss => lang_plain_probe(cx, d.e, probe, d.derefs, d.name, d.name_span, &[]),
                other => other,
            };
            match hit {
                Probe::Hit(ret) => {
                    if !cx.unify(ret, d.ret) {
                        cx.mismatch(d.name_span, d.ret, ret);
                    }
                }
                Probe::Failed => {}
                Probe::Miss => {
                    cx.err("L0104", d.name_span, format!("no method `{}` on this receiver", cx.name(d.name)), "Check the method name.");
                }
            }
            continue;
        }
        // The expected result type can fix the payload (`let s:
        // Option<&str> = x.as_deref()` picks the String impl): try
        // each candidate against receiver and result together.
        let Some((def, _)) = cx.tys.adt_parts(base) else { continue };
        let Some(cands) = inherent_method_cands(p, def, d.name) else { continue };
        let mut winners: Vec<LocalDefId> = Vec::new();
        for cand in cands {
            let snap_vars = cx.snapshot_vars();
            let obl_len = cx.obl_len();
            let sites_len = cx.generic_sites.len();
            let err_len = cx.errs.len();
            let (params, ret) = match p.gx.fn_templates.get(cand.0 as usize).cloned() {
                Some(Some(tmpl)) => {
                    let aligned = method_explicit(cx, cand, &d.explicit);
                    let (params, ret, _) = cx.instantiate_template(d.e, cand, &tmpl.generics, &aligned, d.name_span);
                    (params, ret)
                }
                _ => (p.fn_info(cand).params.clone(), p.ret_view(cand)),
            };
            let want_ret = cx.deep(d.ret);
            if params.first().is_some_and(|&want| cx.unify(want, probe.recv_ty)) && cx.unify(ret, want_ret) {
                winners.push(cand);
            }
            cx.rollback_vars(snap_vars);
            cx.obl_truncate(obl_len);
            cx.generic_sites.truncate(sites_len);
            cx.errs.truncate(err_len);
        }
        if let [cand] = winners.as_slice() {
            let cand = *cand;
            let hit = match p.gx.fn_templates.get(cand.0 as usize).cloned() {
                Some(Some(tmpl)) => {
                    let aligned = method_explicit(cx, cand, &d.explicit);
                    confirm_method(cx, d.e, cand, &tmpl.generics.clone(), &[], &aligned, probe, d.derefs, &[], d.name_span)
                }
                _ => {
                    let params = p.fn_info(cand).params.clone();
                    if params.first().is_some_and(|&want| cx.unify(want, probe.recv_ty)) {
                        cx.set_res(d.e, Res::Method { f: cand, derefs: d.derefs + probe.extra_derefs, autoref: probe.autoref });
                        Some(p.ret_view(cand))
                    } else {
                        None
                    }
                }
            };
            match hit {
                Some(ret) => {
                    if !cx.unify(ret, d.ret) {
                        cx.mismatch(d.name_span, d.ret, ret);
                    }
                }
                None => {
                    cx.err("L0104", d.name_span, format!("no method `{}` on this receiver", cx.name(d.name)), "Check the method name.");
                }
            }
            continue;
        }
        if cx.tainted_lookup(base) {
            // A follow-up of this body's first error (`tainted_lookup`).
        } else if cx.has_unbound_var(base) || !winners.is_empty() {
            cx.err(
                "L0610",
                d.name_span,
                format!("type annotations needed: more than one `{}` method fits this receiver", cx.name(d.name)),
                "Annotate the receiver's type, for example `let x: Option<&i32> = ..`.",
            );
        } else {
            let tn = cx.tn(base);
            cx.err("L0104", d.name_span, format!("no method `{}` on type `{tn}`", cx.name(d.name)), "Check the method name.");
        }
    }
}

/// A trait method call whose impl selection was still ambiguous at
/// the call: body end selects the impl and sets the resolution.
pub(super) struct DeferredMethod {
    e: ExprId,
    tr: TraitRef,
    name: Sym,
    /// The method's own generic args, after the trait's.
    own: Vec<GenericArg>,
    derefs: u8,
    autoref: Autoref,
    /// A path call (`S::conv(3u8)`, `assoc_call_deferred`): the call
    /// names the impl's fn as `Res::Fn`, not as a method.
    path: bool,
}

/// Records a path call typed by its trait's signature for
/// `finish_deferred_methods` (see `Ctx::assoc_call_deferred`).
pub(super) fn defer_path_call(cx: &mut Ctx, e: ExprId, tr: TraitRef, name: Sym, own: Vec<GenericArg>) {
    cx.deferred_methods.push(DeferredMethod { e, tr, name, own, derefs: 0, autoref: Autoref::None, path: true });
}

/// Queues a call `e` of trait method `name` for `finish_deferred_methods`,
/// which points it at the impl `tr` selects once the body's types are
/// known (`collect` into a std source collection, W-STD-C).
pub(super) fn defer_trait_method(cx: &mut Ctx, e: ExprId, tr: TraitRef, name: Sym, own: Vec<GenericArg>, derefs: u8, autoref: Autoref) {
    cx.deferred_methods.push(DeferredMethod { e, tr, name, own, derefs, autoref, path: false });
}

/// Confirms a trait method whose impl is still ambiguous (an input
/// type only an argument or the expected type fixes, or a literal Self
/// with several numeric impls), as rustc does: the call is typed by the
/// trait's method signature, the trait obligation stays queued (the
/// literal fallback can settle it), and `finish_deferred_methods`
/// selects the impl at body end.
#[allow(clippy::too_many_arguments)]
fn confirm_deferred(
    cx: &mut Ctx,
    e: ExprId,
    trait_def: DefId,
    t: &TraitMethodTemplate,
    inputs: &[Ty],
    probe: RcvProbe,
    derefs: u8,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
) -> Probe {
    let n_trait = 1 + inputs.len();
    let snap = cx.snapshot_vars();
    let obl_len = cx.obl_len();
    let mut full: Vec<GenericArg> = vec![GenericArg::Ty(probe.self_ty)];
    full.extend(inputs.iter().map(|&i| GenericArg::Ty(i)));
    for (i, param) in t.generics.params.iter().enumerate().skip(n_trait) {
        let given = explicit.get(i - n_trait).copied().flatten();
        full.push(match (given, &param.kind) {
            (Some(g), _) => g,
            (None, ParamKind::Type) => GenericArg::Ty(cx.new_var(false)),
            (None, ParamKind::Lifetime) => GenericArg::Lifetime(Region::Erased),
            (None, ParamKind::Const(_)) => GenericArg::Const(cx.fresh_const_var()),
        });
    }
    let mut params: Vec<Ty> = t.params.iter().map(|&pt| subst(&mut cx.tys, pt, &full)).collect();
    let ret = subst(&mut cx.tys, t.ret, &full);
    if params.is_empty() || !cx.unify(params[0], probe.recv_ty) {
        cx.rollback_vars(snap);
        cx.obl_truncate(obl_len);
        return Probe::Miss;
    }
    cx.normalize_params(&mut params, name_span);
    let preds = t.generics.predicates.clone();
    cx.push_predicates(&preds, &full, name_span);
    let tr_args = cx.tys.intern_args(&full[..n_trait]);
    let tr = TraitRef { def: trait_def, args: tr_args, bindings: EMPTY_BINDINGS };
    cx.obl.push_trait_at(tr, name_span, 0);
    let derefs = derefs + probe.extra_derefs;
    cx.deferred_methods.push(DeferredMethod { e, tr, name: t.name, own: full[n_trait..].to_vec(), derefs, autoref: probe.autoref, path: false });
    cx.record_pick_probe(e, trait_def, derefs, probe, None);
    cx.check_args(&params[1..], args, name_span);
    Probe::Hit(cx.normalize_use(ret, name_span))
}

/// Body end for `confirm_deferred` calls: after the hard obligation
/// run, select each trait ref and point the call at the impl method
/// (or the trait default), with its generic site for mono. A trait
/// ref that still does not select was already reported by that run.
pub(super) fn finish_deferred_methods(cx: &mut Ctx) {
    let p = cx.p;
    for d in std::mem::take(&mut cx.deferred_methods) {
        let sel = cx.select_obligation(d.tr);
        // A template's path call the env proves calls the signature stub.
        if d.path
            && let Selection::ParamEvidence(i) = sel
            && i != usize::MAX
            && let Some(m) = p.gx.index.trait_record(d.tr.def).and_then(|r| r.method_by_name(d.name))
            && let Some((stub, _)) = param_env_hit(cx, m, d.tr)
        {
            cx.set_res(d.e, Res::Fn(stub));
            continue;
        }
        // A scalar `try_into` or `try_from` picked once the types
        // were known is the checked cast (fx-tryfrom), as the
        // `From` path call below is `FromCast`.
        if matches!(sel, Selection::ParamEvidence(usize::MAX)) {
            if !d.path && d.tr.def == p.gx.lang.try_into {
                cx.set_res(d.e, Res::PrimOp { kind: PrimOpKind::TryIntoCast, derefs: d.derefs });
                continue;
            }
            if d.path && d.tr.def == p.gx.lang.try_from && let Expr::Call { callee, .. } = p.ast.expr(d.e) {
                cx.set_res(*callee, Res::TryFromCast);
                cx.set_res(d.e, Res::TryFromCast);
                continue;
            }
            if d.path && d.tr.def == p.gx.lang.try_into {
                // `TryInto::try_into(x)` to a scalar target at a
                // path call: the same cast, in assoc form.
                if let Expr::Call { callee, .. } = p.ast.expr(d.e) {
                    cx.set_res(*callee, Res::TryFromCast);
                }
                cx.set_res(d.e, Res::TryFromCast);
                continue;
            }
        }
        let Selection::Impl { id, args: impl_args, .. } = sel else {
            if d.path {
                // `From` by structure: core's identity impl or a numeric
                // widening, picked once the arg's type was known
                // (`S::from(v.pop().unwrap())` before `v.push(S { .. })`):
                // a move or a cast, as `assoc_call`'s FromCast.
                if matches!(sel, Selection::ParamEvidence(usize::MAX))
                    && d.tr.def == p.gx.lang.from
                    && let Expr::Call { callee, .. } = p.ast.expr(d.e)
                {
                    cx.set_res(*callee, Res::FromCast);
                    cx.set_res(d.e, Res::FromCast);
                } else if cx.errs.is_empty() {
                    // The hard run reported a miss; a path call keeps
                    // no unresolved callee even if it did not.
                    path_call_unresolved(cx, d.e);
                }
            }
            continue;
        };
        let rec = p.gx.index.get(id);
        let target = match rec.items.iter().copied().find_map(|x| p.local_def(x.hash).filter(|&l| p.fn_info(l).name == d.name)) {
            Some(l) => Some((l, impl_args)),
            None => p.gx.index.trait_record(d.tr.def).and_then(|r| r.method_by_name(d.name)).and_then(|m| p.local_def(m.hash)).map(|l| {
                let raw: Vec<GenericArg> = cx.tys.args(d.tr.args).to_vec();
                (l, raw.iter().map(|&g| if let GenericArg::Ty(t) = g { GenericArg::Ty(cx.deep(t)) } else { g }).collect())
            }),
        };
        // A blanket `TryInto` selection has no `try_into` fn: the
        // call is the `TryFrom` impl's `try_from` (fx-tryfrom).
        let target = target.or_else(|| {
            if d.tr.def != p.gx.lang.try_into {
                return None;
            }
            let a: Vec<Ty> = cx.tys.args(d.tr.args).iter().filter_map(|g| g.as_ty()).collect();
            let [src, dst] = a[..] else { return None };
            let (dst, src) = (cx.deep(dst), cx.deep(src));
            let fargs = cx.tys.intern_args(&[GenericArg::Ty(dst), GenericArg::Ty(src)]);
            let ftr = TraitRef { def: p.gx.lang.try_from, args: fargs, bindings: EMPTY_BINDINGS };
            let Selection::Impl { id: id2, args: args2, .. } = cx.select_obligation(ftr) else { return None };
            let fname = p.gx.index.trait_record(p.gx.lang.try_from).and_then(|r| r.methods.first().map(|m| m.1))?;
            let items = p.gx.index.get(id2).items.clone();
            items.iter().copied().find_map(|x| p.local_def(x.hash).filter(|&l| p.fn_info(l).name == fname)).map(|l| (l, args2))
        });
        let Some((local, mut prefix)) = target else {
            // A synthetic conversion impl (`Borrow::borrow(x)` on a
            // builtin Self) has no fn: the call is the conversion
            // builtin, as `convert_method` sets for a method call.
            let targs: Vec<Ty> = cx.tys.args(d.tr.args).iter().filter_map(|g| g.as_ty()).collect();
            let conv = targs.get(1).copied().and_then(|target| {
                let target = cx.deep(target);
                let core = cx.deep(targs[0]);
                // A std `From` record (`usize::from(nonzero)`): the
                // conversion builtin, as `.into()` lowers it.
                if d.tr.def == p.gx.lang.from && crate::check::convert::std_from(p, &cx.tys, core, target).is_some() {
                    return Some(Builtin::ConvInto);
                }
                cx.conv_call_builtin(d.tr.def, core, target)
            });
            if let Some(b) = conv {
                let res = if d.path { Res::Builtin(b) } else { Res::BuiltinMethod { b, derefs: d.derefs, autoref: d.autoref } };
                cx.set_res(d.e, res);
                continue;
            }
            if d.path {
                path_call_unresolved(cx, d.e);
            }
            continue;
        };
        if p.gx.fn_templates.get(local.0 as usize).is_some_and(|t| t.is_some()) {
            prefix.extend(d.own.iter().copied());
            let ei = cx.ei(d.e);
            cx.generic_sites.push((ei, local, prefix));
        }
        let res = if d.path { Res::Fn(local) } else { Res::Method { f: local, derefs: d.derefs, autoref: d.autoref } };
        cx.set_res(d.e, res);
    }
}

/// A deferred path call whose selection named no fn to call.
fn path_call_unresolved(cx: &mut Ctx, e: ExprId) {
    let span = cx.span(e);
    cx.err(
        "L0104",
        span,
        "no associated function in the impl this call selects",
        "Name the impl's fn with a qualified path, such as `<Type as Trait>::name`.",
    );
}

/// A call the param env proves (a template check: `t.m()` with
/// `T: Tr` in the bounds): the trait method's signature stub, with
/// the trait ref's args (resolved after selection) as its prefix.
fn param_env_hit(cx: &mut Ctx, method_def: DefId, tr: TraitRef) -> Option<(LocalDefId, Vec<GenericArg>)> {
    let stub = *cx.p.gx.trait_method_stubs.get(&method_def)?;
    let raw: Vec<GenericArg> = cx.tys.args(tr.args).to_vec();
    let prefix = raw
        .iter()
        .map(|&g| match g {
            GenericArg::Ty(t) => GenericArg::Ty(cx.deep(t)),
            other => other,
        })
        .collect();
    Some((stub, prefix))
}

/// True when `local` is a method written in an impl (not a trait
/// default template): its template, if any, is keyed by impl
/// generics, not trait generics.
fn local_is_impl_method(p: &Program, local: LocalDefId, _name: Sym) -> bool {
    let def = p.def_id(local);
    // Covered by the def (`LUST_CHECK_READS`): a method's path is its impl's
    // header (def.rs `method_path`), so whether it is an impl item is fixed
    // while the def exists.
    crate::driver::read_cover::muted(|| p.gx.index.all_impls().any(|(_, rec)| rec.items.contains(&def)))
}

/// The plain inherent probe of one variant, through the
/// recorded `MethodSet` query (as `method_call` makes it), for
/// non-template inherent methods. Every candidate in the set is
/// tried; templates are left to `inherent_template_probe`, and
/// associated fns (no `self`) never match here (the fallback in
/// `method_call` reports them when nothing else applies).
#[allow(clippy::too_many_arguments)]
pub(super) fn plain_inherent_probe(
    cx: &mut Ctx,
    e: ExprId,
    probe: RcvProbe,
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
) -> Probe {
    let p = cx.p;
    let head = Head::of(&cx.tys, probe.self_ty);
    let set = p.method_set(&mut cx.out.reads, head, name, probe.filter);
    // A private inherent method is skipped (`private_inherent`).
    if matches!(head, Head::Adt(d) if cx.private_inherent.iter().any(|&(x, a)| x == e && p.def_of_adt(a) == d)) {
        return Probe::Miss;
    }
    for c in set.candidates {
        let Some(f) = p.local_def(c.def.hash) else { continue };
        if c.receiver.is_none() {
            continue;
        }
        if p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
            continue; // the template probe handles it
        }
        // A mono instance of an inherent template: the template probe
        // handles the call too, so the template's bounds are proved at
        // every call (`lust build` checks after mono made the instance).
        if p.gx.fn_class.get(f.0 as usize) == Some(&crate::check::generics::FnClass::Instance) {
            continue;
        }
        let (params, ret) = match p.sig_of(&mut cx.out.reads, c.def) {
            SigOf::Fn(info) => (info.params.clone(), p.ret_view(f)),
            _ => continue,
        };
        let ret = cx.callee_ret(ret);
        // The candidate set is keyed by the reference-peeled head
        // and by the template Adt, so it also surfaces methods
        // whose receiver type or impl Self pattern does not match
        // this receiver (a `&self` method of `S` at a `&S` step
        // under form `Ref`, where lowering would pass `&&S`, or a
        // method of `impl W<u8>` for a `W<u32>` receiver). Unify
        // the method's receiver type with what this variant
        // presents (as `confirm_method` does) and probe on when
        // they differ.
        let snap_vars = cx.snapshot_vars();
        let obl_len = cx.obl_len();
        let want_recv = params.first().copied();
        if want_recv.is_none_or(|want| !cx.unify(want, probe.recv_ty)) {
            cx.rollback_vars(snap_vars);
            cx.obl_truncate(obl_len);
            continue;
        }
        // A turbofish on a method that is not generic names
        // nothing (the compat dispatch in check/mod.rs reports
        // the same when generics are absent).
        if !explicit.is_empty() {
            cx.rollback_vars(snap_vars);
            cx.obl_truncate(obl_len);
            cx.errs.push(crate::diag::not_yet("L0721", name_span, "turbofish on method calls"));
            for &a in args {
                cx.expr(a, None);
            }
            return Probe::Failed;
        }
        cx.set_res(e, Res::Method { f, derefs: derefs + probe.extra_derefs, autoref: probe.autoref });
        cx.check_args(&params[1.min(params.len())..], args, name_span);
        return Probe::Hit(ret);
    }
    Probe::Miss
}

/// The std supertraits of dyn principal `principal` (Debug, Display,
/// Hasher, ..., whose methods are not vtable methods and so are not in
/// `object_cands`; Debug or Display also as the principal itself) that
/// declare a method `name` of receiver form `form`. They are object
/// candidates too, in scope or not: with `trait U: Debug { fn fmt(&self)
/// }`, `dyn U`'s `x.fmt()` is ambiguous in rustc (E0034).
fn std_super_cands(
    cx: &Ctx,
    principal: DefId,
    name: Sym,
    form: ReceiverForm,
    cands: &[(usize, crate::check::object::ObjectCand)],
) -> Vec<DefId> {
    let p = cx.p;
    let mut seen: Vec<DefId> = Vec::new();
    let mut work = vec![principal];
    let mut n = Vec::new();
    while let Some(cur) = work.pop() {
        if seen.contains(&cur) {
            continue;
        }
        seen.push(cur);
        let Some(rec) = p.gx.index.trait_record(cur) else { continue };
        // `dyn Debug` / `dyn Display` have dyn infos with no vtable
        // methods: their `fmt` is still a candidate here, also as the
        // principal itself.
        if (cur != principal || cur == p.gx.lang.debug || cur == p.gx.lang.display)
            && !p.gx.dyn_infos.get(&cur).is_some_and(|i| i.methods.iter().any(|m| m.name == name))
            && !cands.iter().any(|(_, c)| c.owner.def == cur)
            && let Some(m) = rec.method_by_name(name)
        {
            let kind =
                p.gx.trait_methods.get(&m).and_then(|t| t.self_kind).or_else(|| p.gx.lang_method_sigs.get(&m).and_then(|t| t.self_kind));
            let same = match kind {
                Some(SelfKind::Ref) => form == ReceiverForm::Ref,
                Some(SelfKind::RefMut) => form == ReceiverForm::RefMut,
                Some(SelfKind::Value | SelfKind::Typed) => form == ReceiverForm::Value,
                None => false,
            };
            if same {
                n.push(cur);
            }
        }
        for pred in &rec.generics.predicates {
            if let Predicate::Trait(b) = pred
                && b.count == 0
                && cx
                    .tys
                    .args(b.value.args)
                    .first()
                    .and_then(|g| g.as_ty())
                    .is_some_and(|t| matches!(cx.tys.kind(t), TyKind::Param(ParamId(0))))
            {
                work.push(b.value.def);
            }
        }
    }
    n
}

/// The inherent probe of a dyn step (ARCH 2.8, 2.10): methods of
/// `impl dyn Trait` blocks and the object candidates (methods of the
/// principal and its supertraits, which need no import) are both
/// inherent here, as in rustc, so two of them at one receiver form are
/// ambiguous (rustc E0034). An object method calls through the vtable.
/// With `only`, a replayed template pick: just the object candidates of
/// that trait, as the generic body resolved `<T as Tr>::m` (picks.rs).
#[allow(clippy::too_many_arguments)]
pub(super) fn dyn_probe(
    cx: &mut Ctx,
    e: ExprId,
    probe: RcvProbe,
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
    only: Option<DefId>,
) -> Probe {
    use crate::check::object::{self, DynRecv};
    let p = cx.p;
    // At step `&dyn P` the by-value group's pointee variant probes
    // `dyn P` for `&self` methods, ahead of any trait method that needs
    // an autoref there (a blanket `impl<T: ?Sized> Tr for &T`), as in
    // rustc; the call reborrows through the step.
    let (step, form, derefs) = (probe.self_ty, probe.filter, derefs + probe.extra_derefs);
    let Some(principal) = object::principal_of(&cx.tys, step) else { return Probe::Miss };
    let form_of = |k: Option<SelfKind>| match k {
        Some(SelfKind::Value) | Some(SelfKind::Typed) => Some(ReceiverForm::Value),
        Some(SelfKind::Ref) => Some(ReceiverForm::Ref),
        Some(SelfKind::RefMut) => Some(ReceiverForm::RefMut),
        None => None,
    };
    let key = object::erase_dyn_region(&mut cx.tys, step);
    let inherent = if only.is_some() { None } else { p.gx.dyn_inherent.get(&(key, name)).copied() };
    if let Some(f) = inherent
        && form_of(p.fn_info(f).self_kind).is_none()
    {
        if form == ReceiverForm::Value {
            cx.err(
                "L0104",
                name_span,
                format!("`{}` is an associated function, not a method", cx.name(name)),
                "Call it as `<dyn Trait>::name(...)`.",
            );
            return Probe::Failed;
        }
        return Probe::Miss;
    }
    let inherent = inherent.filter(|&f| form_of(p.fn_info(f).self_kind) == Some(form));
    let cands: Vec<(usize, object::ObjectCand)> = object::object_cands(p, &mut cx.tys, principal, name)
        .into_iter()
        .enumerate()
        .filter(|(_, c)| only.is_none_or(|t| c.owner.def == t))
        .filter(|(_, c)| match c.call {
            Ok((_, DynRecv::Ref)) => form == ReceiverForm::Ref,
            Ok((_, DynRecv::RefMut)) => form == ReceiverForm::RefMut,
            Err(_) => p.gx.trait_methods.get(&c.def).and_then(|t| form_of(t.self_kind)) == Some(form),
        })
        .collect();
    let std_supers = if only.is_some() { Vec::new() } else { std_super_cands(cx, principal.def, name, form, &cands) };
    if inherent.is_some() as usize + cands.len() + std_supers.len() > 1 {
        cx.err(
            "L0720",
            name_span,
            format!("multiple applicable items named `{}` are in scope for this `dyn` receiver", cx.name(name)),
            "Call the method with a fully qualified path, such as `Trait::method(receiver)`.",
        );
        for &a in args {
            cx.expr(a, None);
        }
        return Probe::Failed;
    }
    if let Some(f) = inherent {
        // A generic method of an `impl dyn Tr` block (`downcast_ref::<T>`):
        // instantiated like an inherent template. Its impl has no params
        // of its own here (the template's params are all the method's),
        // so a turbofish binds them in order.
        if let Some(Some(tmpl)) = p.gx.fn_templates.get(f.0 as usize).cloned() {
            let own = p.fn_info(f).def(&p.ast).generics.params.iter().filter(|g| !matches!(g, ast::GenericParam::Lifetime { .. })).count();
            if own != tmpl.generics.params.len() {
                cx.errs.push(crate::check::generics::dyn_not_yet(name_span, "generic `impl dyn Trait` blocks"));
                return Probe::Failed;
            }
            cx.check_dyn_method_vis(f, name_span);
            return match confirm_method(cx, e, f, &tmpl.generics, &[], explicit, probe, derefs, args, name_span) {
                Some(ret) => Probe::Hit(ret),
                None => Probe::Miss,
            };
        }
        cx.check_dyn_method_vis(f, name_span);
        let (params, ret) = {
            let info = p.fn_info(f);
            (info.params.clone(), p.ret_view(f))
        };
        let ret = cx.callee_ret(ret);
        cx.set_res(e, Res::Method { f, derefs, autoref: probe.autoref });
        cx.check_args(&params[1.min(params.len())..], args, name_span);
        return Probe::Hit(ret);
    }
    // The one candidate is `fmt` of a Display or Debug supertrait (`dyn U`
    // with `U: Display`): that trait's builtin call, which formats through
    // the vtable's fmt shim. It needs no import, like any object candidate.
    if cands.is_empty()
        && let [d] = std_supers[..]
        && (d == p.gx.lang.display || d == p.gx.lang.debug)
    {
        let kind = if d == p.gx.lang.display { crate::ast::FmtKind::Display } else { crate::ast::FmtKind::Debug };
        return Probe::Hit(cx.set_fmt_call(e, kind, derefs, probe.autoref, name_span, args));
    }
    let Some((ci, c)) = cands.into_iter().next() else { return Probe::Miss };
    let slot = match c.call {
        Ok((slot, _)) => slot,
        Err(why) => {
            let tn = cx.tn(step);
            cx.err(
                "L0703",
                name_span,
                format!("the method `{}` cannot be called on `{tn}`: {why}", cx.name(name)),
                "Call it on a concrete type, or on a generic parameter bounded by the trait.",
            );
            for &a in args {
                cx.expr(a, None);
            }
            return Probe::Failed;
        }
    };
    let Some(tm) = p.gx.trait_methods.get(&c.def) else { return Probe::Miss };
    let (tparams, tret) = (tm.params.clone(), tm.ret);
    // The method's signature with Self as the dyn type and the owner
    // trait's params from the receiver's principal.
    let mut sargs: Vec<GenericArg> = cx.tys.args(c.owner.args).to_vec();
    sargs[0] = GenericArg::Ty(step);
    let params: Vec<Ty> = tparams.iter().map(|&t| subst(&mut cx.tys, t, &sargs)).collect();
    let ret = subst(&mut cx.tys, tret, &sargs);
    let cand = u8::try_from(ci).expect("at most 256 object candidates");
    cx.set_res(e, Res::DynMethod { owner: c.owner.def, cand, slot, derefs, autoref: probe.autoref });
    if c.needs_static && !object::dyn_is_static(p, &cx.tys, step) {
        cx.obl.push(crate::check::obligations::Obligation::DynStatic { span: name_span });
    }
    cx.check_args(&params[1.min(params.len())..], args, name_span);
    Probe::Hit(cx.normalize_here(ret))
}

/// The full generic method search over autoderef steps, in
/// rustc's receiver-type probe order. Returns Hit/Miss/Failed
/// like a single probe.
#[allow(clippy::too_many_arguments)]
/// The comparison trait of a method call (`eq`, `partial_cmp`, `cmp`,
/// ...) whose argument rustc types differently from a plain coercion to
/// the written impl's `&Self`: on a `&mut` receiver of an Adt (rustc's
/// `Self` is the `&mut A` itself, through core's blanket impls) or on a
/// std type with several `PartialEq`/`PartialOrd` impls in std that
/// lust's source does not all have (`cmp_rhs_open`). The search still
/// picks the impl; `cmp_arg_rule` then checks the argument's own type.
fn cmp_needs_rustc_rhs(cx: &mut Ctx, recv_ty: Ty, name: Sym) -> Option<DefId> {
    let lang = cx.p.gx.lang;
    let trait_def = match cx.p.interner.get(name) {
        "eq" | "ne" => lang.partial_eq,
        "lt" | "le" | "gt" | "ge" | "partial_cmp" => lang.partial_ord,
        "cmp" => lang.ord,
        _ => return None,
    };
    let rt = cx.resolve(recv_ty);
    // The Adt under every reference decides; `Self` keeps the outer
    // references but one shared one (`&&OsStr` compares as `&OsStr`).
    let mut adt_ty = rt;
    while let TyKind::Ref(_, _, inner) = cx.tys.kind(adt_ty) {
        adt_ty = cx.resolve(inner);
    }
    let a = cx.tys.local_adt(adt_ty)?;
    let self_ty = match cx.tys.kind(rt) {
        TyKind::Ref(_, Mut::Mut, _) => return Some(trait_def),
        TyKind::Ref(_, _, inner) => cx.resolve(inner),
        _ => rt,
    };
    (std_display_path(cx.p, a) && trait_def != lang.ord && cx.cmp_rhs_open(self_ty, trait_def)).then_some(trait_def)
}

/// True when Adt `a` is a std type (spliced source or lust's std
/// platform crate): its display path is under `std`, `core`, or `alloc`.
pub(super) fn std_display_path(p: &Program, a: AdtId) -> bool {
    let path = p.display_path(p.adt(a).name);
    ["std::", "core::", "alloc::"].iter().any(|r| path.starts_with(r))
}

/// `Iterator` methods lust has no port of that other std traits also
/// name (`PartialEq::eq`, `PartialOrd::partial_cmp`, `Ord::max`, ...).
const ITER_SHADOWED: &[&str] = &["eq", "ne", "lt", "le", "gt", "ge", "partial_cmp", "cmp", "max", "min"];

/// True when the receiver type `step` (the first autoderef step) is an
/// iterator Adt, or a `&mut` or `Box` of one (core's impls make those
/// iterators too), and `name` is one of its by-value `Iterator` methods
/// in `ITER_SHADOWED`: rustc's by-value probe finds it before the
/// autoref'd comparison traits (`it.eq(&other)` is `Iterator::eq`), so
/// the search must not go on to them. A `&I` receiver is no iterator:
/// there `PartialEq::eq` takes the step as is. `max` and `min` are
/// lust's own iterator consumers unless the type is also `Ord` (then
/// rustc reports the two by-value candidates, E0034).
fn iterator_shadows(cx: &mut Ctx, step: Ty, name: Sym) -> bool {
    let n = cx.p.interner.get(name);
    if !ITER_SHADOWED.contains(&n) {
        return false;
    }
    let step = match cx.tys.kind(step) {
        TyKind::Ref(_, Mut::Mut, inner) => cx.resolve(inner),
        _ => cx.tys.boxed_elem(step).map_or(step, |e| cx.resolve(e)),
    };
    if cx.tys.local_adt(step).is_none() {
        return false;
    }
    let holds = |cx: &mut Ctx, def: DefId| {
        let args = cx.tys.intern_args(&[GenericArg::Ty(step)]);
        matches!(cx.select_obligation(TraitRef { def, args, bindings: EMPTY_BINDINGS }), Selection::Impl { .. } | Selection::ParamEvidence(_))
    };
    let lang = cx.p.gx.lang;
    holds(cx, lang.iterator) && (!matches!(n, "max" | "min") || holds(cx, lang.ord))
}

/// The reject for an `iterator_shadows` call (L0640: the `Iterator`
/// method is declared, lust has no port; L0104 for rustc's E0034).
/// `eq`/`ne` on the iterator Adt itself are lust's builtin
/// `Iterator::eq` (check/iter.rs, through `ByNext`), taken here, at
/// rustc's by-value step, before any autoref'd `PartialEq::eq` or
/// inherent `&self` method.
fn iterator_shadow_reject(cx: &mut Ctx, e: ExprId, step: Ty, name: Sym, name_span: Span, args: &[ExprId], expected: Option<Ty>) -> Probe {
    let n = cx.p.interner.get(name).to_string();
    if matches!(n.as_str(), "eq" | "ne")
        && cx.tys.local_adt(step).is_some()
        && let Expr::MethodCall { recv, .. } = cx.p.ast.expr(e)
        && let Some(t) = cx.iter_method(e, *recv, step, step, 0, name, name_span, args, &[], expected)
    {
        return Probe::Hit(t);
    }
    let tn = cx.tn(step);
    if matches!(n.as_str(), "max" | "min") {
        let msg = format!("multiple applicable items in scope: `{n}` of `Iterator` and of `Ord` for `{tn}`");
        cx.err("L0104", name_span, msg, format!("Call it as `Iterator::{n}(x)` or `Ord::{n}(x, y)`."));
    } else {
        let msg = format!("the iterator method `{n}` (Rust picks `Iterator::{n}` on `{tn}`) is not implemented yet");
        cx.err("L0640", name_span, msg, "Compare with `==` or the comparison trait's path, such as `PartialEq::eq(&a, &b)`.");
    }
    for &a in args {
        cx.expr(a, None);
    }
    Probe::Failed
}

pub(super) fn generic_method_search(
    cx: &mut Ctx,
    e: ExprId,
    recv_ty: Ty,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
    expected: Option<Ty>,
) -> Probe {
    let cmp_trait = cmp_needs_rustc_rhs(cx, recv_ty, name);
    let hit = method_search_steps(cx, e, recv_ty, name, name_span, args, explicit, expected);
    if let (Some(tr), Probe::Hit(_), [a]) = (cmp_trait, &hit, args) {
        let at = cx.out.expr_ty[cx.ei(*a)];
        cx.cmp_arg_rule(recv_ty, at, tr, *a, name);
    }
    hit
}

/// The step+form search of `generic_method_search`.
#[allow(clippy::too_many_arguments)]
fn method_search_steps(
    cx: &mut Ctx,
    e: ExprId,
    recv_ty: Ty,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
    expected: Option<Ty>,
) -> Probe {
    // Autoderef steps through references and `Box` (the builtin
    // derefs of this wave), each with its deref count for lowering.
    // A final array step unsizes to a slice step at the same deref
    // count, as in rustc: `b"x\0".name()` reaches an impl for
    // `[u8]` there. The flag marks that step; its autoref is a
    // `SliceOf` of the array place (`Autoref::SliceRef`).
    let mut steps: Vec<(Ty, u8, bool)> = Vec::new();
    let mut cur = cx.resolve(recv_ty);
    for derefs in 0..32u8 {
        steps.push((cur, derefs, false));
        match cx.tys.kind(cur) {
            TyKind::Ref(_, _, inner) => cur = cx.resolve(inner),
            _ => match cx.tys.smart_elem(cur) {
                Some(inner) => cur = cx.resolve(inner),
                None => break,
            },
        }
    }
    // `Vec<T>` derefs to `[T]` and `String` to `str` the same way
    // (their builtin `Deref` impls), with the slice made from the
    // place (`SliceOf`, `StringAsStr`).
    if let Some(&(last, derefs, _)) = steps.last() {
        let unsized_step = match cx.tys.kind(last) {
            TyKind::Array(el, _) => Some(cx.tys.intern(TyKind::Slice(el))),
            _ if last == STRING => Some(STR),
            _ => cx.tys.vec_elem(last).map(|el| cx.tys.intern(TyKind::Slice(el))),
        };
        if let Some(t) = unsized_step {
            steps.push((t, derefs, true));
        }
    }
    // Through a user `Deref` (`method_via_user_deref`), `recv_ty` is
    // the `&Target` that `deref()` returns, but rustc's step is the
    // target place itself: `&Target` is no step of its own.
    if cx.user_deref_call == Some(e) && steps.len() > 1 && matches!(cx.tys.kind(steps[0].0), TyKind::Ref(..)) {
        steps.remove(0);
    }
    for (step, derefs, unsize) in steps {
        // One group per receiver type, in probe order: by value
        // (the step type itself; at a reference step this group
        // also has the pointee variant), then `&step`, then
        // `&mut step`. Inherent probes run for every variant of
        // the group before the group's trait probe.
        let mut by_value = vec![RcvProbe::at(cx, step, ReceiverForm::Value)];
        if let Some(elem) = cx.tys.smart_elem(step) {
            // Typed receivers on the pointee's impls (`self:
            // Box<Self>`, `self: &Rc<Self>`, kin) match by
            // receiver type at this step (ARCH 2.10 step 3).
            // They bucket as Value, so the filter stays Value
            // while the receiver type carries the real form.
            let elem = cx.resolve(elem);
            by_value.push(RcvProbe { self_ty: elem, recv_ty: step, autoref: Autoref::None, extra_derefs: 0, filter: ReceiverForm::Value });
            by_value.push(RcvProbe {
                self_ty: elem,
                recv_ty: cx.tys.mk_ref(false, step),
                autoref: Autoref::Ref,
                extra_derefs: 0,
                filter: ReceiverForm::Value,
            });
            by_value.push(RcvProbe {
                self_ty: elem,
                recv_ty: cx.tys.mk_ref(true, step),
                autoref: Autoref::RefMut,
                extra_derefs: 0,
                filter: ReceiverForm::Value,
            });
        }
        if let TyKind::Ref(_, m, inner) = cx.tys.kind(step) {
            by_value.push(RcvProbe {
                self_ty: cx.resolve(inner),
                recv_ty: step,
                autoref: if m == Mut::Mut { Autoref::RefMut } else { Autoref::Ref },
                extra_derefs: 1,
                filter: if m == Mut::Mut { ReceiverForm::RefMut } else { ReceiverForm::Ref },
            });
        }
        // The unsize step has no by-value probe (an unsized Self
        // is never held by value); its autorefs make the slice
        // reference from the array place instead of a plain ref.
        let (by_value, ref_probe, refmut_probe) = if unsize {
            (
                Vec::new(),
                RcvProbe {
                    self_ty: step,
                    recv_ty: cx.tys.mk_ref(false, step),
                    autoref: Autoref::SliceRef,
                    extra_derefs: 0,
                    filter: ReceiverForm::Ref,
                },
                RcvProbe {
                    self_ty: step,
                    recv_ty: cx.tys.mk_ref(true, step),
                    autoref: Autoref::SliceRefMut,
                    extra_derefs: 0,
                    filter: ReceiverForm::RefMut,
                },
            )
        } else {
            (by_value, RcvProbe::at(cx, step, ReceiverForm::Ref), RcvProbe::at(cx, step, ReceiverForm::RefMut))
        };
        // At an autoref the receiver `&step` is also the Self type of
        // by-value methods (`impl Tr for &S { fn m(self) }`), as in
        // rustc, where any method whose receiver type is `&step` fits.
        let autoref_self = |pr: RcvProbe| RcvProbe { self_ty: pr.recv_ty, filter: ReceiverForm::Value, ..pr };
        // `&mut str` from a `String` place is not lowered: no `&mut` probe there.
        let refmut_group = if unsize && step == STR { Vec::new() } else { vec![refmut_probe, autoref_self(refmut_probe)] };
        let iter_shadow = !unsize && derefs == 0 && iterator_shadows(cx, step, name);
        let groups = [by_value, vec![ref_probe, autoref_self(ref_probe)], refmut_group];
        for (gi, group) in groups.iter().enumerate() {
            if gi == 1 && iter_shadow {
                return iterator_shadow_reject(cx, e, step, name, name_span, args, expected);
            }
            for &probe in group {
                match dyn_probe(cx, e, probe, derefs, name, name_span, args, explicit, None) {
                    Probe::Miss => {}
                    hit => return hit,
                }
                match plain_inherent_probe(cx, e, probe, derefs, name, name_span, args, explicit) {
                    Probe::Miss => {}
                    hit => return hit,
                }
                match inherent_template_probe(cx, e, probe, derefs, name, name_span, args, explicit) {
                    Probe::Miss => {}
                    hit => return hit,
                }
                match super::picks::where_clause_probe(cx, e, probe, derefs, name, name_span, args, explicit, expected) {
                    Probe::Miss => {}
                    hit => return hit,
                }
            }
            match trait_method_probe(cx, e, group, derefs, name, name_span, args, explicit, expected) {
                Probe::Miss => {}
                hit => return hit,
            }
            match fmt_ptr_probe(cx, e, group, derefs, name, name_span, args, explicit) {
                Probe::Miss => {}
                hit => return hit,
            }
        }
    }
    Probe::Miss
}

/// `x.fmt(f)` where a group's `&self` Self type is a std pointer to a dyn
/// object (`Box<dyn U>`, `Rc<dyn U>`, `&dyn U`): the fmt traits in scope
/// that the pointer implements are rustc's extension candidates at this
/// step, ahead of the object candidates of the dyn step below it. One is
/// the call; two are ambiguous (rustc E0034).
#[allow(clippy::too_many_arguments)]
fn fmt_ptr_probe(
    cx: &mut Ctx,
    e: ExprId,
    group: &[RcvProbe],
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
) -> Probe {
    if cx.p.interner.get(name) != "fmt" || args.len() != 1 || !explicit.is_empty() {
        return Probe::Miss;
    }
    for &probe in group {
        if probe.filter != ReceiverForm::Ref {
            continue;
        }
        let s = cx.resolve(probe.self_ty);
        let mut cur = s;
        loop {
            cur = match cx.tys.kind(cur) {
                TyKind::Ref(_, _, inner) => cx.resolve(inner),
                _ => match cx.tys.smart_elem(cur) {
                    Some(inner) => cx.resolve(inner),
                    None => break,
                },
            };
        }
        if cur == s || !matches!(cx.tys.kind(cur), TyKind::Dyn(..)) {
            continue;
        }
        match cx.fmt_traits_of(s)[..] {
            [] => {}
            [k] => return Probe::Hit(cx.set_fmt_call(e, k, derefs + probe.extra_derefs, probe.autoref, name_span, args)),
            _ => {
                cx.err(
                    "L0104",
                    name_span,
                    "multiple applicable items in scope: `fmt` of `Display` and of `Debug`",
                    "Call it as `fmt::Display::fmt(&value, f)` or `fmt::Debug::fmt(&value, f)`.",
                );
                for &a in args {
                    cx.expr(a, None);
                }
                return Probe::Failed;
            }
        }
    }
    Probe::Miss
}
