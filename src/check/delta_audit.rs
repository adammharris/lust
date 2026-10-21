// What a fn signature delta does with each table of a kept `Program`
// (docs: /home/theo/lust-scratch/sigedit/PLAN.md, P2). The delta takes a
// collected program, swaps one fn's signature in with `install_fn`, and
// reruns the checks that read it; the result must equal a fresh collect
// of the edited Ast. Each field below names its rule:
//
// - same: no fn header can change it while the item outline stands
//   (names, types, impls, traits, consts other than `init_names`).
// - replace: `install_fn` rewrites the edited fn's entry in it.
// - rerun: a check or pass that reads it runs again for the edited fn.
// - refuse: an edit that could change it falls back to a full collect.
// - item: the item patch owns it (Ast, resolver tables).
//
// Completeness: `Program` and `GenTables` are destructured with no `..`,
// so a new field fails to compile here until it states its rule. The
// digest hashes the fields a signature delta writes or reads, so a cold
// collect before and after a refactor (LUST_PROGRAM_DIGEST) and a warm
// delta against a cold collect can be compared field by field.
use super::collect::{self, FnLoc, FnSite, Install, ParentGen, Program};
use super::generics::{self, FnClass, GenTables};
use crate::def::LocalDefId;
use crate::diag::Diag;
use std::fmt::Write as _;
use std::hash::Hasher;

/// Feeds `Debug` text into a hasher without building the string.
struct HashWriter(std::collections::hash_map::DefaultHasher);

impl std::fmt::Write for HashWriter {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.0.write(s.as_bytes());
        Ok(())
    }
}

fn h(x: &dyn std::fmt::Debug) -> u64 {
    let mut w = HashWriter(Default::default());
    let _ = write!(w, "{x:?}");
    w.0.finish()
}

/// One hash per signature-relevant table of `p`, by field name. Type
/// ids are hashed as ids: two programs agree only when they interned
/// the same types in the same order (the bar for a cold refactor).
pub fn digest(p: &Program) -> Vec<(&'static str, u64)> {
    let Program {
        ast: _,                      // item
        interner: _,                 // item (append-only)
        known: _,                    // same
        tys: _,                      // append-only store; ids in the tables below
        defs,                        // replace (the fn's generics and sig)
        adts: _,                     // same
        fns,                         // replace
        consts: _,                   // refuse: a fn in `init_names` falls back
        const_names: _,              // same
        const_defs: _,               // same
        static_defs: _,              // same
        assoc_const_names: _,        // same
        impl_assoc_consts: _,        // same
        trait_assoc_const_values: _, // same
        statics: _,                  // refuse (`init_names`)
        static_names: _,             // same
        body_items,                  // same (nested fns are body edits)
        body_type_items: _,          // same
        item_blocks: _,              // same (spans move with prog_shift)
        body_consts: _,              // refuse (`init_names`)
        const_values,                // refuse (`init_names`)
        scope_of_stmt: _,            // same
        fn_siblings: _,              // same
        const_body_reads: _,         // const_body::check_dirty (reuse_kept)
        const_sites_shape: _,        // same
        type_names: _,               // same
        drop_adts: _,                // same
        aliases: _,                  // same
        fn_names,                    // same (outline)
        methods,                     // same (outline)
        main,                        // refuse: main is never patched
        krate: _,                    // same
        stable_crate: _,             // same
        fn_defs,                     // same (the fn's hash stands)
        def_by_hash,                 // same
        std_fns: _,                  // same (std splice edits refuse)
        shipped_ranges: _,           // same
        resolved: _,                 // item
        gx,
        record_reads: _, // same
        unwind: _,       // same
        overflow_checks: _, // same
        debug_assertions: _, // same
        unwind_tables: _,   // same
        regions,         // replace (`fns`, `opaque_sigs`); rerun (outlives)
        fp_memo: _,      // the driver clears it
        impl_parents,    // same (impl headers stand)
        reuse_stamp: _,  // the driver sets it (`patch::keep`)
        verified: _,     // the driver clears it (`compile`)
        outer_params: _, // rebuilt for a new Ast (`outer_param_names_in`)
        const_goals: _,  // same (const fns refuse)
    } = p;
    let fn_defs_data: Vec<_> = fn_defs.iter().map(|&d| defs.get(d)).collect();
    let mut out = vec![
        ("fns", h(fns)),
        ("fn_defs", h(fn_defs)),
        ("defs", h(&fn_defs_data)),
        ("def_by_hash", h(def_by_hash)),
        ("fn_names", h(fn_names)),
        ("methods", h(methods)),
        ("main", h(main)),
        ("body_items", h(body_items)),
        ("const_values", h(const_values)),
        ("impl_parents", h(&sorted(impl_parents.iter().map(|(k, v)| (*k, (&v.generics, &v.scope, v.impl_item)))))),
        ("region_fns", h(&sorted(regions.fns.iter()))),
        ("region_opaque_sigs", h(&sorted(regions.opaque_sigs.iter()))),
    ];
    gen_digest(gx, &mut out);
    out
}

/// A map's entries in a fixed order (by the key's `Debug` text), so the
/// hash does not depend on the map's insertion history.
fn sorted<K: std::fmt::Debug, V>(it: impl Iterator<Item = (K, V)>) -> Vec<(K, V)> {
    let mut v: Vec<(String, (K, V))> = it.map(|e| (format!("{:?}", e.0), e)).collect();
    v.sort_by(|a, b| a.0.cmp(&b.0));
    v.into_iter().map(|e| e.1).collect()
}

fn gen_digest(gx: &GenTables, out: &mut Vec<(&'static str, u64)>) {
    let GenTables {
        lang: _,                  // same
        index: _,                 // same: impl records do not hold fn sigs
        trait_names: _,           // same
        trait_scopes: _,          // same
        trait_methods: _,         // refuse: trait method decls are never patched
        lang_method_sigs: _,      // refuse: lang methods are never patched
        trait_assoc_defaults: _,  // same
        trait_unsafe: _,          // same
        trait_assoc_consts: _,    // same
        wf_headers: _,            // same (impl headers)
        adt_info: _,              // same
        adt_lifetimes: _,         // same
        generic_aliases: _,       // same
        adt_generics: _,          // same
        adt_envs: _,              // same
        adt_scopes: _,            // same
        adt_instance_of: _,       // rerun (materialize)
        fn_templates,             // replace
        fn_scopes,                // replace
        fn_class,                 // replace; the class must stand
        instances,                // rerun (materialize)
        closures: _,              // rerun (body checks)
        closure_fns: _,           // rerun (body checks)
        template_closures: _,     // rerun (template checks)
        template_calls: _,        // rerun (template checks)
        instance_by_key,          // rerun (materialize)
        inherent_methods,         // same (outline)
        inherent_tmpls: _,        // derived from inherent_methods
        prim_inherent_methods: _, // same (std splice)
        inherent_self_pats,       // same (impl headers)
        inherent_impl_self: _,    // same
        inherent_const_self: _,   // same
        assoc_const_tmpls: _,     // same
        traits_by_method: _,      // same
        drop_methods: _,          // same (trait impl methods refuse)
        glue_methods: _,          // same
        clone_from_methods: _,    // same
        pcmp_methods: _,          // same
        ref_default_methods: _,   // same
        fmt_methods: _,           // same
        deferred_debug_fields: _, // same
        hasher_methods: _,        // same
        fmt_write_methods: _,     // same
        build_hashers: _,         // same
        iter_methods: _,          // same
        written_hash: _,          // same
        hash_impls: _,            // same
        dyn_keys: _,              // same
        generic_hash: _,          // same
        borrow_impls: _,          // same
        has_generics,             // refuse: the fn class stands
        user_generics,            // refuse: the fn class stands
        cow_fns: _,               // refuse (the whole-Ast Cow scan)
        mono_counts,              // rerun (materialize)
        template_checks,          // rerun (materialize)
        trait_picks: _,           // rerun (body checks)
        trait_method_stubs: _,    // same
        walk_instances: _,        // same
        reuse: _,                 // the driver's cache
        dyn_infos: _,             // same (traits)
        vtables: _,               // rerun (materialize)
        vtable_by_key: _,         // rerun (materialize)
        dyn_inherent,             // same (impl headers)
        dyn_impl_sites: _,        // same
        static_dyn_impls: _,      // same
        static_dyn_fns,           // same (impl headers)
        eager_dyn_traits,         // same (a `dyn` header stands only while the Ast names this set)
        mono_done: _,             // rerun
        inst_order: _,            // the driver's order
        template_rows: _,         // rerun
        adt_created: _,           // rerun (materialize)
        turn_marks: _,            // rerun (materialize)
        derive_marks: _,          // same
        written_projections: _,   // replace (normalize_fn_sig)
        item_index: _,            // same
        param_defaults: _,        // same
        opaques,                  // replace
        opaque_ret_of,            // rerun (reveal)
        opaque_hidden,            // rerun (reveal)
        anon_wants: _,            // same (an anon const edit refuses reuse_kept)
    } = gx;
    out.extend([
        ("fn_templates", h(fn_templates)),
        ("fn_scopes", h(fn_scopes)),
        ("fn_class", h(fn_class)),
        ("instances", h(&sorted(instances.iter()))),
        ("instance_by_key", h(&sorted(instance_by_key.iter()))),
        ("inherent_methods", h(&sorted(inherent_methods.iter()))),
        ("inherent_self_pats", h(&sorted(inherent_self_pats.iter()))),
        ("has_generics", h(&(has_generics, user_generics))),
        ("mono_counts", h(mono_counts)),
        ("template_checks", h(&sorted(template_checks.iter()))),
        ("dyn_inherent", h(&sorted(dyn_inherent.iter()))),
        ("static_dyn_fns", h(static_dyn_fns)),
        ("eager_dyn_traits", h(eager_dyn_traits)),
        ("opaques", h(&sorted(opaques.iter()))),
        ("opaque_ret_of", h(&sorted(opaque_ret_of.iter()))),
        ("opaque_hidden", h(&sorted(opaque_hidden.iter()))),
    ]);
}

/// Appends `p`'s digest to the file `LUST_PROGRAM_DIGEST` names, one
/// line per collect, when the variable is set (a test hook; see the
/// module docs).
pub fn dump_if_asked(p: &Program, errors: usize) {
    static PATH: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    let Some(path) = PATH.get_or_init(|| std::env::var("LUST_PROGRAM_DIGEST").ok()) else { return };
    let mut line = format!("errors={errors}");
    for (k, v) in digest(p) {
        let _ = write!(line, " {k}={v:016x}");
    }
    line.push('\n');
    use std::io::Write as _;
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
        let _ = f.write_all(line.as_bytes());
    }
}

/// Collect's work for one fn's signature, done again over the
/// program's Ast (a header delta of the kept program): the record under
/// its cached parent (`Program::impl_parents`) written over the old one,
/// then the checks `finish_collect` runs over signatures, in its order
/// (dyn types, written WF, outlives), then normalization. Err when the fn
/// would not stay a plain fn or a template with the same parameter kinds,
/// or when its `impl Trait` return comes or
/// goes (`rpit`: the fn defines one before the edit; without it, any
/// `impl Trait` refuses). Diagnostics go to `errs`. The caller reveals
/// the hidden type of an `impl Trait` return again.
pub(crate) fn redo_sig(p: &mut Program, f: LocalDefId, rpit: bool, errs: &mut Vec<Diag>) -> Result<(), &'static str> {
    let (ast, interner, known) = (p.ast.clone(), p.interner.clone(), p.known.clone());
    let info = p.fn_info(f);
    let (loc, owner) = (info.loc, info.owner);
    let fdef = p.def_id(f);
    let (parent_gen, parent) = match loc {
        FnLoc::Item(_) => (ParentGen::default(), None),
        FnLoc::Impl(item, _) => (p.impl_parents.get(&item).cloned().ok_or("sig loc")?, p.defs.get(fdef).and_then(|d| d.parent)),
        _ => return Err("sig loc"),
    };
    let site = FnSite { loc, owner, self_ty: parent_gen.scope.self_ty, parent, hash: fdef.hash };
    let rec = collect::fn_record(p, &ast, &interner, &known, site, &parent_gen, errs);
    // A template stays one with the same parameter kinds: instance
    // arguments and the param env key on them.
    let kinds = |g: &crate::ty::Generics| g.params.iter().map(|q| q.kind).collect::<Vec<_>>();
    let old_kinds = p.gx.fn_templates[f.0 as usize].as_ref().map(|t| kinds(&t.generics));
    if old_kinds != rec.is_template().then(|| kinds(rec.generics())) {
        return Err("sig class");
    }
    if rec.has_opaque() != rpit {
        return Err("sig rpit");
    }
    if !errs.is_empty() {
        return Err("sig diag");
    }
    collect::install_fn(p, rec, Install::Replace(f));
    // A trait impl method: `finish_trait_impl` compares it with the trait
    // method before the signature checks run.
    if loc_is_trait_impl(p, loc) && !generics::redo_impl_method(p, f, errs) {
        return Err("sig loc");
    }
    if !errs.is_empty() {
        return Err("sig diag");
    }
    crate::check::object::check_fn_signature(p, f, errs);
    generics::check_fn_wf(p, f, errs);
    crate::check::outlives::check_queued(p, errs);
    generics::normalize_fn_sig(p, f.0 as usize);
    Ok(())
}

/// True for a method of a trait impl.
fn loc_is_trait_impl(p: &Program, loc: FnLoc) -> bool {
    matches!(loc, FnLoc::Impl(item, _) if matches!(&p.ast.items[item as usize].kind, crate::ast::ItemKind::Impl(imp) if imp.trait_ref.is_some()))
}

/// The record of one fn as `redo_sig` finds it: `undo` writes it back,
/// so a delta that hits a diagnostic leaves the kept program as it was
/// (sigedit PLAN R9). These are every table `install_fn(Replace)` and the
/// signature kernels write for the fn (`normalize_fn_sig` rewrites the
/// params and return); new types the record interned stay, unread.
pub(crate) struct SigUndo {
    f: LocalDefId,
    fn_sig: (Option<crate::ast::SelfKind>, Vec<crate::ty::Ty>, crate::ty::Ty, Option<usize>, bool),
    def: Option<(crate::ty::Generics, crate::ty::defs::SigData)>,
    template: Option<generics::FnTemplate>,
    scope: generics::FnScope,
    class: FnClass,
    regions: (Option<crate::borrowck::RegionSig>, Option<crate::borrowck::RegionSig>),
    opaque: (crate::def::DefId, Option<generics::OpaqueInfo>),
    /// The opaque return a revealed fn keeps (`reveal_again` writes it).
    opaque_ret: Option<crate::ty::Ty>,
}

/// Takes fn `f`'s record before `redo_sig` (see `SigUndo`).
pub(crate) fn sig_undo(p: &Program, f: LocalDefId) -> SigUndo {
    let (i, info, def) = (f.0 as usize, p.fn_info(f), p.def_id(f));
    let od = generics::opaque_def(def);
    SigUndo {
        f,
        fn_sig: (info.self_kind, info.params.clone(), info.ret, info.ret_borrows_from, info.is_const),
        def: p.defs.get(def).map(|d| (d.generics.clone(), d.sig.clone())),
        template: p.gx.fn_templates[i].clone(),
        scope: p.gx.fn_scopes[i].clone(),
        class: p.gx.fn_class[i],
        regions: (p.regions.fns.get(&f).cloned(), p.regions.opaque_sigs.get(&f).cloned()),
        opaque: (od, p.gx.opaques.get(&od).cloned()),
        opaque_ret: p.gx.opaque_ret_of.get(&f).copied(),
    }
}

/// Writes back what `sig_undo` took.
pub(crate) fn undo(p: &mut Program, u: SigUndo) {
    let (i, def) = (u.f.0 as usize, p.def_id(u.f));
    let info = &mut p.fns[i];
    (info.self_kind, info.params, info.ret, info.ret_borrows_from, info.is_const) = u.fn_sig;
    if let (Some(d), Some((g, sig))) = (p.defs.get_mut(def), u.def) {
        (d.generics, d.sig) = (g, sig);
    }
    (p.gx.fn_templates[i], p.gx.fn_scopes[i], p.gx.fn_class[i]) = (u.template, u.scope, u.class);
    for (map, old) in [(&mut p.regions.fns, u.regions.0), (&mut p.regions.opaque_sigs, u.regions.1)] {
        match old {
            Some(r) => map.insert(u.f, r),
            None => map.remove(&u.f),
        };
    }
    match u.opaque.1 {
        Some(o) => p.gx.opaques.insert(u.opaque.0, o),
        None => p.gx.opaques.remove(&u.opaque.0),
    };
    match u.opaque_ret {
        Some(t) => p.gx.opaque_ret_of.insert(u.f, t),
        None => p.gx.opaque_ret_of.remove(&u.f),
    };
    p.regions.outlives_items.clear();
}

/// Reveals plain fn `f`'s own `impl Trait` again from its body under
/// its new signature, as `reveal_plain` does in collect. The hidden type
/// must be the one the program holds (or none, before and after): other
/// fns' revealed returns and every reader of the opaque then stand, and
/// `f`'s revealed return is its old one (`old_ret`).
pub(crate) fn reveal_again(p: &mut Program, f: LocalDefId, old_ret: crate::ty::Ty) -> Result<(), &'static str> {
    let (record_reads, unwind) = (p.record_reads, p.unwind);
    (p.record_reads, p.unwind) = (true, false);
    let again = crate::check::opaque::hidden_again(p, f);
    (p.record_reads, p.unwind) = (record_reads, unwind);
    match again {
        crate::check::opaque::HiddenAgain::Stands => {}
        // The body has errors now: the request answers with them.
        crate::check::opaque::HiddenAgain::Errors => return Err("hidden diag"),
        crate::check::opaque::HiddenAgain::Moved => return Err("hidden type"),
    }
    if p.gx.opaque_ret_of.contains_key(&f) {
        let opaque = p.fns[f.0 as usize].ret;
        p.gx.opaque_ret_of.insert(f, opaque);
        p.fns[f.0 as usize].ret = old_ret;
    }
    Ok(())
}

/// A test hook (`LUST_SIGDELTA_SELFTEST=1`, or `v` to print counts,
/// timing, and the refusal census, also to the file `LUST_SIGDELTA_CENSUS`
/// names): after a clean collect, redoes the
/// signature of every plain or template free fn, inherent method, and
/// trait impl method the delta takes on the same Ast (`redo_sig`). The digest must stay the same, no diagnostic may
/// appear, and a plain fn's `impl Trait` return must reveal the same hidden
/// type. A failure appends one line to the file `LUST_SIGDELTA_LOG` names
/// (a daemon answers a panicked request again, so sweeps read the log),
/// then panics. Nested fns and lang methods are left out (a header delta
/// refuses them).
pub fn self_test_if_asked(p: &mut Program) {
    static ON: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    let Some(mode) = ON.get_or_init(|| std::env::var("LUST_SIGDELTA_SELFTEST").ok().filter(|v| v == "1" || v == "v")) else { return };
    let fail = |msg: String| -> ! {
        if let Ok(path) = std::env::var("LUST_SIGDELTA_LOG") {
            use std::io::Write as _;
            if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
                let _ = f.write_all(format!("{msg}\n").as_bytes());
            }
        }
        panic!("{msg}");
    };
    let before = digest(p);
    let mut redone = 0usize;
    let (mut total, mut worst) = (std::time::Duration::ZERO, std::time::Duration::ZERO);
    for i in 0..p.fns.len() {
        let f = LocalDefId(i as u32);
        let inherent = matches!(p.fns[i].loc, FnLoc::Impl(..)) && p.gx.inherent_self_pats.contains_key(&f);
        let rpit = p.gx.opaques.contains_key(&generics::opaque_def(p.def_id(f)));
        // A trait impl method the delta takes (`generics::delta_impl_trait`).
        let trait_impl = loc_is_trait_impl(p, p.fns[i].loc) && !rpit && generics::delta_impl_trait(p, f).is_some();
        let class = p.gx.fn_class[i];
        if !matches!(class, FnClass::Plain | FnClass::Template)
            || p.is_lang_method(f)
            || !(matches!(p.fns[i].loc, FnLoc::Item(_)) || inherent || trait_impl)
        {
            continue;
        }
        let old_ret = p.fns[i].ret;
        let mut errs = Vec::new();
        let t0 = std::time::Instant::now();
        // A template's hidden type comes from its template check, which
        // the unchanged body does not need again.
        let reveal = rpit && class == FnClass::Plain;
        let r = redo_sig(p, f, rpit, &mut errs).and_then(|()| if reveal { reveal_again(p, f, old_ret) } else { Ok(()) });
        let dt = t0.elapsed();
        (total, worst) = (total + dt, worst.max(dt));
        if r.is_err() || !errs.is_empty() {
            let name = p.display_name(p.fns[i].name);
            fail(format!("sigdelta selftest: fn {i} ({name}): {r:?} {:?}", errs.first().map(|d| &d.message)));
        }
        redone += 1;
    }
    let after = digest(p);
    let moved: Vec<&str> = before.iter().zip(&after).filter(|(a, b)| a != b).map(|(a, _)| a.0).collect();
    if !moved.is_empty() {
        fail(format!("sigdelta selftest: {redone} fns redone, digest fields moved: {moved:?}"));
    }
    if mode == "v" {
        let mean = total.as_secs_f64() * 1e3 / redone.max(1) as f64;
        eprintln!("sigdelta selftest: {redone} fns redone, digest stands; mean {mean:.3} ms, max {:.3} ms", worst.as_secs_f64() * 1e3);
        let census = format!("sigdelta census: {} fns {:?}", p.fns.len(), crate::driver::kept_delta::census(p));
        eprintln!("{census}");
        // A daemon's stderr is often not kept: `LUST_SIGDELTA_CENSUS`
        // names a file that gets the line too.
        if let Ok(path) = std::env::var("LUST_SIGDELTA_CENSUS") {
            use std::io::Write as _;
            if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
                let _ = writeln!(f, "{census}");
            }
        }
    }
}
