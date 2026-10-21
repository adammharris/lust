// Moves the spans a kept `Program` holds when the daemon's body patch
// edits the merged Ast under it (W-INCR3; driver/patch.rs moves the
// Ast's own spans). Collect copies spans out of the Ast into its tables
// (Adt, def, and generic parameter spans, impl and trait records, the
// blocks that hold items, and the wf and dyn sites it checks later);
// after an edit each one must name the same text as a fresh collect's.
//
// Completeness: `Program` and `GenTables` are destructured with no `..`,
// so a new field fails to compile here until it says whether it holds a
// span. The leaf types bound to `_` hold none (types, symbols, defs,
// ids, flags); nested types with spans go through their own walks.
use super::collect::Program;
use super::generics::GenTables;
use crate::diag::{FileId, Span};
use crate::ty::Generics;

/// Applies `f` to each span of a program: `f` maps an old span to its
/// place after the edit. Returns the number of spans visited.
pub fn shift_program(p: &mut Program, f: &mut dyn FnMut(Span) -> Span) -> usize {
    let mut n = 0usize;
    let mut sp = |s: &mut Span| {
        *s = f(*s);
        n += 1;
    };
    let Program {
        ast: _,
        interner: _,
        known: _,
        tys: _,
        defs,
        adts,
        fns: _,
        consts: _,
        const_names: _,
        const_defs: _,
        static_defs: _,
        assoc_const_names: _,
        impl_assoc_consts: _,
        trait_assoc_const_values: _,
        statics: _,
        static_names: _,
        body_items: _,
        body_type_items: _,
        item_blocks,
        body_consts: _,
        const_values: _,
        scope_of_stmt: _,
        fn_siblings: _,
        const_body_reads: _,
        const_sites_shape: _,
        type_names: _,
        drop_adts: _,
        aliases: _,
        fn_names: _,
        methods: _,
        main: _,
        krate: _,
        stable_crate: _,
        fn_defs: _,
        def_by_hash: _,
        std_fns: _,
        shipped_ranges,
        resolved: _,
        gx,
        record_reads: _,
        unwind: _,
        overflow_checks: _,
        debug_assertions: _,
        unwind_tables: _,
        regions: _,
        fp_memo: _,
        impl_parents,
        reuse_stamp: _,
        verified: _,
        outer_params: _,
        const_goals,
    } = p;
    const_goals.iter_mut().for_each(|(_, s)| sp(s));
    defs.for_each_span(&mut |s| sp(s));
    adts.iter_mut().for_each(|a| {
        sp(&mut a.span);
        a.variants.iter_mut().for_each(|v| v.fields.iter_mut().for_each(|f| sp(&mut f.span)));
    });
    item_blocks.iter_mut().for_each(|(s, _)| sp(s));
    // Shipped std source ranges are byte ranges of file 0.
    for (lo, hi, _) in shipped_ranges.iter_mut() {
        let mut s = Span::new(FileId(0), *lo, *hi);
        sp(&mut s);
        (*lo, *hi) = (s.lo, s.hi);
    }
    impl_parents.values_mut().for_each(|g| shift_generics(&mut g.generics, &mut sp));
    shift_gen_tables(gx, &mut sp);
    n
}

/// The spans of a parameter list (`ParamDef::span`).
pub fn shift_generics(g: &mut Generics, sp: &mut dyn FnMut(&mut Span)) {
    g.params.iter_mut().for_each(|p| sp(&mut p.span));
}

fn shift_gen_tables(gx: &mut GenTables, sp: &mut dyn FnMut(&mut Span)) {
    let GenTables {
        lang: _,
        index,
        trait_names: _,
        trait_scopes: _,
        trait_methods,
        lang_method_sigs: _,
        trait_assoc_defaults: _,
        trait_unsafe: _,
        trait_assoc_consts: _,
        wf_headers,
        adt_info: _,
        adt_lifetimes: _,
        generic_aliases: _,
        adt_generics,
        adt_envs: _,
        adt_scopes: _,
        adt_instance_of: _,
        fn_templates,
        fn_scopes: _,
        fn_class: _,
        instances: _,
        closures: _,
        closure_fns: _,
        template_closures: _,
        template_calls: _,
        instance_by_key: _,
        inherent_methods: _,
        inherent_tmpls: _,
        prim_inherent_methods: _,
        inherent_self_pats,
        inherent_impl_self,
        inherent_const_self,
        assoc_const_tmpls,
        traits_by_method: _,
        drop_methods: _,
        glue_methods: _,
        clone_from_methods: _,
        pcmp_methods: _,
        ref_default_methods: _,
        fmt_methods: _,
        deferred_debug_fields,
        hasher_methods: _,
        fmt_write_methods: _,
        build_hashers: _,
        written_hash: _,
        hash_impls: _,
        dyn_keys: _,
        generic_hash: _,
        borrow_impls: _,
        has_generics: _,
        user_generics: _,
        cow_fns: _,
        mono_counts: _,
        template_checks: _,
        trait_picks: _,
        trait_method_stubs: _,
        walk_instances: _,
        reuse: _,
        dyn_infos,
        vtables: _,
        vtable_by_key: _,
        dyn_inherent: _,
        dyn_impl_sites,
        static_dyn_impls: _,
        static_dyn_fns: _,
        eager_dyn_traits: _,
        mono_done: _,
        inst_order: _,
        template_rows: _,
        adt_created: _,
        turn_marks: _,
        derive_marks: _,
        written_projections: _,
        item_index: _,
        param_defaults: _,
        opaques: _,
        opaque_ret_of: _,
        opaque_hidden: _,
        iter_methods: _,
        anon_wants: _,
    } = gx;
    index.for_each_span(&mut |s| sp(s));
    trait_methods.values_mut().for_each(|t| shift_generics(&mut t.generics, sp));
    for (_, g, s) in wf_headers.iter_mut() {
        shift_generics(g, sp);
        sp(s);
    }
    adt_generics.iter_mut().for_each(|g| shift_generics(g, sp));
    fn_templates.iter_mut().flatten().for_each(|t| shift_generics(&mut t.generics, sp));
    inherent_self_pats.values_mut().for_each(|(_, g)| shift_generics(g, sp));
    inherent_impl_self.values_mut().for_each(|(_, g)| shift_generics(g, sp));
    for (_, g, s) in inherent_const_self.values_mut() {
        shift_generics(g, sp);
        sp(s);
    }
    assoc_const_tmpls.values_mut().for_each(|(_, g)| shift_generics(g, sp));
    deferred_debug_fields.iter_mut().for_each(|(_, s)| sp(s));
    for info in dyn_infos.values_mut() {
        if let Some((_, s)) = &mut info.violation {
            sp(s);
        }
    }
    dyn_impl_sites.iter_mut().for_each(|(_, s)| sp(s));
}
