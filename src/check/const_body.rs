// Type and borrow checking of const and static initializers.
//
// The const evaluator (ty/consteval.rs) runs initializers on the AST, so no
// IR existed for them and borrowck never saw them: `const C: (S, S) = { let
// s = S { x: 1 }; (s, s) };` was accepted (rustc E0382). The parser makes
// each initializer a fn body too (`ast::ConstDef::init_fn`: no parameters,
// a block whose tail is the value). After collect, `check_all` gives every
// such body a transient fn entry that returns the item's type (under its
// impl's or trait's generics for an associated const), runs the body
// checker, lowering and borrowck on it, and removes the entries again, so
// nothing after collect (mono, the driver, codegen) sees them.
//
// Anonymous consts outside fn bodies (array lengths in types, const
// generic arguments and defaults, enum discriminants) are bodies too
// (`ast::AnonConst`): collect records the ones it meets in signatures
// with the type their position gives (`GenTables::anon_wants`), and each
// is checked here the same way, so a dead branch the scalar evaluator
// skips still gets type, mutability and borrow errors. Anonymous consts
// inside bodies are checked with their body (lower.rs `anon_consts`).
//
// Lowering knows these bodies by their location (`FnLoc::is_const_init`):
// the temporaries the value extends (`&Vec::new()`, `&S { .. }`) live in
// static storage, as rustc's do in a const initializer, so a borrow of one
// may be the item's value. The const-specific checks (no `&mut` or
// interior mutability in the final value, no destructor runs, const fn
// calls only) stay with the evaluator.

use super::collect::{FnInfo, FnLoc, ParentGen, Program, apply_stmt_overlay};
use super::generics::{self, ConstScalar, FnClass, FnScope, FnTemplate};
use crate::ast::{self, ItemKind};
use crate::def::{DefId, LocalDefId};
use crate::diag::{Diag, Span};
use crate::driver::graph::{ReadKey, ReadKeys};
use crate::ty::defs::{DefData, DefKind, ModuleId, SigData, Vis};
use crate::ty::{AdtId, GenericArg, Region, Ty, TyIntern, TyKind};

/// One initializer to check: where its body is, the written type, the
/// generics and scope it is checked under, and its item's span.
struct Site {
    loc: FnLoc,
    ty: SiteTy,
    parent: ParentGen,
    owner: Option<AdtId>,
    /// The trait of a trait default: the body may use `Self: Trait`.
    trait_def: Option<DefId>,
    /// The body items an anonymous const inside a body item may name.
    loc_sibs: Option<Vec<u32>>,
    span: Span,
}

/// The type an initializer body returns: its item's written type, or the
/// type of an anonymous const's position (None: the position gives none;
/// the scalar checks in collect type the value then).
enum SiteTy {
    Written(ast::TyId),
    Scalar(Option<ConstScalar>),
}

/// Type- and borrow-checks every const and static initializer of the
/// program (the module comment). Runs at the end of collect, when the
/// program has no errors yet; diagnostics go to `errs`.
pub fn check_all(p: &mut Program, errs: &mut Vec<Diag>) {
    p.const_body_reads.clear();
    check_sites(p, errs, &|_| true);
    p.const_sites_shape = Shape::of(&p.ast);
}

/// The AST counts that bound the initializer sites (`sites`): anonymous
/// consts, items, and body items. A kept program's AST with the counts of
/// the last walk over every site holds the same sites, except in the
/// signatures of edited headers (`check_dirty`).
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct Shape {
    anon_consts: usize,
    items: usize,
    stmt_items: usize,
}

impl Shape {
    fn of(ast: &ast::Ast) -> Shape {
        Shape { anon_consts: ast.anon_consts.len(), items: ast.items.len(), stmt_items: ast.stmt_items.len() }
    }
}

/// `check_all` for a kept program after a header or derive delta: only
/// the bodies whose stored reads moved check again, and the ones with no
/// stored reads (an anonymous const of an edited signature); all of them
/// when the program records no reads. `edited` are the fns whose headers
/// the delta redid.
///
/// Every site of a kept program checked clean and stored its reads (a
/// failed one sends the request to the full path), so a site with no
/// reads is new. With no dirty set, the walk over the sites is skipped
/// when none can be new: the AST counts equal the last walk's (`Shape`)
/// and no edited header's item has a signature anon const.
///
/// `moved` says which read keys the deltas can move (`kept_delta::Touched`,
/// `Program::derive_key_moves`). A program that holds its verified-at mark
/// (`Program::verified`: a compile tail kept it, and no request took it
/// since) compares only those keys and `Checked` reads (which never hold
/// by fingerprint): every stored set held against that program, since only
/// `check_all` and this fn write them. Any other program compares every
/// read. With `prove` (the item oracle) every keyed clean set also takes
/// the full compare; the return is the count it finds dirty.
pub fn check_dirty(
    p: &mut Program,
    errs: &mut Vec<Diag>,
    moved: &mut dyn FnMut(&Program, &ReadKey) -> bool,
    prove: bool,
    edited: &[LocalDefId],
) -> usize {
    if !p.record_reads {
        check_all(p, errs);
        return 0;
    }
    let t0 = std::time::Instant::now();
    let mut memo = crate::intern::FxMap::default();
    let reads = std::mem::take(&mut p.const_body_reads);
    let known: std::collections::HashSet<FnLoc> = reads.iter().map(|(l, _)| *l).collect();
    let mut unproven = 0;
    let dirty: Vec<bool> = if p.verified != 0 {
        let mut hit: crate::intern::FxMap<ReadKey, bool> = crate::intern::FxMap::default();
        let mut out = Vec::with_capacity(reads.len());
        for (_, r) in &reads {
            let mut d = false;
            for (k, stored) in r.iter(ReadKeys::none()) {
                let h = *hit.entry(*k).or_insert_with(|| matches!(k, ReadKey::Checked(_)) || moved(p, k));
                if h && *memo.entry(*k).or_insert_with(|| p.read_fingerprint(k)) != stored {
                    d = true;
                    break;
                }
            }
            if !d && prove && p.reads_dirty_memo(r, ReadKeys::none(), &mut memo) != 0 {
                unproven += 1;
            }
            out.push(d);
        }
        out
    } else {
        reads.iter().map(|(_, r)| p.reads_dirty_memo(r, ReadKeys::none(), &mut memo) != 0).collect()
    };
    super::derive_delta::log(&|| {
        let ms = t0.elapsed().as_secs_f64() * 1e3;
        let n = dirty.iter().filter(|&&d| d).count();
        format!("const bodies: {} sets, {n} dirty, {} fingerprints, compare {ms:.1} ms\n", reads.len(), memo.len())
    });
    let mut locs = std::collections::HashSet::new();
    for ((l, r), d) in reads.into_iter().zip(dirty) {
        if d {
            locs.insert(l);
        } else {
            p.const_body_reads.push((l, r));
        }
    }
    let edited_item = |f: &LocalDefId| match p.fns.get(f.0 as usize).map(|i| i.loc) {
        Some(FnLoc::Item(i) | FnLoc::Impl(i, _) | FnLoc::Trait(i, _)) => p.ast.items.get(i as usize),
        _ => None,
    };
    let none_new = locs.is_empty()
        && p.const_sites_shape == Shape::of(&p.ast)
        && edited.iter().all(|f| edited_item(f).is_some_and(|item| SigWalk::roots(&p.ast, &p.interner, item).is_empty()));
    if !none_new {
        check_sites(p, errs, &|l| locs.contains(&l) || !known.contains(&l));
        p.const_sites_shape = Shape::of(&p.ast);
    }
    super::derive_delta::log(&|| {
        let walk = if none_new { " (no site walk)" } else { "" };
        format!("const bodies: {} rechecked{walk}, all {:.1} ms\n", locs.len(), t0.elapsed().as_secs_f64() * 1e3)
    });
    unproven
}

/// Checks the initializer bodies `keep` selects and stores their reads.
fn check_sites(p: &mut Program, errs: &mut Vec<Diag>, keep: &dyn Fn(FnLoc) -> bool) {
    let sites = sites(p, keep);
    if sites.is_empty() {
        return;
    }
    let base = (p.fns.len(), p.fn_defs.len(), p.defs.len());
    let ids: Vec<LocalDefId> = sites.into_iter().filter_map(|s| install(p, s)).collect();
    let prog: &Program = p;
    let results = crate::pool::par_map(&ids, |&f| {
        // Every checker error counts: a value the evaluator takes but the
        // checker does not type is a false reject, never a dropped error.
        let (ck, mut e) = super::check_fn(prog, f);
        let reads = if e.is_empty() {
            // Lowering and borrowck read derive lists too (Copy operands).
            let ((mut reads, be), noted) = super::derive_delta::scoped(prog.record_reads, || {
                let body = crate::lower::lower(prog, f, ck);
                let be = crate::borrowck::borrowck(prog, &body);
                (body.reads, be)
            });
            super::derive_delta::record(prog, &mut reads, &noted);
            e.extend(be);
            reads
        } else {
            ck.reads
        };
        (prog.fns[f.0 as usize].loc, e, reads)
    });
    p.fns.truncate(base.0);
    p.fn_defs.truncate(base.1);
    p.defs.truncate(base.2);
    p.gx.fn_templates.truncate(base.0);
    p.gx.fn_scopes.truncate(base.0);
    p.gx.fn_class.truncate(base.0);
    for &f in &ids {
        p.fn_siblings.remove(&f);
        p.regions.fns.remove(&f);
    }
    for (loc, e, reads) in results {
        errs.extend(e);
        if p.record_reads {
            p.const_body_reads.push((loc, reads));
        }
    }
}

/// The module whose names an initializer body sees: its item's (the
/// resolver records it by item span), or for a const inside a fn body,
/// the innermost fn around it. None for any other fn.
pub fn module_of(p: &Program, f: LocalDefId) -> Option<ModuleId> {
    let info = p.fns.get(f.0 as usize)?;
    if !info.loc.is_const_init() {
        return None;
    }
    let tables = p.resolved.as_deref()?;
    let root = Some(crate::ty::defs::ROOT_MODULE);
    let span = match info.loc {
        FnLoc::ConstItem(i) => item_span(&p.ast.items[i as usize])?,
        FnLoc::ImplConst(i, k) => match &p.ast.items[i as usize].kind {
            ItemKind::Impl(imp) => imp.consts[k as usize].span,
            _ => return root,
        },
        FnLoc::TraitConst(i, k) => match &p.ast.items[i as usize].kind {
            ItemKind::Trait(t) => t.consts[k as usize].span,
            _ => return root,
        },
        FnLoc::NestedConst(i) => item_span(&p.ast.stmt_items[i as usize])?,
        FnLoc::AnonConst(i) => return p.ast.anon_consts[i as usize].module.or(root),
        _ => return None,
    };
    if let Some(&m) = tables.const_init_module.get(&span) {
        return Some(m);
    }
    // A const in a fn body: the module of the smallest fn whose
    // expressions hold it.
    let at = info.def(&p.ast).exprs.0;
    let mut best: Option<(u32, ModuleId)> = None;
    for (i, g) in p.fns.iter().enumerate().take(tables.fn_module.len()) {
        let (lo, hi) = g.def(&p.ast).exprs;
        if at >= lo && at < hi && best.is_none_or(|(b, _)| hi - lo < b) {
            let m = super::collect::def_module_of_fn(p, i).unwrap_or(tables.fn_module[i]);
            best = Some((hi - lo, m));
        }
    }
    best.map(|(_, m)| m).or(root)
}

/// The span of a const or static item as the resolver keys it.
fn item_span(item: &ast::Item) -> Option<Span> {
    match &item.kind {
        ItemKind::Const(c) => Some(c.span),
        ItemKind::Static(s) => Some(s.span),
        _ => None,
    }
}

/// The initializer bodies of the program that `keep` selects, outside
/// shipped std source. A `thread_local!` static's value is a path to its
/// init fn, which is checked as a fn already. Each site's scope is built
/// only when `keep` takes it: after a delta it takes a few of thousands.
fn sites(p: &Program, keep: &dyn Fn(FnLoc) -> bool) -> Vec<Site> {
    let ast = &*p.ast;
    // A value with closures has a hidden fn copy that checks as a fn
    // (`Program::is_value_init_fn`), named at the item's name span: its
    // item is no site, or each error would be reported twice.
    let copied: std::collections::HashSet<(crate::diag::FileId, u32)> = (0..p.fns.len() as u32)
        .map(LocalDefId)
        .filter(|&f| matches!(p.fns[f.0 as usize].loc, FnLoc::Item(_) | FnLoc::Nested(_)) && p.is_value_init_fn(f))
        .map(|f| {
            let s = p.fn_def(f).name_span;
            (s.file, s.lo)
        })
        .collect();
    let take = |loc: FnLoc, span: Span| p.shipped_crate_at(span).is_none() && !p.in_lang_methods(span) && keep(loc);
    let uncopied = |name_span: Span| !copied.contains(&(name_span.file, name_span.lo));
    let plain = |loc, ty, span| Site {
        loc,
        ty: SiteTy::Written(ty),
        parent: ParentGen::default(),
        owner: None,
        trait_def: None,
        loc_sibs: None,
        span,
    };
    let tls = |item: &ast::Item| super::tls::key_form(&item.attrs, &p.interner).is_some();
    let mut out = Vec::new();
    for (i, item) in ast.items.iter().enumerate() {
        let i = i as u32;
        match &item.kind {
            ItemKind::Const(c) if c.init_fn.is_some() && uncopied(c.name_span) && take(FnLoc::ConstItem(i), c.span) => {
                out.push(plain(FnLoc::ConstItem(i), c.ty, c.span))
            }
            ItemKind::Static(s) if s.init_fn.is_some() && !tls(item) && uncopied(s.name_span) && take(FnLoc::ConstItem(i), s.span) => {
                out.push(plain(FnLoc::ConstItem(i), s.ty, s.span))
            }
            ItemKind::Impl(imp) if !imp.consts.is_empty() => {
                let mut cs = imp
                    .consts
                    .iter()
                    .enumerate()
                    .filter(|(k, c)| c.init_fn.is_some() && take(FnLoc::ImplConst(i, *k as u32), c.span))
                    .peekable();
                if cs.peek().is_none() {
                    continue;
                }
                let Some(parent) = p.impl_parents.get(&i) else { continue };
                let owner = parent.scope.self_ty.and_then(|t| p.tys.local_adt(t));
                for (k, c) in cs {
                    let loc = FnLoc::ImplConst(i, k as u32);
                    out.push(Site {
                        loc,
                        ty: SiteTy::Written(c.ty),
                        parent: parent.clone(),
                        owner,
                        trait_def: None,
                        loc_sibs: None,
                        span: c.span,
                    });
                }
            }
            ItemKind::Trait(t) if t.consts.iter().any(|c| c.init_fn.is_some()) => {
                let mut cs = t
                    .consts
                    .iter()
                    .enumerate()
                    .filter(|(k, c)| c.init_fn.is_some() && take(FnLoc::TraitConst(i, *k as u32), c.span))
                    .peekable();
                if cs.peek().is_none() {
                    continue;
                }
                let Some(&td) = p.gx.trait_names.get(&t.name) else { continue };
                let (Some(rec), Some(scope)) = (p.gx.index.trait_record(td), p.gx.trait_scopes.get(&td)) else { continue };
                let parent = ParentGen { generics: rec.generics.clone(), scope: scope.clone(), impl_item: None };
                for (k, c) in cs {
                    let loc = FnLoc::TraitConst(i, k as u32);
                    out.push(Site {
                        loc,
                        ty: SiteTy::Written(c.ty),
                        parent: parent.clone(),
                        owner: None,
                        trait_def: Some(td),
                        loc_sibs: None,
                        span: c.span,
                    });
                }
            }
            _ => {}
        }
    }
    for (i, item) in ast.stmt_items.iter().enumerate() {
        let loc = FnLoc::NestedConst(i as u32);
        let mut site = match &item.kind {
            ItemKind::Const(c) if c.init_fn.is_some() && uncopied(c.name_span) && take(loc, c.span) => plain(loc, c.ty, c.span),
            ItemKind::Static(s) if s.init_fn.is_some() && !tls(item) && uncopied(s.name_span) && take(loc, s.span) => plain(loc, s.ty, s.span),
            _ => continue,
        };
        apply_stmt_overlay(p, &mut site.parent.scope, item.span);
        out.push(site);
    }
    anon_sites(p, &take, &mut out);
    out
}

/// The anonymous consts of item signatures (`SigWalk`) that `take`
/// selects, as sites with the scope of their item, added to `out`.
fn anon_sites(p: &Program, take: &dyn Fn(FnLoc, Span) -> bool, out: &mut Vec<Site>) {
    let ast = &*p.ast;
    if ast.anon_consts.is_empty() {
        return;
    }
    let wants = p.gx.anon_wants.lock().unwrap_or_else(|e| e.into_inner());
    // The taken roots of one item: (anon const, its type when known, span).
    let taken = |item: &ast::Item| -> Vec<(u32, Option<ConstScalar>, Span)> {
        SigWalk::roots(ast, &p.interner, item)
            .into_iter()
            .filter_map(|(e, want)| {
                let i = ast.anon_const(e)?;
                let span = ast.expr_span(e);
                take(FnLoc::AnonConst(i), span).then(|| (i, want.or_else(|| wants.get(&e.0).copied().flatten()), span))
            })
            .collect()
    };
    let mut push = |roots: Vec<(u32, Option<ConstScalar>, Span)>, parent: &ParentGen, sibs: Option<&Vec<u32>>| {
        for (i, want, span) in roots {
            out.push(Site {
                loc: FnLoc::AnonConst(i),
                ty: SiteTy::Scalar(want),
                parent: parent.clone(),
                owner: parent.scope.self_ty.and_then(|t| p.tys.local_adt(t)),
                trait_def: None,
                loc_sibs: sibs.cloned(),
                span,
            });
        }
    };
    for (k, item) in ast.items.iter().enumerate() {
        let roots = taken(item);
        if roots.is_empty() {
            continue;
        }
        let parent = match &item.kind {
            ItemKind::Impl(imp) if imp.generics.params.is_empty() => p.impl_parents.get(&(k as u32)).cloned().unwrap_or_default(),
            // A field's const in an Adt with no parameters may name `Self`.
            ItemKind::Struct(ast::StructDef { name, generics, .. }) | ItemKind::Enum(ast::EnumDef { name, generics, .. })
                if generics.params.is_empty() =>
            {
                match p.type_names.get(name) {
                    Some(&id) => ParentGen { scope: p.gx.adt_scopes[id.0 as usize].clone(), ..ParentGen::default() },
                    None => ParentGen::default(),
                }
            }
            _ => ParentGen::default(),
        };
        push(roots, &parent, None);
    }
    for (k, item) in ast.stmt_items.iter().enumerate() {
        let roots = taken(item);
        if roots.is_empty() {
            continue;
        }
        let mut parent = ParentGen::default();
        apply_stmt_overlay(p, &mut parent.scope, item.span);
        push(roots, &parent, p.scope_of_stmt.get(&(k as u32)));
    }
}

/// Walks one item's signature (generics, field, parameter and alias
/// types, impl and trait headers, discriminants) for the values of
/// anonymous consts with a body (`Ast::anon_consts`): an array length
/// is a `usize`, a discriminant its repr type, a const argument or
/// default unknown here. Bodies are not walked: their anonymous consts
/// are checked with them.
struct SigWalk<'a> {
    ast: &'a ast::Ast,
    /// Also the values with no entry (a type written in a body).
    all: bool,
    out: Vec<(ast::ExprId, Option<ConstScalar>)>,
}

/// The anonymous consts of a type written in a body (`let x: [u8; ..]`),
/// with the type each must have when known: the body checker types them
/// (`Ctx::type_anon_const`). A const argument takes the type its
/// parameter gave when the type resolved (`GenTables::anon_wants`).
pub(crate) fn written_anon_consts(p: &Program, t: ast::TyId) -> Vec<(ast::ExprId, Option<ConstScalar>)> {
    let mut w = SigWalk { ast: &p.ast, all: true, out: Vec::new() };
    w.ty(t);
    if w.out.iter().any(|(_, want)| want.is_none()) {
        let wants = p.gx.anon_wants.lock().unwrap_or_else(|e| e.into_inner());
        for (e, want) in &mut w.out {
            *want = want.or_else(|| crate::check::spec::anon_want(e.0, || wants.get(&e.0).copied().flatten()));
        }
    }
    w.out
}

impl SigWalk<'_> {
    fn roots(ast: &ast::Ast, interner: &crate::intern::Interner, item: &ast::Item) -> Vec<(ast::ExprId, Option<ConstScalar>)> {
        let mut w = SigWalk { ast, all: false, out: Vec::new() };
        w.item(interner, item);
        w.out
    }

    fn root(&mut self, e: ast::ExprId, want: Option<ConstScalar>) {
        if if self.all { !self.ast.is_plain_const(e) } else { self.ast.anon_const(e).is_some() } {
            self.out.push((e, want));
        }
    }

    fn item(&mut self, interner: &crate::intern::Interner, item: &ast::Item) {
        let fields = |w: &mut Self, vf: &ast::VariantFields| {
            if let ast::VariantFields::Tuple(fs) | ast::VariantFields::Struct(fs) = vf {
                fs.iter().for_each(|f| w.ty(f.ty));
            }
        };
        match &item.kind {
            ItemKind::Fn(d) => self.fn_sig(d),
            ItemKind::Struct(s) => {
                self.generics(&s.generics, &s.where_clause);
                fields(self, &s.fields);
            }
            ItemKind::Union(u) => {
                self.generics(&u.generics, &u.where_clause);
                u.fields.iter().for_each(|f| self.ty(f.ty));
            }
            ItemKind::Enum(e) => {
                self.generics(&e.generics, &e.where_clause);
                let repr = ConstScalar::Int(super::collect::disc_want_ty(interner, &item.attrs));
                for v in &e.variants {
                    fields(self, &v.fields);
                    if let Some(d) = v.discriminant {
                        self.root(d, Some(repr));
                    }
                }
            }
            ItemKind::Type(a) => {
                self.generics(&a.generics, &a.where_clause);
                self.ty(a.ty);
            }
            ItemKind::Const(c) => self.ty(c.ty),
            ItemKind::Static(s) => self.ty(s.ty),
            ItemKind::Impl(imp) => {
                self.generics(&imp.generics, &imp.where_clause);
                if let Some(tr) = &imp.trait_ref {
                    self.segs(&tr.path);
                }
                self.ty(imp.self_ty);
                imp.fns.iter().for_each(|f| self.fn_sig(f));
                imp.consts.iter().for_each(|c| self.ty(c.ty));
                for t in &imp.types {
                    self.generics(&t.generics, &t.where_clause);
                    self.bounds(&t.bounds);
                    t.default.into_iter().for_each(|d| self.ty(d));
                }
            }
            ItemKind::Trait(t) => {
                self.generics(&t.generics, &t.where_clause);
                self.bounds(&t.bounds);
                t.fns.iter().for_each(|f| self.fn_sig(f));
                t.consts.iter().for_each(|c| self.ty(c.ty));
                for a in &t.types {
                    self.generics(&a.generics, &a.where_clause);
                    self.bounds(&a.bounds);
                    a.default.into_iter().for_each(|d| self.ty(d));
                }
            }
            ItemKind::ExternBlock(b) => {
                for fi in &b.items {
                    match fi {
                        ast::ForeignItem::Fn(d) => self.fn_sig(d),
                        ast::ForeignItem::Static(s) => self.ty(s.ty),
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    fn fn_sig(&mut self, d: &ast::FnDef) {
        self.generics(&d.generics, &d.where_clause);
        if let Some(t) = d.self_param.as_ref().and_then(|s| s.ty) {
            self.ty(t);
        }
        d.params.iter().for_each(|p| self.ty(p.ty));
        d.ret.into_iter().for_each(|t| self.ty(t));
    }

    fn generics(&mut self, g: &ast::Generics, w: &ast::WhereClause) {
        for param in &g.params {
            match param {
                ast::GenericParam::Type { bounds, default, .. } => {
                    self.bounds(bounds);
                    default.into_iter().for_each(|&t| self.ty(t));
                }
                ast::GenericParam::Const { ty, default, .. } => {
                    self.ty(*ty);
                    default.into_iter().for_each(|&e| self.root(e, None));
                }
                ast::GenericParam::Lifetime { .. } => {}
            }
        }
        for pred in &w.preds {
            if let ast::WherePred::Type { ty, bounds, .. } = pred {
                self.ty(*ty);
                self.bounds(bounds);
            }
        }
    }

    fn bounds(&mut self, bounds: &[ast::TraitBound]) {
        for b in bounds {
            if let ast::TraitBound::Trait { trait_ref, .. } = b {
                self.segs(&trait_ref.path);
            }
        }
    }

    fn segs(&mut self, segs: &[ast::PathSeg]) {
        for s in segs {
            match &s.args {
                ast::GenericArgs::Angle(args) => {
                    for a in args {
                        match a {
                            ast::GenericArg::Type(t) => self.ty(*t),
                            ast::GenericArg::Const(e) => self.root(*e, None),
                            ast::GenericArg::Binding { kind, .. } => match kind {
                                ast::BindingKind::EqTy(t) => self.ty(*t),
                                ast::BindingKind::EqConst(e) => self.root(*e, None),
                                ast::BindingKind::Constraint(b) => self.bounds(b),
                            },
                            ast::GenericArg::Lifetime(_) => {}
                        }
                    }
                }
                ast::GenericArgs::Parenthesized { inputs, output } => {
                    inputs.iter().for_each(|&t| self.ty(t));
                    output.iter().for_each(|&t| self.ty(t));
                }
                ast::GenericArgs::None => {}
            }
        }
    }

    fn ty(&mut self, t: ast::TyId) {
        let ast = self.ast;
        match ast.ty(t) {
            ast::TyExpr::Path(segs) => self.segs(segs),
            ast::TyExpr::Ref { inner, .. } | ast::TyExpr::Slice(inner) | ast::TyExpr::Ptr { inner, .. } | ast::TyExpr::Paren(inner) => {
                self.ty(*inner)
            }
            ast::TyExpr::Tuple(ts) => ts.iter().for_each(|&t| self.ty(t)),
            ast::TyExpr::Array { inner, len } => {
                self.ty(*inner);
                self.root(*len, Some(ConstScalar::Int(crate::ty::IntTy::Usize)));
            }
            ast::TyExpr::FnPtr { inputs, ret, .. } => {
                inputs.iter().for_each(|p| self.ty(p.ty));
                ret.iter().for_each(|&t| self.ty(t));
            }
            ast::TyExpr::Dyn { bounds, .. } | ast::TyExpr::ImplTrait { bounds, .. } => self.bounds(bounds),
            ast::TyExpr::QPath { self_ty, trait_path, segs } => {
                self.ty(*self_ty);
                self.segs(trait_path);
                self.segs(segs);
            }
            ast::TyExpr::Unit | ast::TyExpr::Never | ast::TyExpr::Infer | ast::TyExpr::MacroCall(_) => {}
        }
    }
}

/// Adds the transient fn entry of one initializer body. None when its
/// written type does not resolve here (the evaluator reports that).
fn install(p: &mut Program, site: Site) -> Option<LocalDefId> {
    let Site { loc, ty, parent, owner, trait_def, loc_sibs, .. } = site;
    let scope = parent.scope;
    let ret = match ty {
        SiteTy::Written(ty) => {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            let t = generics::resolve_scoped(&p.ast, &p.interner, &p.known, &cx, &mut p.tys, ty, &scope).ok()?;
            generics::normalize_item_ty(p, t)
        }
        SiteTy::Scalar(Some(s)) => s.ty(),
        SiteTy::Scalar(None) => crate::ty::ERROR,
    };
    // Every region in a const's or static's type is `'static` (an impl
    // lifetime in an associated const's type is taken as `'static` too):
    // the region signature says so, the fn entry holds the erased type.
    let regioned = all_static(&mut p.tys, ret);
    let ret = crate::borrowck::erase(&mut p.tys, ret);
    let generics = parent.generics;
    let mut preds = generics.predicates.clone();
    if let Some(td) = trait_def {
        // A trait default's body may use the trait's own items on Self.
        let own: Vec<GenericArg> = generics
            .params
            .iter()
            .enumerate()
            .map(|(i, d)| match d.kind {
                crate::ty::ParamKind::Const(_) => GenericArg::Const(p.tys.intern_const(crate::ty::ConstKind::Param(i as u32))),
                crate::ty::ParamKind::Lifetime => GenericArg::Lifetime(crate::ty::Region::Erased),
                crate::ty::ParamKind::Type => GenericArg::Ty(p.tys.intern(TyKind::Param(crate::ty::ParamId(i as u32)))),
            })
            .collect();
        let args = p.tys.intern_args(&own);
        let tr = crate::ty::TraitRef { def: td, args, bindings: crate::ty::EMPTY_BINDINGS };
        preds.push(crate::ty::Predicate::Trait(crate::ty::Binder::plain(tr)));
    }
    let env = generics::body_env(&mut p.tys, &p.gx.index, &preds);
    let is_template = !generics.params.is_empty();
    let mut body_scope = scope;
    if !is_template {
        body_scope.type_params.clear();
        body_scope.const_params.clear();
    }
    let id = LocalDefId(p.fns.len() as u32);
    let def = DefId { krate: p.krate, hash: crate::def::item_hash(p.stable_crate, &["<const init>"], crate::def::DefKind::Fn, "", id.0) };
    let name = loc.def(&p.ast).name;
    let mut data = DefData::skeleton(DefKind::Fn, generics.parent, name, Vis::Priv, loc.def(&p.ast).name_span);
    data.generics = generics.clone();
    data.sig = SigData::Fn { params: Vec::new(), ret };
    p.defs.insert(def, data);
    p.fn_defs.push(def);
    p.fns.push(FnInfo { name, loc, owner, self_kind: None, params: Vec::new(), ret, ret_borrows_from: None, is_const: false });
    p.gx.fn_templates.push(is_template.then(|| FnTemplate { generics, env: env.clone() }));
    p.gx.fn_scopes.push(FnScope { env, scope: body_scope });
    p.gx.fn_class.push(if is_template { FnClass::Template } else { FnClass::Plain });
    let sig = crate::borrowck::RegionSig::const_value(regioned);
    p.regions.fns.insert(id, sig);
    // A const in a fn body names its block's items and the enclosing
    // blocks' items, as a nested fn does.
    let sibs = match loc {
        FnLoc::NestedConst(i) => p.scope_of_stmt.get(&i).cloned(),
        _ => loc_sibs,
    };
    if let Some(sibs) = sibs {
        p.fn_siblings.insert(id, sibs);
    }
    Some(id)
}

/// `t` with every region `'static`: references, dyn object lifetimes,
/// and lifetime args, through every type it contains.
pub(crate) fn all_static(tys: &mut impl TyIntern, t: Ty) -> Ty {
    let arg = |tys: &mut _, g: GenericArg| match g {
        GenericArg::Ty(e) => GenericArg::Ty(all_static(tys, e)),
        GenericArg::Lifetime(_) => GenericArg::Lifetime(Region::Static),
        g => g,
    };
    match tys.kind(t) {
        TyKind::Ref(_, m, inner) => {
            let i = all_static(tys, inner);
            tys.intern(TyKind::Ref(Region::Static, m, i))
        }
        TyKind::Dyn(b, _) => tys.intern(TyKind::Dyn(b, Region::Static)),
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = tys.tys_of(ts).to_vec().into_iter().map(|e| all_static(tys, e)).collect();
            let id = tys.intern_tys(&elems);
            tys.intern(TyKind::Tuple(id))
        }
        TyKind::Array(e, n) => {
            let e = all_static(tys, e);
            tys.intern(TyKind::Array(e, n))
        }
        TyKind::Slice(e) => {
            let e = all_static(tys, e);
            tys.intern(TyKind::Slice(e))
        }
        TyKind::Adt(d, a) => {
            let args: Vec<GenericArg> = tys.args(a).to_vec().into_iter().map(|g| arg(tys, g)).collect();
            tys.mk_adt(d, &args)
        }
        _ => t,
    }
}
