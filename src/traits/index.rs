// The impl index (docs/ARCH.md section 2.3), the trait records the
// solver reads, and the coherence and orphan checks (section 2.6).
//
// One index is built per crate at collect. All trait selection and
// all trait method lookup read impls from here; nothing else walks
// impl items. An impl record stores its trait ref as a pattern over
// the impl's own generic parameters (`ParamId` indexes the impl's
// `Generics`), resolved in the global type store.
use crate::def::DefId;
use crate::diag::Span;
use crate::intern::{FxMap, Sym};
use crate::ty::*;

/// The index of one impl record in the `ImplIndex`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ImplId(pub u32);

/// The head of a Self type: the bucket key of section 2.3. `&T` and
/// `&mut T` are distinct heads, because an impl for one is not an
/// impl for the other. This is not `driver::graph::Head`, which
/// peels references for method candidate sets; selection records its
/// `ImplSet` reads under that head separately.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SelfHead {
    Adt(DefId),
    Ref,
    RefMut,
    RawPtr,
    Slice,
    Array,
    Tuple(u16),
    Str,
    FnPtr,
    /// The principal trait of a `dyn` type.
    Dyn(DefId),
    Int(IntTy),
    Float(FloatTy),
    Bool,
    Char,
    Never,
    Unit,
    /// A bare generic parameter, possibly under one wrapper. Only
    /// impl patterns head to `Param`; a checked Self type that is a
    /// bare parameter has no known head (`head_of` returns None).
    Param,
}

/// The wrapper a blanket impl's Self pattern puts around its bare
/// parameter, if any (section 2.6). `Smart` is one of the accepted
/// smart-pointer Adts (`Box`, `Rc`, `Arc`); collect rejects every
/// other shape around a bare parameter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlanketWrap {
    Bare,
    Ref,
    RefMut,
    Smart(DefId),
}

/// What generated an impl record that no source impl wrote.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Synthetic {
    /// A written `impl` item.
    None,
    /// A `#[derive]` expansion (section 2.2). The payload is the
    /// derive name (`Clone`, `Debug`, ...) and its derive bit
    /// (check/derive_delta.rs `bit`).
    Derive(Sym, u16),
    /// A lang-trait fact for a builtin type (for example the
    /// `IntoIterator` blanket, `From<T> for T`, slice `Index`).
    /// These records exist so selection and coherence see one impl
    /// set; the bodies stay in the builtin code paths until source
    /// std replaces them in wave A2.
    Lang,
}

/// One impl in the index.
#[derive(Clone, Debug)]
pub struct ImplRecord {
    /// The impl's own def. Synthetic impls (derives, lang facts)
    /// also carry a def, minted by collect, so reads and errors can
    /// name them.
    pub def: DefId,
    pub trait_def: DefId,
    /// The full trait ref pattern: Self pattern plus every input
    /// argument, over this impl's parameters (section 2.4).
    pub trait_ref: TraitRef,
    /// The impl's generic parameters, and its written predicates
    /// (the where clauses selection re-checks after a header match).
    pub generics: Generics,
    /// Associated type bindings, as patterns over the impl's
    /// parameters, with trait defaults already filled in by collect.
    pub assoc_tys: Vec<(DefId, Ty)>,
    /// Associated const bindings, as const values over the impl's
    /// parameters.
    pub assoc_consts: Vec<(DefId, ConstId)>,
    /// The defs of the impl's methods and associated fns, in
    /// written order.
    pub items: Vec<DefId>,
    pub synthetic: Synthetic,
    /// True when this impl is written (or generated) in the crate
    /// that owns the index. Coherence checks a pair only when at
    /// least one side is local, as rustc does per crate.
    pub local: bool,
    pub span: Span,
    /// The bucket head of the Self pattern.
    pub head: SelfHead,
    /// Set when the Self pattern is a bare parameter (optionally
    /// wrapped): the record also sits in the trait's blanket bucket.
    pub blanket: Option<BlanketWrap>,
}

impl ImplRecord {
    /// The Self type pattern of this impl.
    pub fn self_ty(&self, tys: &impl TyIntern) -> Ty {
        tys.args(self.trait_ref.args)[0].as_ty().expect("trait ref args start with the Self type")
    }
    /// The pattern bound to one associated type, if this impl binds it.
    pub fn assoc_ty(&self, assoc: DefId) -> Option<Ty> {
        self.assoc_tys.iter().find(|(d, _)| *d == assoc).map(|(_, t)| *t)
    }
}

/// One trait definition, as the solver needs it. The full record
/// (items, signatures) lives in `Defs`; this is the selection view.
#[derive(Clone, Debug)]
pub struct TraitRecord {
    pub def: DefId,
    pub name: Sym,
    /// Parameters with `Self` first (see `traits/mod.rs`), and the
    /// trait's own written predicates. The supertrait bounds are the
    /// trait predicates whose Self is this trait's `Self` parameter.
    pub generics: Generics,
    /// Associated items in written order: `(def, name, is_type)`.
    pub assoc_items: Vec<(DefId, Sym, bool)>,
    /// Methods and associated fns: `(def, name)` in written order.
    pub methods: Vec<(DefId, Sym)>,
    /// True when the trait is defined in the crate that owns the index.
    pub local: bool,
    pub span: Span,
}

impl TraitRecord {
    /// The def of one associated item by name, if the trait has it.
    pub fn assoc_by_name(&self, name: Sym) -> Option<DefId> {
        self.assoc_items.iter().find(|(_, n, _)| *n == name).map(|(d, _, _)| *d)
    }
    /// The def of one method or associated fn by name.
    pub fn method_by_name(&self, name: Sym) -> Option<DefId> {
        self.methods.iter().find(|(_, n)| *n == name).map(|(d, _)| *d)
    }
}

/// The head of a type whose outer form is fixed (section 2.4: a
/// "known head"). `resolve` follows inference links; a bare
/// unresolved inference variable or a bare generic parameter has no
/// known head and returns None. Callers that key impl patterns use
/// `pattern_head` instead.
pub fn head_of(tys: &impl TyIntern, t: Ty, resolve: &dyn Fn(Ty) -> Ty) -> Option<SelfHead> {
    match tys.kind(resolve(t)) {
        TyKind::Adt(d, _) => Some(SelfHead::Adt(d)),
        TyKind::Ref(_, Mut::Shared, _) => Some(SelfHead::Ref),
        TyKind::Ref(_, Mut::Mut, _) => Some(SelfHead::RefMut),
        TyKind::RawPtr(..) => Some(SelfHead::RawPtr),
        TyKind::Slice(_) => Some(SelfHead::Slice),
        TyKind::Array(..) => Some(SelfHead::Array),
        TyKind::Tuple(ts) => Some(SelfHead::Tuple(tys.tys_of(ts).len() as u16)),
        TyKind::Str => Some(SelfHead::Str),
        TyKind::FnPtr(_) | TyKind::FnDef(..) | TyKind::Closure(..) => Some(SelfHead::FnPtr),
        TyKind::Dyn(b, _) => tys.dyn_bounds(b).principal.map(|p| SelfHead::Dyn(p.value.def)),
        TyKind::Int(i) => Some(SelfHead::Int(i)),
        TyKind::Float(f) => Some(SelfHead::Float(f)),
        TyKind::Bool => Some(SelfHead::Bool),
        TyKind::Char => Some(SelfHead::Char),
        TyKind::Never => Some(SelfHead::Never),
        TyKind::Unit => Some(SelfHead::Unit),
        _ => None,
    }
}

/// The bucket head and blanket wrapper of an impl's Self pattern.
/// `smart` names the Adt defs accepted as bare-parameter wrappers
/// (`Box`, `Rc`, `Arc`). Returns None for a pattern shape the subset
/// does not index (a parameter under any other constructor, a
/// projection, an opaque): collect rejects those impls.
pub fn pattern_head(tys: &impl TyIntern, self_ty: Ty, smart: &[DefId]) -> Option<(SelfHead, Option<BlanketWrap>)> {
    match tys.kind(self_ty) {
        TyKind::Param(_) => Some((SelfHead::Param, Some(BlanketWrap::Bare))),
        TyKind::Ref(_, m, inner) => match tys.kind(inner) {
            TyKind::Param(_) => {
                let (h, w) = if m.is_mut() { (SelfHead::RefMut, BlanketWrap::RefMut) } else { (SelfHead::Ref, BlanketWrap::Ref) };
                Some((h, Some(w)))
            }
            _ => head_of(tys, self_ty, &|t| t).map(|h| (h, None)),
        },
        TyKind::Adt(d, a) if smart.contains(&d) => match tys.args(a).first().and_then(|g| g.as_ty()) {
            Some(inner) if matches!(tys.kind(inner), TyKind::Param(_)) => Some((SelfHead::Adt(d), Some(BlanketWrap::Smart(d)))),
            _ => Some((SelfHead::Adt(d), None)),
        },
        TyKind::Infer(_) | TyKind::Projection(..) | TyKind::Opaque(..) => None,
        _ => head_of(tys, self_ty, &|t| t).map(|h| (h, None)),
    }
}

/// True when a blanket wrapper can match a concrete Self type: a
/// bare-parameter blanket matches every Self, a `&T` blanket only a
/// shared reference, and a smart-pointer blanket only that Adt.
fn blanket_matches(tys: &impl TyIntern, wrap: BlanketWrap, self_ty: Ty, resolve: &dyn Fn(Ty) -> Ty) -> bool {
    match (wrap, tys.kind(resolve(self_ty))) {
        (BlanketWrap::Bare, _) => true,
        (BlanketWrap::Ref, TyKind::Ref(_, Mut::Shared, _)) => true,
        (BlanketWrap::RefMut, TyKind::Ref(_, Mut::Mut, _)) => true,
        (BlanketWrap::Smart(d), TyKind::Adt(e, _)) => d == e,
        _ => false,
    }
}

/// The per-crate impl index. Built once at collect, then read-only.
#[derive(Default)]
pub struct ImplIndex {
    impls: Vec<ImplRecord>,
    by_def: FxMap<DefId, ImplId>,
    /// `(trait, Self head)` to the impls in that bucket.
    buckets: FxMap<(DefId, SelfHead), Vec<ImplId>>,
    /// Trait to its blanket impls (bare parameter or wrapped parameter).
    blankets: FxMap<DefId, Vec<ImplId>>,
    /// Every impl of a trait, in insert order. Coherence walks this.
    by_trait: FxMap<DefId, Vec<ImplId>>,
    traits: FxMap<DefId, TraitRecord>,
    /// Associated item def to its trait def.
    assoc_trait: FxMap<DefId, DefId>,
    /// Traits answered by type structure, never by impl records
    /// (`Sized` and the auto traits, ARCH 2.7): an empty bucket says
    /// nothing about them.
    pub structural: Vec<DefId>,
    /// The derive-family lang traits (`Clone`, `PartialEq`, ...):
    /// core implements them for tuples, arrays, slices, references,
    /// and closures by structure, with no impl records for those.
    pub derive_family: Vec<DefId>,
    /// Traits that need `Self: Sized` in core (`Sized`, `Clone`,
    /// `Copy`, `Default`): provably false for `str`, `[T]`, and
    /// `dyn Trait`, so a blanket `impl<T: Clone> X for T` leaves the
    /// unsized heads to their own impls (W-STD-B: `[T]: ToOwned`).
    pub sized_only: Vec<DefId>,
    /// Std impls that coherence must see but selection must not
    /// (`impl<T: Hash> Hash for &T`, `impl<T> Drop for Box<T>`): lust
    /// has no bodies for them, so they stay out of every bucket. A
    /// user impl that overlaps one is a conflict with std (rustc E0119),
    /// and a where clause they can satisfy is no disproof. A negative
    /// impl (`!Clone for &mut T`, flagged) only conflicts.
    shadows: Vec<(ImplRecord, bool)>,
    /// The derived record of each (Adt template def, trait def), dead or
    /// alive (`set_dead`).
    derived: FxMap<(DefId, DefId), ImplId>,
    /// Records a derive delta took out (check/derive_delta.rs): they keep
    /// their ids and slots, but no bucket, trait list, def lookup, or
    /// `all_impls` walk sees them, as if collect had never made them.
    dead: Vec<bool>,
    /// The written impls of traits outside `ImplSet` reads (std and lang
    /// traits) by the Adt templates their trait refs name (Self pattern
    /// and trait arguments; `name_adts`), and each such impl's Adts, by
    /// impl id. A body records a `LangImpls` read of an Adt its types
    /// name, and of each Adt of such an impl that `get` hands out
    /// (driver/graph.rs `ReadKey::LangImpls`).
    by_adt: FxMap<DefId, Vec<ImplId>>,
    names: Vec<Vec<DefId>>,
}

impl ImplIndex {
    /// An empty index.
    pub fn new() -> ImplIndex {
        ImplIndex::default()
    }

    /// Visits every span the index holds: each impl and trait record's
    /// span and generic parameter spans (check/prog_shift.rs moves them).
    pub fn for_each_span(&mut self, f: &mut dyn FnMut(&mut Span)) {
        for r in self.impls.iter_mut().chain(self.shadows.iter_mut().map(|(r, _)| r)) {
            let ImplRecord {
                def: _,
                trait_def: _,
                trait_ref: _,
                generics,
                assoc_tys: _,
                assoc_consts: _,
                items: _,
                synthetic: _,
                local: _,
                span,
                head: _,
                blanket: _,
            } = r;
            f(span);
            generics.params.iter_mut().for_each(|p| f(&mut p.span));
        }
        for r in self.traits.values_mut() {
            let TraitRecord { def: _, name: _, generics, assoc_items: _, methods: _, local: _, span } = r;
            f(span);
            generics.params.iter_mut().for_each(|p| f(&mut p.span));
        }
    }

    /// Records one trait. Its associated items are indexed back to it.
    pub fn insert_trait(&mut self, rec: TraitRecord) {
        for (assoc, _, _) in &rec.assoc_items {
            self.assoc_trait.insert(*assoc, rec.def);
        }
        self.traits.insert(rec.def, rec);
    }

    /// The record of one trait, if indexed.
    pub fn trait_record(&self, def: DefId) -> Option<&TraitRecord> {
        self.traits.get(&def)
    }

    /// Every trait record, in no particular order.
    pub fn trait_records(&self) -> impl Iterator<Item = &TraitRecord> {
        self.traits.values()
    }

    /// The trait an associated item belongs to.
    pub fn trait_of_assoc(&self, assoc: DefId) -> Option<DefId> {
        self.assoc_trait.get(&assoc).copied()
    }

    /// The trait a method belongs to, by its def.
    pub fn trait_of_method(&self, method: DefId) -> Option<DefId> {
        self.traits.values().find(|r| r.methods.iter().any(|(d, _)| *d == method)).map(|r| r.def)
    }

    /// Makes room for `n` more impls, so a batch of inserts (the
    /// synthetic std impls, over a thousand) does not regrow the
    /// record list and the def map many times.
    pub fn reserve(&mut self, n: usize) {
        self.impls.reserve(n);
        self.by_def.reserve(n);
        self.by_trait.reserve(n / 8);
        self.buckets.reserve(n);
    }

    /// Records one impl and returns its id. The record's head and
    /// blanket fields decide its buckets; collect computes them with
    /// `pattern_head`.
    pub fn insert_impl(&mut self, rec: ImplRecord) -> ImplId {
        let id = ImplId(self.impls.len() as u32);
        self.by_def.insert(rec.def, id);
        self.buckets.entry((rec.trait_def, rec.head)).or_default().push(id);
        if rec.blanket.is_some() {
            self.blankets.entry(rec.trait_def).or_default().push(id);
        }
        self.by_trait.entry(rec.trait_def).or_default().push(id);
        if let (Synthetic::Derive(..), SelfHead::Adt(adt)) = (rec.synthetic, rec.head) {
            self.derived.insert((adt, rec.trait_def), id);
        }
        self.impls.push(rec);
        self.dead.push(false);
        id
    }

    /// Records that the written impl `id` of a trait outside `ImplSet`
    /// reads names the Adt templates `adts` in its trait ref (collect,
    /// right after `insert_impl`).
    pub fn name_adts(&mut self, id: ImplId, adts: &[DefId]) {
        let i = id.0 as usize;
        if self.names.len() <= i {
            self.names.resize_with(i + 1, Vec::new);
        }
        for &a in adts {
            let list = self.by_adt.entry(a).or_default();
            if !list.contains(&id) {
                list.push(id);
                self.names[i].push(a);
            }
        }
    }

    /// The live impls whose trait ref names the Adt template `adt`
    /// (`name_adts`), in insert order.
    pub fn impls_naming(&self, adt: DefId) -> impl Iterator<Item = ImplId> + '_ {
        self.by_adt.get(&adt).into_iter().flatten().copied().filter(|id| !self.dead[id.0 as usize])
    }

    /// The derived record of trait `trait_def` for the Adt template
    /// `adt`, alive or dead (None: collect never made one).
    pub fn derived_record(&self, adt: DefId, trait_def: DefId) -> Option<ImplId> {
        self.derived.get(&(adt, trait_def)).copied()
    }

    /// The number of impl records, dead ones included (ids run below it).
    pub fn record_count(&self) -> usize {
        self.impls.len()
    }

    /// True when a derive delta took the record out (`set_dead`).
    pub fn is_dead(&self, id: ImplId) -> bool {
        self.dead[id.0 as usize]
    }

    /// Takes a derived record out of every lookup, or puts it back in its
    /// old place (check/derive_delta.rs). Ids and insert order stand, so
    /// the live records keep the order a collect without the dead ones
    /// would give them. Only derived records (never blankets) toggle.
    pub fn set_dead(&mut self, id: ImplId, dead: bool) {
        let i = id.0 as usize;
        if self.dead[i] == dead {
            return;
        }
        self.dead[i] = dead;
        let (def, key) = (self.impls[i].def, (self.impls[i].trait_def, self.impls[i].head));
        debug_assert!(self.impls[i].blanket.is_none() && matches!(self.impls[i].synthetic, Synthetic::Derive(..)));
        let lists = [self.buckets.entry(key).or_default(), self.by_trait.entry(key.0).or_default()];
        for list in lists {
            match (list.binary_search(&id), dead) {
                (Ok(at), true) => {
                    list.remove(at);
                }
                (Err(at), false) => list.insert(at, id),
                _ => {}
            }
        }
        if dead {
            self.by_def.remove(&def);
        } else {
            self.by_def.insert(def, id);
        }
    }

    /// Records one coherence-only std impl (see `shadows`).
    pub fn insert_shadow(&mut self, rec: ImplRecord, negative: bool) {
        self.shadows.push((rec, negative));
    }

    /// One impl record by id. Handing out a derived record notes a read
    /// of its trait in its Adt's derive list (check/derive_delta.rs); a
    /// written impl of a std or lang trait notes a `LangImpls` read of
    /// each Adt it names (`name_adts`).
    pub fn get(&self, id: ImplId) -> &ImplRecord {
        let rec = &self.impls[id.0 as usize];
        if let (Synthetic::Derive(_, bit), SelfHead::Adt(def)) = (rec.synthetic, rec.head) {
            crate::check::derive_delta::note_def(def, bit);
        }
        if let Some(adts) = self.names.get(id.0 as usize) {
            crate::check::derive_delta::note_defs(adts, crate::check::derive_delta::bit::LANG);
        }
        crate::driver::read_cover::note(crate::driver::read_cover::Access::Impl(rec.def, rec.trait_def));
        rec
    }

    /// One impl record by id with no derive note: for a scan that only
    /// reads `head` and `synthetic` to skip records. A derived record it
    /// skips does not decide its answer, so its Adt's derive list is not
    /// a read (a toggle of it would check the body again for nothing).
    /// A record the scan goes on to use comes from `get`.
    pub fn peek(&self, id: ImplId) -> &ImplRecord {
        &self.impls[id.0 as usize]
    }

    /// One impl record by its def, with no note (see `peek`): for
    /// fingerprints, which a body records while its scope is open.
    pub fn peek_def(&self, def: DefId) -> Option<&ImplRecord> {
        self.by_def.get(&def).map(|&id| &self.impls[id.0 as usize])
    }

    /// One impl record by its def.
    pub fn by_def(&self, def: DefId) -> Option<(ImplId, &ImplRecord)> {
        self.by_def.get(&def).map(|&id| (id, self.get(id)))
    }

    /// Every impl record, in insert order.
    pub fn all_impls(&self) -> impl Iterator<Item = (ImplId, &ImplRecord)> {
        crate::driver::read_cover::note(crate::driver::read_cover::Access::AllImpls);
        self.impls.iter().enumerate().filter(|&(i, _)| !self.dead[i]).map(|(i, r)| (ImplId(i as u32), r))
    }

    /// Every impl of one trait, in insert order.
    pub fn impls_of_trait(&self, trait_def: DefId) -> &[ImplId] {
        crate::driver::read_cover::note(crate::driver::read_cover::Access::ImplsOf(trait_def));
        self.by_trait.get(&trait_def).map_or(&[], |v| v)
    }

    /// The impls in one bucket, for `ImplSet` reads and error lists.
    pub fn bucket(&self, trait_def: DefId, head: SelfHead) -> &[ImplId] {
        crate::driver::read_cover::note(crate::driver::read_cover::Access::ImplsOf(trait_def));
        self.buckets.get(&(trait_def, head)).map_or(&[], |v| v)
    }

    /// The header candidates for one trait and Self type (section 2.4
    /// step 2): the bucket for the Self head, plus the blanket impls
    /// whose wrapper shape matches. A record appears at most once.
    /// With no known head, only bare-parameter blankets can be probed
    /// (the probe itself can still bind the head). An integer or float
    /// literal variable probes the buckets of every integer or float
    /// type: it can only become one of those (rustc selects the one
    /// impl that matches, or defers until the literal fallback).
    pub fn candidates(&self, tys: &impl TyIntern, trait_def: DefId, self_ty: Ty, resolve: &dyn Fn(Ty) -> Ty) -> Vec<ImplId> {
        let mut out: Vec<ImplId> = Vec::new();
        if let Some(head) = head_of(tys, self_ty, resolve) {
            out.extend_from_slice(self.bucket(trait_def, head));
        }
        match tys.kind(resolve(self_ty)) {
            TyKind::Infer(v) if v.is_int() => {
                for i in IntTy::ALL {
                    out.extend_from_slice(self.bucket(trait_def, SelfHead::Int(i)));
                }
            }
            TyKind::Infer(v) if v.is_float() => {
                for f in [FloatTy::F32, FloatTy::F64] {
                    out.extend_from_slice(self.bucket(trait_def, SelfHead::Float(f)));
                }
            }
            _ => {}
        }
        if let Some(blankets) = self.blankets.get(&trait_def) {
            for &id in blankets {
                let rec = self.get(id);
                if let Some(wrap) = rec.blanket
                    && blanket_matches(tys, wrap, self_ty, resolve)
                    && !out.contains(&id)
                {
                    out.push(id);
                }
            }
        }
        out
    }

    /// The supertrait predicates of one trait ref, with the trait's
    /// parameters substituted by the ref's args (Self first). This is
    /// the provider `ty::elaborate` takes; the equalities of the
    /// ref's own bindings are elaboration's job, not this one's.
    pub fn supertraits_of(&self, tys: &mut impl TyIntern, tr: &TraitRef) -> Vec<Predicate> {
        let Some(rec) = self.traits.get(&tr.def) else { return Vec::new() };
        let args: Vec<GenericArg> = tys.args(tr.args).to_vec();
        let mut out = Vec::new();
        for pred in &rec.generics.predicates {
            out.push(subst_predicate(tys, *pred, &args));
        }
        out
    }
}

/// One predicate under substitution, binder kept. Shared with the
/// solver, which substitutes impl predicates after a selection.
pub fn subst_predicate(tys: &mut impl TyIntern, pred: Predicate, args: &[GenericArg]) -> Predicate {
    match pred {
        Predicate::Trait(b) => Predicate::Trait(Binder { count: b.count, value: subst_trait_ref_pub(tys, b.value, args) }),
        Predicate::AssocEq(b) => {
            let trait_args = subst_args_pub(tys, b.value.trait_args, args);
            let ty = subst(tys, b.value.ty, args);
            Predicate::AssocEq(Binder { count: b.count, value: AssocEqData { assoc: b.value.assoc, trait_args, ty } })
        }
        Predicate::TypeOutlives(t, r) => Predicate::TypeOutlives(subst(tys, t, args), r),
        other => other,
    }
}

/// A trait ref under substitution: args and bindings.
pub fn subst_trait_ref_pub(tys: &mut impl TyIntern, tr: TraitRef, args: &[GenericArg]) -> TraitRef {
    let a = subst_args_pub(tys, tr.args, args);
    let old: Vec<(DefId, GenericArg)> = tys.bindings(tr.bindings).to_vec();
    let new: Vec<(DefId, GenericArg)> = old
        .iter()
        .map(|&(d, g)| {
            (
                d,
                match g {
                    GenericArg::Ty(t) => GenericArg::Ty(subst(tys, t, args)),
                    other => other,
                },
            )
        })
        .collect();
    let bindings = tys.intern_bindings(&new);
    TraitRef { def: tr.def, args: a, bindings }
}

/// An argument list under substitution.
pub fn subst_args_pub(tys: &mut impl TyIntern, a: ArgsId, args: &[GenericArg]) -> ArgsId {
    let old: Vec<GenericArg> = tys.args(a).to_vec();
    let new: Vec<GenericArg> = old
        .iter()
        .map(|&g| match g {
            GenericArg::Ty(t) => GenericArg::Ty(subst(tys, t, args)),
            other => other,
        })
        .collect();
    tys.intern_args(&new)
}

// ---------- Pattern unification (coherence) ----------
//
// Coherence asks whether two impl headers can describe one trait
// ref. That is first-order unification over the two patterns, with
// each side's generic parameters as distinct variables: the right
// side is renamed by the left side's parameter count first, then a
// substitution map over `ParamId` carries the result. No inference
// variables take part, so this runs at collect over global types.

/// Renames every `Param(i)` in a value to `Param(offset + i)`, so two
/// patterns can share one variable space.
fn rename_ty(tys: &mut impl TyIntern, t: Ty, n_params: usize, offset: u32) -> Ty {
    if offset == 0 {
        return t;
    }
    let args: Vec<GenericArg> = (0..n_params)
        .map(|i| {
            let p = tys.intern(TyKind::Param(ParamId(offset + i as u32)));
            GenericArg::Ty(p)
        })
        .collect();
    subst(tys, t, &args)
}

fn rename_trait_ref(tys: &mut impl TyIntern, tr: TraitRef, n_params: usize, offset: u32) -> TraitRef {
    if offset == 0 {
        return tr;
    }
    let args: Vec<GenericArg> = (0..n_params)
        .map(|i| {
            let p = tys.intern(TyKind::Param(ParamId(offset + i as u32)));
            GenericArg::Ty(p)
        })
        .collect();
    subst_trait_ref_pub(tys, tr, &args)
}

/// Follows pattern-variable bindings for one type.
fn pat_resolve(tys: &impl TyIntern, map: &FxMap<ParamId, Ty>, mut t: Ty) -> Ty {
    while let TyKind::Param(p) = tys.kind(t) {
        match map.get(&p) {
            Some(&b) => t = b,
            None => return t,
        }
    }
    t
}

/// True if pattern variable `p` occurs in `t` under the bindings so far.
fn pat_occurs(tys: &impl TyIntern, map: &FxMap<ParamId, Ty>, p: ParamId, t: Ty) -> bool {
    let t = pat_resolve(tys, map, t);
    match tys.kind(t) {
        TyKind::Param(q) => q == p,
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => pat_occurs(tys, map, p, e),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => {
            tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| pat_occurs(tys, map, p, e)))
        }
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| pat_occurs(tys, map, p, e)),
        _ => false,
    }
}

/// Unifies two pattern types, extending the variable map. Lifetime
/// arguments always unify (regions do not split impls in this
/// subset); const arguments unify when equal or when either side is
/// a const parameter.
pub fn unify_patterns(tys: &impl TyIntern, map: &mut FxMap<ParamId, Ty>, a: Ty, b: Ty) -> bool {
    let (a, b) = (pat_resolve(tys, map, a), pat_resolve(tys, map, b));
    if a == b {
        return true;
    }
    match (tys.kind(a), tys.kind(b)) {
        (TyKind::Error, _) | (_, TyKind::Error) => true,
        (TyKind::Param(p), _) => {
            if pat_occurs(tys, map, p, b) {
                return false;
            }
            map.insert(p, b);
            true
        }
        (_, TyKind::Param(p)) => {
            if pat_occurs(tys, map, p, a) {
                return false;
            }
            map.insert(p, a);
            true
        }
        (TyKind::Ref(_, m, x), TyKind::Ref(_, n, y)) => m == n && unify_patterns(tys, map, x, y),
        (TyKind::RawPtr(m, x), TyKind::RawPtr(n, y)) => m == n && unify_patterns(tys, map, x, y),
        (TyKind::Slice(x), TyKind::Slice(y)) => unify_patterns(tys, map, x, y),
        (TyKind::Array(x, cx), TyKind::Array(y, cy)) => unify_patterns(tys, map, x, y) && unify_pattern_consts(tys, cx, cy),
        (TyKind::Tuple(x), TyKind::Tuple(y)) => {
            let (xs, ys) = (tys.tys_of(x).to_vec(), tys.tys_of(y).to_vec());
            xs.len() == ys.len() && xs.iter().zip(&ys).all(|(&u, &v)| unify_patterns(tys, map, u, v))
        }
        (TyKind::Adt(d, x), TyKind::Adt(e, y)) => d == e && unify_pattern_args(tys, map, x, y),
        (TyKind::FnDef(d, x), TyKind::FnDef(e, y)) => d == e && unify_pattern_args(tys, map, x, y),
        (TyKind::Projection(d, x), TyKind::Projection(e, y)) => d == e && unify_pattern_args(tys, map, x, y),
        (TyKind::Opaque(d, x), TyKind::Opaque(e, y)) => d == e && unify_pattern_args(tys, map, x, y),
        // The object lifetime bound is a region, and regions do not
        // split impls: `dyn T + 'static` and `dyn T + 'a` are one
        // type here (rustc E0119 for two impls of them).
        (TyKind::Dyn(x, _), TyKind::Dyn(y, _)) => unify_dyn_bounds(tys, map, x, y),
        (ka, kb) => ka == kb,
    }
}

/// Two dyn bound lists unify when the auto bits match and the
/// principals are the same trait ref up to pattern unification
/// (args and bindings; the Self slot is `DYN_SELF`, an error type,
/// which unifies with anything). The `supertraits` field is a
/// derived set, so the principal decides it.
fn unify_dyn_bounds(tys: &impl TyIntern, map: &mut FxMap<ParamId, Ty>, a: BoundsId, b: BoundsId) -> bool {
    let (a, b) = (tys.dyn_bounds(a), tys.dyn_bounds(b));
    if a.auto != b.auto {
        return false;
    }
    match (a.principal, b.principal) {
        (None, None) => true,
        (Some(x), Some(y)) => {
            let (x, y) = (x.value, y.value);
            if x.def != y.def || !unify_pattern_args(tys, map, x.args, y.args) {
                return false;
            }
            let yb: Vec<(DefId, GenericArg)> = tys.bindings(y.bindings).to_vec();
            tys.bindings(x.bindings).len() == yb.len()
                && tys.bindings(x.bindings).iter().all(|&(assoc, ga)| {
                    match (ga, yb.iter().find(|(d, _)| *d == assoc)) {
                        (GenericArg::Ty(u), Some(&(_, GenericArg::Ty(v)))) => unify_patterns(tys, map, u, v),
                        (GenericArg::Ty(_), _) => false,
                        _ => true,
                    }
                })
        }
        _ => false,
    }
}

fn unify_pattern_consts(tys: &impl TyIntern, a: ConstId, b: ConstId) -> bool {
    a == b || matches!(tys.const_kind(a), ConstKind::Param(_)) || matches!(tys.const_kind(b), ConstKind::Param(_))
}

fn unify_pattern_args(tys: &impl TyIntern, map: &mut FxMap<ParamId, Ty>, a: ArgsId, b: ArgsId) -> bool {
    let n = tys.args(a).len();
    if n != tys.args(b).len() {
        return false;
    }
    for i in 0..n {
        let ok = match (tys.args(a)[i], tys.args(b)[i]) {
            (GenericArg::Ty(x), GenericArg::Ty(y)) => unify_patterns(tys, map, x, y),
            (GenericArg::Const(x), GenericArg::Const(y)) => unify_pattern_consts(tys, x, y),
            (GenericArg::Lifetime(_), GenericArg::Lifetime(_)) => true,
            _ => false,
        };
        if !ok {
            return false;
        }
    }
    true
}

/// Applies a pattern substitution map to one type. Unmapped
/// parameters stay as written. Variable chains are followed first
/// (`pat_resolve`), then the walk is structural, so a binding like
/// `P0 = P1` cannot loop. `n_params` is kept for callers that track
/// their variable space size; the walk itself needs only the map.
pub fn apply_pattern_subst(tys: &mut impl TyIntern, map: &FxMap<ParamId, Ty>, t: Ty, _n_params: usize) -> Ty {
    let t = pat_resolve(tys, map, t);
    if map.is_empty() || !tys.flags(t).contains_param() {
        return t;
    }
    match tys.kind(t) {
        TyKind::Param(_) => t,
        TyKind::Ref(r, m, e) => {
            let e = apply_pattern_subst(tys, map, e, _n_params);
            tys.intern(TyKind::Ref(r, m, e))
        }
        TyKind::RawPtr(m, e) => {
            let e = apply_pattern_subst(tys, map, e, _n_params);
            tys.intern(TyKind::RawPtr(m, e))
        }
        TyKind::Slice(e) => {
            let e = apply_pattern_subst(tys, map, e, _n_params);
            tys.intern(TyKind::Slice(e))
        }
        TyKind::Array(e, n) => {
            let e = apply_pattern_subst(tys, map, e, _n_params);
            tys.intern(TyKind::Array(e, n))
        }
        TyKind::Tuple(ts) => {
            let old: Vec<Ty> = tys.tys_of(ts).to_vec();
            let new: Vec<Ty> = old.iter().map(|&e| apply_pattern_subst(tys, map, e, _n_params)).collect();
            let ts = tys.intern_tys(&new);
            tys.intern(TyKind::Tuple(ts))
        }
        TyKind::Adt(d, a) => {
            let a = apply_pattern_args(tys, map, a, _n_params);
            tys.intern(TyKind::Adt(d, a))
        }
        TyKind::FnDef(d, a) => {
            let a = apply_pattern_args(tys, map, a, _n_params);
            tys.intern(TyKind::FnDef(d, a))
        }
        TyKind::Closure(d, a) => {
            let a = apply_pattern_args(tys, map, a, _n_params);
            tys.intern(TyKind::Closure(d, a))
        }
        TyKind::Opaque(d, a) => {
            let a = apply_pattern_args(tys, map, a, _n_params);
            tys.intern(TyKind::Opaque(d, a))
        }
        TyKind::Projection(d, a) => {
            let a = apply_pattern_args(tys, map, a, _n_params);
            tys.intern(TyKind::Projection(d, a))
        }
        _ => t,
    }
}

/// One argument list under a pattern substitution map.
fn apply_pattern_args(tys: &mut impl TyIntern, map: &FxMap<ParamId, Ty>, a: ArgsId, n_params: usize) -> ArgsId {
    let old: Vec<GenericArg> = tys.args(a).to_vec();
    let new: Vec<GenericArg> = old
        .iter()
        .map(|&g| match g {
            GenericArg::Ty(e) => GenericArg::Ty(apply_pattern_subst(tys, map, e, n_params)),
            other => other,
        })
        .collect();
    tys.intern_args(&new)
}

/// Applies a pattern substitution map to one trait ref.
fn apply_pattern_subst_ref(tys: &mut impl TyIntern, map: &FxMap<ParamId, Ty>, tr: TraitRef, n_params: usize) -> TraitRef {
    if map.is_empty() {
        return tr;
    }
    let args = apply_pattern_args(tys, map, tr.args, n_params);
    let old: Vec<(DefId, GenericArg)> = tys.bindings(tr.bindings).to_vec();
    let new: Vec<(DefId, GenericArg)> = old
        .iter()
        .map(|&(d, g)| {
            (
                d,
                match g {
                    GenericArg::Ty(e) => GenericArg::Ty(apply_pattern_subst(tys, map, e, n_params)),
                    other => other,
                },
            )
        })
        .collect();
    let bindings = tys.intern_bindings(&new);
    TraitRef { def: tr.def, args, bindings }
}

// ---------- Coherence and the orphan rule (section 2.6) ----------

/// Strips fundamental wrappers (`&`, `&mut`, raw pointers, and the
/// `fundamental` Adts such as `Box` and `Pin`) from a Self type,
/// (`fundamental` lists rustc's `#[fundamental]` items: Adts, and for
/// coherence also the `Fn` traits),
/// following pattern bindings. Returns the base type.
fn strip_fundamental(tys: &impl TyIntern, map: &FxMap<ParamId, Ty>, mut t: Ty, fundamental: &[DefId]) -> Ty {
    loop {
        t = pat_resolve(tys, map, t);
        t = match tys.kind(t) {
            TyKind::Ref(_, _, inner) | TyKind::RawPtr(_, inner) => inner,
            TyKind::Adt(d, a) if fundamental.contains(&d) => match tys.args(a).iter().find_map(|g| g.as_ty()) {
                Some(inner) => inner,
                None => return t,
            },
            _ => return t,
        };
    }
}

impl ImplIndex {
    /// True when no impl in the index can match this trait ref
    /// pattern: every candidate header either fails to unify with
    /// it or has a where clause that cannot hold under that
    /// unification (one level per `depth`, as the selection-side
    /// provably-false check recurses: `Box<My>: Clone` dies through
    /// core's `impl<T: Clone> Clone for Box<T>` when `My: Clone`
    /// cannot hold). Pattern variables in `tr` are the caller's
    /// merged variable space; each candidate's own parameters are
    /// renamed above it.
    #[allow(clippy::too_many_arguments)]
    fn no_impl_can_match(
        &self,
        tys: &mut impl TyIntern,
        tr: TraitRef,
        vars_in_use: u32,
        depth: u32,
        fundamental: &[DefId],
        by_construction: &[DefId],
        is_local: &dyn Fn(DefId) -> bool,
    ) -> bool {
        // The builtin object impl has no impl record: `dyn T`
        // implements `T` and every supertrait of `T` by
        // construction, so such a clause can hold.
        if self.dyn_object_impl_holds(tys, tr) {
            return false;
        }
        let shadows = self.shadows.iter().filter(|(r, neg)| !neg && r.trait_def == tr.def).map(|(r, _)| r);
        for rec in self.impls_of_trait(tr.def).iter().map(|&id| self.get(id)).chain(shadows) {
            let rec = rec.clone();
            let n = rec.generics.params.len();
            let cand = rename_trait_ref(tys, rec.trait_ref, n, vars_in_use);
            let mut map: FxMap<ParamId, Ty> = FxMap::default();
            if !unify_pattern_args(tys, &mut map, cand.args, tr.args) {
                continue;
            }
            // An associated type binding of the clause must agree with
            // the impl's (`&Local: Deref<Target = i32>` is dead through
            // core's `impl Deref for &T` with `Target = T`).
            let bindings: Vec<(DefId, GenericArg)> = tys.bindings(tr.bindings).to_vec();
            let binding_clash = bindings.into_iter().any(|(assoc, ga)| match (ga, rec.assoc_ty(assoc)) {
                (GenericArg::Ty(want), Some(have)) => {
                    let have = rename_ty(tys, have, n, vars_in_use);
                    !unify_patterns(tys, &mut map, want, have)
                }
                _ => false,
            });
            if binding_clash {
                continue;
            }
            // A matching header is live unless one of its clauses
            // cannot hold; past the depth cap it counts as live.
            let dead = depth < 4
                && trait_clauses_of(tys, &rec, vars_in_use).into_iter().any(|clause| {
                    self.clause_cannot_hold_at(tys, &map, clause, vars_in_use as usize + n, depth + 1, fundamental, by_construction, is_local)
                });
            if !dead {
                return false;
            }
        }
        true
    }

    /// True when the goal holds by the builtin object impl: its
    /// Self type is a dyn type whose principal trait (or a
    /// supertrait of it, transitively) is the goal trait, with
    /// arguments that unify as patterns. The principal's Self
    /// slot is `DYN_SELF`, which unifies with anything.
    pub(crate) fn dyn_object_impl_holds(&self, tys: &mut impl TyIntern, tr: TraitRef) -> bool {
        let Some(self_ty) = tys.args(tr.args).first().and_then(|g| g.as_ty()) else { return false };
        let TyKind::Dyn(b, _) = tys.kind(self_ty) else { return false };
        let Some(principal) = tys.dyn_bounds(b).principal.map(|p| p.value) else { return false };
        let mut work: Vec<TraitRef> = vec![principal];
        let mut seen: Vec<TraitRef> = Vec::new();
        while let Some(cand) = work.pop() {
            if seen.contains(&cand) {
                continue;
            }
            seen.push(cand);
            if cand.def == tr.def {
                let mut map: FxMap<ParamId, Ty> = FxMap::default();
                if unify_pattern_args(tys, &mut map, cand.args, tr.args) {
                    return true;
                }
            }
            for pred in self.supertraits_of(tys, &cand) {
                // Only predicates on the principal's own Self are
                // supertraits; bounds on its other params are not.
                if let Predicate::Trait(s) = pred
                    && tys.args(s.value.args).first().and_then(|g| g.as_ty()).is_some_and(|t| t == DYN_SELF || t == self_ty)
                {
                    work.push(s.value);
                }
            }
        }
        false
    }

    /// The orphan-based impossibility test of section 2.6 for one
    /// where clause, after the two impl headers have been unified
    /// into `map`. The clause cannot hold only when it is a trait
    /// predicate with a local side and no impl in the index
    /// matches it, so the orphan rule also bars every downstream
    /// crate from adding one. The local side is rustc's orphan
    /// test over the whole trait ref: the trait is local, or a
    /// local type occurs in the Self type or one of the trait's
    /// input types before any uncovered type parameter. Traits
    /// that hold by construction (`Sized`, the auto traits) are
    /// never disproved: they have no impl records to match, but a
    /// `S: Sized` clause on a local struct is true, not impossible.
    fn clause_cannot_hold(
        &self,
        tys: &mut impl TyIntern,
        map: &FxMap<ParamId, Ty>,
        clause: TraitRef,
        n_vars: usize,
        fundamental: &[DefId],
        by_construction: &[DefId],
        is_local: &dyn Fn(DefId) -> bool,
    ) -> bool {
        self.clause_cannot_hold_at(tys, map, clause, n_vars, 0, fundamental, by_construction, is_local)
    }

    /// `clause_cannot_hold` at one recursion depth (see
    /// `no_impl_can_match`).
    #[allow(clippy::too_many_arguments)]
    fn clause_cannot_hold_at(
        &self,
        tys: &mut impl TyIntern,
        map: &FxMap<ParamId, Ty>,
        clause: TraitRef,
        n_vars: usize,
        depth: u32,
        fundamental: &[DefId],
        by_construction: &[DefId],
        is_local: &dyn Fn(DefId) -> bool,
    ) -> bool {
        let clause = apply_pattern_subst_ref(tys, map, clause, n_vars);
        let self_ty = tys.args(clause.args)[0].as_ty().unwrap_or(ERROR);
        // `Sized` (and the traits that need it, `Clone` and kin) never
        // holds for an unsized type: the implicit `T: Sized` of `impl<T>
        // Tr for T` keeps it off `str`, `[u8]`, and `dyn Fn()`.
        if self.sized_only.contains(&clause.def) && matches!(tys.kind(self_ty), TyKind::Str | TyKind::Slice(_) | TyKind::Dyn(..)) {
            return true;
        }
        if by_construction.contains(&clause.def) {
            return false;
        }
        let empty: FxMap<ParamId, Ty> = FxMap::default();
        let base = strip_fundamental(tys, &empty, self_ty, fundamental);
        // A bare parameter Self can gain any impl downstream. An
        // empty bucket proves nothing for it.
        if matches!(tys.kind(base), TyKind::Param(_) | TyKind::Infer(_) | TyKind::Error) {
            return false;
        }
        // A fundamental trait (`Fn`, `FnMut`, `FnOnce`) is knowable like
        // a local one: no upstream release adds an impl of it. Its fn
        // item, fn pointer, and closure impls are structural (no
        // records), so those Self types and opaque ones can hold.
        // rustc's `trait_ref_is_knowable`: a downstream crate may
        // implement the clause when any of its types is an uncovered
        // variable (`Local: PartialEq<?B>` for a downstream `B`).
        if tys.args(clause.args).iter().any(|g| g.as_ty().is_some_and(|t| has_uncovered_param(tys, t, fundamental))) {
            return false;
        }
        let fundamental_trait = fundamental.contains(&clause.def);
        if fundamental_trait
            && matches!(tys.kind(base), TyKind::FnPtr(_) | TyKind::FnDef(..) | TyKind::Closure(..) | TyKind::Opaque(..) | TyKind::Projection(..))
        {
            return false;
        }
        let local_side = is_local(clause.def) || fundamental_trait || ref_has_local_side(tys, clause.args, fundamental, is_local);
        local_side && self.no_impl_can_match(tys, clause, n_vars as u32, depth, fundamental, by_construction, is_local)
    }

    /// Every overlapping pair of impls (section 2.6), as impl ids in
    /// index order. A pair is checked only when at least one impl is
    /// local to this crate. Two headers overlap when their full
    /// trait refs unify (Self, every input, and bindings) and no
    /// where clause of either is disprovable by the orphan test.
    /// The caller reports each pair as an overlapping-impls error at the later impl.
    /// Only pairs with a side `only` takes are tested (a derive delta's scope).
    pub fn coherence_overlaps(
        &self,
        tys: &mut impl TyIntern,
        fundamental: &[DefId],
        by_construction: &[DefId],
        is_local: &dyn Fn(DefId) -> bool,
        only: &dyn Fn(ImplId) -> bool,
    ) -> Vec<(ImplId, ImplId)> {
        // Pair generation by Self head, not all pairs per trait:
        // two non-blanket impls whose Self heads differ cannot unify
        // their Self patterns (see `unify_patterns`: the outer
        // constructor must agree), so only same-bucket pairs and
        // pairs that involve a blanket impl can overlap. A blanket
        // impl pairs against every impl of its trait. Without this,
        // one derived impl per Adt makes coherence quadratic in the
        // Adt count of the crate (thousands of Clone/Debug records).
        // A pair with no local side is never checked, so it is never
        // made (the std lang facts fill buckets of a dozen impls each).
        let mut pairs: Vec<(ImplId, ImplId)> = Vec::new();
        let local = |id: ImplId| self.get(id).local;
        for ids in self.buckets.values() {
            for (i, &a) in ids.iter().enumerate() {
                for &b in &ids[i + 1..] {
                    if local(a) || local(b) {
                        pairs.push(if a.0 < b.0 { (a, b) } else { (b, a) });
                    }
                }
            }
        }
        for (trait_def, blanket_ids) in &self.blankets {
            let Some(ids) = self.by_trait.get(trait_def) else { continue };
            for &b in blanket_ids {
                for &o in ids {
                    if o != b && (local(b) || local(o)) {
                        pairs.push(if b.0 < o.0 { (b, o) } else { (o, b) });
                    }
                }
            }
        }
        pairs.sort_by_key(|(a, b)| (a.0, b.0));
        pairs.dedup();
        let mut out = Vec::new();
        for (a, b) in pairs {
            let (ra, rb) = (self.get(a), self.get(b));
            if !only(a) && !only(b) {
                continue;
            }
            if self.pair_overlaps(tys, ra, rb, fundamental, by_construction, is_local) {
                out.push((a, b));
            }
        }
        out
    }

    /// The local impls that overlap a coherence-only std impl (see
    /// `shadows`), each once, in index order. Only impls `only` takes
    /// are tested (a derive delta's scope; collect takes all).
    pub fn shadow_overlaps(
        &self,
        tys: &mut impl TyIntern,
        fundamental: &[DefId],
        by_construction: &[DefId],
        is_local: &dyn Fn(DefId) -> bool,
        user_impl: &dyn Fn(ImplId) -> bool,
        only: &dyn Fn(ImplId) -> bool,
    ) -> Vec<ImplId> {
        let mut out = Vec::new();
        for (id, rec) in self.all_impls() {
            if !user_impl(id) || !only(id) {
                continue;
            }
            if self.shadows.iter().any(|(s, _)| s.trait_def == rec.trait_def && self.pair_overlaps(tys, s, rec, fundamental, by_construction, is_local)) {
                out.push(id);
            }
        }
        out
    }

    /// The overlap test for one pair of impls of one trait.
    fn pair_overlaps(
        &self,
        tys: &mut impl TyIntern,
        ra: &ImplRecord,
        rb: &ImplRecord,
        fundamental: &[DefId],
        by_construction: &[DefId],
        is_local: &dyn Fn(DefId) -> bool,
    ) -> bool {
        let na = ra.generics.params.len();
        let nb = rb.generics.params.len();
        let tr_b = rename_trait_ref(tys, rb.trait_ref, nb, na as u32);
        let mut map: FxMap<ParamId, Ty> = FxMap::default();
        if !unify_pattern_args(tys, &mut map, ra.trait_ref.args, tr_b.args) {
            return false;
        }
        // Bindings take part: `Out = u8` against `Out = u16` do not
        // overlap. A binding written on one side only is no bar.
        let bindings_b: Vec<(DefId, GenericArg)> = tys.bindings(tr_b.bindings).to_vec();
        for &(assoc, ga) in tys.bindings(ra.trait_ref.bindings) {
            if let (GenericArg::Ty(x), Some(&(_, GenericArg::Ty(y)))) = (ga, bindings_b.iter().find(|(d, _)| *d == assoc))
                && !unify_patterns(tys, &mut map, x, y)
            {
                return false;
            }
        }
        // One disprovable trait clause on either side ends the pair.
        let mut all: Vec<TraitRef> = trait_clauses_of(tys, ra, 0);
        all.extend(trait_clauses_of(tys, rb, na as u32));
        for clause in all {
            if self.clause_cannot_hold(tys, &map, clause, na + nb, fundamental, by_construction, is_local) {
                return false;
            }
        }
        true
    }

    /// The overlap test for one pair of inherent methods with the
    /// same name (rustc E0592): their impl Self patterns, over
    /// their impl generics, unify, and no where clause of either
    /// is disprovable by the orphan test. `pat_a` and `pat_b` are
    /// written over `gen_a` and `gen_b` parameters.
    pub fn inherent_pair_overlaps(
        &self,
        tys: &mut impl TyIntern,
        pat_a: Ty,
        gen_a: &Generics,
        pat_b: Ty,
        gen_b: &Generics,
        fundamental: &[DefId],
        by_construction: &[DefId],
        is_local: &dyn Fn(DefId) -> bool,
    ) -> bool {
        let na = gen_a.params.len();
        let nb = gen_b.params.len();
        let pat_b = rename_ty(tys, pat_b, nb, na as u32);
        let mut map: FxMap<ParamId, Ty> = FxMap::default();
        if !unify_patterns(tys, &mut map, pat_a, pat_b) {
            return false;
        }
        let mut all = trait_clauses_of_generics(tys, gen_a, 0);
        all.extend(trait_clauses_of_generics(tys, gen_b, na as u32));
        for clause in all {
            if self.clause_cannot_hold(tys, &map, clause, na + nb, fundamental, by_construction, is_local) {
                return false;
            }
        }
        true
    }

    /// The orphan rule for one impl (section 2.3), in rustc's
    /// form: the trait must be local, or one of the trait ref's
    /// types (the Self type first, then the trait's input types,
    /// in order) must be local, with no uncovered type parameter
    /// in any type before the first local one. A type here is
    /// local only when its outer form, after the fundamental
    /// wrappers (`&`, `&mut`, raw pointers, and fundamental Adts)
    /// are stripped, is a local Adt: `Option<MyType>` and
    /// `(MyType, MyType)` do not count, `&MyType` does. A
    /// parameter is uncovered when it is not nested under a
    /// fundamental wrapper. The caller reports a failure at the
    /// impl's span.
    pub fn orphan_ok(&self, tys: &impl TyIntern, rec: &ImplRecord, fundamental: &[DefId], is_local: &dyn Fn(DefId) -> bool) -> bool {
        is_local(rec.trait_def) || ref_has_local_side(tys, rec.trait_ref.args, fundamental, is_local)
    }
}

/// The type-list half of the orphan rule over one trait ref's
/// types (Self first, then the inputs), in RFC 2451's form: true
/// when a type in the list is local and no uncovered type parameter
/// occurs in any type before it. A type is local when it is a local
/// Adt or `dyn LocalTrait`, or a fundamental wrapper (`&`, `&mut`,
/// and fundamental Adts such as `Box` and `Pin`, never raw pointers)
/// of one. Used by the orphan rule itself and by the coherence
/// disproof, which needs the same test on a clause.
fn ref_has_local_side(tys: &impl TyIntern, args: ArgsId, fundamental: &[DefId], is_local: &dyn Fn(DefId) -> bool) -> bool {
    let mut seen_uncovered = false;
    for g in tys.args(args) {
        let Some(t) = g.as_ty() else { continue };
        if is_local_ty(tys, t, fundamental, is_local) {
            return !seen_uncovered;
        }
        if has_uncovered_param(tys, t, fundamental) {
            seen_uncovered = true;
        }
    }
    false
}

/// True when `t` is local for the orphan rule (see `ref_has_local_side`).
fn is_local_ty(tys: &impl TyIntern, t: Ty, fundamental: &[DefId], is_local: &dyn Fn(DefId) -> bool) -> bool {
    match tys.kind(t) {
        TyKind::Ref(_, _, e) => is_local_ty(tys, e, fundamental, is_local),
        TyKind::Adt(d, a) if fundamental.contains(&d) => {
            tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| is_local_ty(tys, e, fundamental, is_local)))
        }
        TyKind::Adt(d, _) => is_local(d),
        // `dyn LocalTrait` is local, as in rustc.
        TyKind::Dyn(b, _) => tys.dyn_bounds(b).principal.is_some_and(|pr| is_local(pr.value.def)),
        _ => false,
    }
}

/// True when a type parameter occurs uncovered in `t` (RFC 2451): `t`
/// is the parameter itself or a fundamental wrapper (`&T`, `&mut T`,
/// `Box<T>`, `Pin<T>`) of an uncovered one. Any other type constructor
/// (`Vec<T>`, `(T,)`, `*const T`) covers the parameters inside it.
fn has_uncovered_param(tys: &impl TyIntern, t: Ty, fundamental: &[DefId]) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) => true,
        TyKind::Ref(_, _, e) => has_uncovered_param(tys, e, fundamental),
        TyKind::Adt(d, a) if fundamental.contains(&d) => {
            tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| has_uncovered_param(tys, e, fundamental)))
        }
        _ => false,
    }
}

/// The rank-0 trait predicates of one impl's where clauses, with
/// its parameters renamed by `offset` (0 keeps them as written).
fn trait_clauses_of(tys: &mut impl TyIntern, rec: &ImplRecord, offset: u32) -> Vec<TraitRef> {
    let n = rec.generics.params.len();
    rec.generics
        .predicates
        .iter()
        .filter_map(|p| match p {
            Predicate::Trait(b) if b.count == 0 => Some(b.value),
            _ => None,
        })
        .map(|tr| rename_trait_ref(tys, tr, n, offset))
        .collect()
}

/// The trait clauses of one generics list (an inherent impl's),
/// renamed by `offset`, as `trait_clauses_of` does for an impl
/// record.
fn trait_clauses_of_generics(tys: &mut impl TyIntern, generics: &Generics, offset: u32) -> Vec<TraitRef> {
    let n = generics.params.len();
    generics
        .predicates
        .iter()
        .filter_map(|p| match p {
            Predicate::Trait(b) if b.count == 0 => Some(b.value),
            _ => None,
        })
        .map(|tr| rename_trait_ref(tys, tr, n, offset))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::def::{DefPathHash, LOCAL_CRATE};

    fn def(hash: u64) -> DefId {
        DefId { krate: LOCAL_CRATE, hash: DefPathHash(hash) }
    }

    fn params(n: usize) -> Vec<ParamDef> {
        (0..n).map(|_| ParamDef { name: Sym(0), kind: ParamKind::Type, span: Span::default() }).collect()
    }

    fn trait_pred(g: &mut GlobalTys, trait_def: DefId, self_ty: Ty) -> Predicate {
        let args = g.intern_args(&[GenericArg::Ty(self_ty)]);
        Predicate::Trait(Binder::plain(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS }))
    }

    fn add_impl(
        g: &mut GlobalTys,
        index: &mut ImplIndex,
        hash: u64,
        trait_def: DefId,
        self_pat: Ty,
        rest: &[Ty],
        n_params: usize,
        predicates: Vec<Predicate>,
    ) -> ImplId {
        let mut all = vec![GenericArg::Ty(self_pat)];
        all.extend(rest.iter().map(|&t| GenericArg::Ty(t)));
        let args = g.intern_args(&all);
        let (head, blanket) = pattern_head(g, self_pat, &[]).unwrap();
        index.insert_impl(ImplRecord {
            def: def(hash),
            trait_def,
            trait_ref: TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS },
            generics: Generics { parent: None, params: params(n_params), predicates },
            assoc_tys: Vec::new(),
            assoc_consts: Vec::new(),
            items: Vec::new(),
            synthetic: Synthetic::None,
            local: true,
            span: Span::default(),
            head,
            blanket,
        })
    }

    fn is_local(d: DefId) -> bool {
        // In these fixtures every def with a hash under 1000 is a
        // local def; impl defs at 1000+ are never asked.
        d.hash.0 < 1000
    }

    /// `impl<T: A> Tr for T` against `impl<T: B> Tr for T` overlaps
    /// even with every trait local and no `A` or `B` impls: a bare
    /// parameter Self is never disprovable (E0119 class).
    #[test]
    fn two_blankets_overlap() {
        let mut g = GlobalTys::new();
        let (a_tr, b_tr, tr) = (def(10), def(11), def(12));
        let mut index = ImplIndex::new();
        let p0 = g.intern(TyKind::Param(ParamId(0)));
        let pa = trait_pred(&mut g, a_tr, p0);
        let pb = trait_pred(&mut g, b_tr, p0);
        let x = add_impl(&mut g, &mut index, 1000, tr, p0, &[], 1, vec![pa]);
        let y = add_impl(&mut g, &mut index, 1001, tr, p0, &[], 1, vec![pb]);
        assert_eq!(index.coherence_overlaps(&mut g, &[], &[], &is_local, &|_| true), [(x, y)]);
    }

    /// The orphan positive case: `impl<T: A> Tr for T` next to
    /// `impl Tr for My`, with `A` and `My` local and no
    /// `A for My` impl, does not overlap. Adding that impl makes
    /// the pair overlap.
    #[test]
    fn orphan_positive_case_accepts() {
        let mut g = GlobalTys::new();
        let (a_tr, tr, my) = (def(10), def(12), def(20));
        let mut index = ImplIndex::new();
        let p0 = g.intern(TyKind::Param(ParamId(0)));
        let my_ty = g.mk_adt(my, &[]);
        let pa = trait_pred(&mut g, a_tr, p0);
        add_impl(&mut g, &mut index, 1000, tr, p0, &[], 1, vec![pa]);
        add_impl(&mut g, &mut index, 1001, tr, my_ty, &[], 0, vec![]);
        assert!(index.coherence_overlaps(&mut g, &[], &[], &is_local, &|_| true).is_empty());
        add_impl(&mut g, &mut index, 1002, a_tr, my_ty, &[], 0, vec![]);
        assert_eq!(index.coherence_overlaps(&mut g, &[], &[], &is_local, &|_| true).len(), 1);
    }

    /// The same impl twice overlaps; the same Self with different
    /// trait inputs does not (full trait-ref matching, not Self
    /// alone).
    #[test]
    fn duplicate_overlaps_but_different_inputs_do_not() {
        let mut g = GlobalTys::new();
        let (tr, s) = (def(10), def(20));
        let mut index = ImplIndex::new();
        let s_ty = g.mk_adt(s, &[]);
        add_impl(&mut g, &mut index, 1000, tr, s_ty, &[int(IntTy::U8)], 0, vec![]);
        add_impl(&mut g, &mut index, 1001, tr, s_ty, &[int(IntTy::U16)], 0, vec![]);
        assert!(index.coherence_overlaps(&mut g, &[], &[], &is_local, &|_| true).is_empty());
        add_impl(&mut g, &mut index, 1002, tr, s_ty, &[int(IntTy::U8)], 0, vec![]);
        assert_eq!(index.coherence_overlaps(&mut g, &[], &[], &is_local, &|_| true).len(), 1);
    }

    /// The blanket-plus-concrete `IntoIterator` shape: the
    /// concrete impl's clause check sees `Range: Iter` cannot hold
    /// (local Self, no impl), so the pair stands.
    #[test]
    fn blanket_and_concrete_coexist() {
        let mut g = GlobalTys::new();
        let (iter_tr, into_tr, range, count) = (def(10), def(11), def(20), def(21));
        let mut index = ImplIndex::new();
        let p0 = g.intern(TyKind::Param(ParamId(0)));
        let range_ty = g.mk_adt(range, &[]);
        let count_ty = g.mk_adt(count, &[]);
        add_impl(&mut g, &mut index, 1000, iter_tr, count_ty, &[], 0, vec![]);
        add_impl(&mut g, &mut index, 1001, into_tr, range_ty, &[], 0, vec![]);
        let pi = trait_pred(&mut g, iter_tr, p0);
        add_impl(&mut g, &mut index, 1002, into_tr, p0, &[], 1, vec![pi]);
        assert!(index.coherence_overlaps(&mut g, &[], &[], &is_local, &|_| true).is_empty());
    }

    /// The orphan rule: foreign trait for a foreign type fails, a
    /// local trait for a foreign type passes, a foreign trait for
    /// a foreign container of a local type fails (locality is by
    /// the outer type), and a local type in a trait input passes.
    #[test]
    fn orphan_rule_sides() {
        let mut g = GlobalTys::new();
        let (foreign_tr, local_tr, foreign_adt, local_adt) = (def(5000), def(10), def(6000), def(20));
        let mut index = ImplIndex::new();
        let local_only = |d: DefId| d.hash.0 < 1000;
        let check = |g: &mut GlobalTys, index: &mut ImplIndex, tr: DefId, self_ty: Ty, n: usize| {
            let id = add_impl(g, index, 1000 + n as u64, tr, self_ty, &[], 0, vec![]);
            index.orphan_ok(g, index.get(id), &[], &local_only)
        };
        assert!(!check(&mut g, &mut index, foreign_tr, int(IntTy::U8), 1), "foreign trait, foreign scalar");
        let local_ty = g.mk_adt(local_adt, &[]);
        assert!(check(&mut g, &mut index, local_tr, int(IntTy::U32), 2), "local trait, foreign scalar");
        assert!(check(&mut g, &mut index, foreign_tr, local_ty, 3), "foreign trait, local type");
        let wrap = g.mk_adt(foreign_adt, &[GenericArg::Ty(local_ty)]);
        assert!(!check(&mut g, &mut index, foreign_tr, wrap, 4), "foreign trait, foreign container of a local type");
        // A local type as a trait input carries it: the
        // `From<Local> for u32` shape.
        let id = add_impl(&mut g, &mut index, 1010, foreign_tr, int(IntTy::U32), &[local_ty], 0, vec![]);
        assert!(index.orphan_ok(&g, index.get(id), &[], &local_only), "foreign trait, local trait input");
        // An uncovered parameter before the local type blocks it:
        // `impl<T> Foreign for Foreign2<T, Local>` is not orphan-ok.
        let p0 = g.intern(TyKind::Param(ParamId(0)));
        let wrap2 = g.mk_adt(foreign_adt, &[GenericArg::Ty(p0), GenericArg::Ty(local_ty)]);
        let id = {
            let args = g.intern_args(&[GenericArg::Ty(wrap2)]);
            let (head, blanket) = pattern_head(&g, wrap2, &[]).unwrap();
            index.insert_impl(ImplRecord {
                def: def(1005),
                trait_def: foreign_tr,
                trait_ref: TraitRef { def: foreign_tr, args, bindings: EMPTY_BINDINGS },
                generics: Generics { parent: None, params: params(1), predicates: vec![] },
                assoc_tys: Vec::new(),
                assoc_consts: Vec::new(),
                items: Vec::new(),
                synthetic: Synthetic::None,
                local: true,
                span: Span::default(),
                head,
                blanket,
            })
        };
        assert!(!index.orphan_ok(&g, index.get(id), &[], &local_only));
    }

    /// RFC 2451: a fundamental wrapper does not cover its parameter
    /// (`impl<T> Foreign<Local> for &T` and `for Box<T>` are orphans),
    /// another type constructor does (`for Vec<T>` is fine).
    #[test]
    fn orphan_rule_fundamental_does_not_cover() {
        let mut g = GlobalTys::new();
        let (foreign_tr, foreign_adt, box_adt, local_adt) = (def(5000), def(6000), def(6001), def(20));
        let mut index = ImplIndex::new();
        let local_only = |d: DefId| d.hash.0 < 1000;
        let local_ty = g.mk_adt(local_adt, &[]);
        let p0 = g.intern(TyKind::Param(ParamId(0)));
        let ref_p = g.mk_ref(false, p0);
        let box_p = g.mk_adt(box_adt, &[GenericArg::Ty(p0)]);
        let vec_p = g.mk_adt(foreign_adt, &[GenericArg::Ty(p0)]);
        let ptr_local = g.intern(TyKind::RawPtr(Mut::Shared, local_ty));
        let box_local = g.mk_adt(box_adt, &[GenericArg::Ty(local_ty)]);
        let cases = [(ref_p, Some(local_ty), false), (box_p, Some(local_ty), false), (vec_p, Some(local_ty), true), (ptr_local, None, false), (box_local, None, true)];
        for (n, (self_ty, input, ok)) in cases.into_iter().enumerate() {
            let inputs: Vec<Ty> = input.into_iter().collect();
            let id = add_impl(&mut g, &mut index, 1200 + n as u64, foreign_tr, self_ty, &inputs, 1, vec![]);
            assert_eq!(index.orphan_ok(&g, index.get(id), &[box_adt], &local_only), ok, "case {n}");
        }
    }

    /// `dyn Local` is a local type, also behind a reference (rustc's
    /// `ty_is_local_constructor`); `dyn Foreign` is not.
    #[test]
    fn orphan_rule_dyn_types() {
        let mut g = GlobalTys::new();
        let (foreign_tr, local_tr, foreign_tr2) = (def(5000), def(10), def(5001));
        let mut index = ImplIndex::new();
        let local_only = |d: DefId| d.hash.0 < 1000;
        let dyn_of = |g: &mut GlobalTys, tr: DefId| {
            let args = g.intern_args(&[GenericArg::Ty(DYN_SELF)]);
            let principal = Some(Binder::plain(TraitRef { def: tr, args, bindings: EMPTY_BINDINGS }));
            let b = g.intern_dyn_bounds(DynBounds { principal, supertraits: Box::new([]), auto: AutoTraits::default() });
            g.intern(TyKind::Dyn(b, Region::Erased))
        };
        let local_dyn = dyn_of(&mut g, local_tr);
        let foreign_dyn = dyn_of(&mut g, foreign_tr2);
        let ref_local = g.mk_ref(false, local_dyn);
        for (n, (t, ok)) in [(local_dyn, true), (ref_local, true), (foreign_dyn, false)].into_iter().enumerate() {
            let id = add_impl(&mut g, &mut index, 1100 + n as u64, foreign_tr, t, &[], 0, vec![]);
            assert_eq!(index.orphan_ok(&g, index.get(id), &[], &local_only), ok, "case {n}");
        }
    }

    /// Head-bucketed pair generation finds exactly the pairs the
    /// naive all-pairs loop finds: many distinct Adt heads, one
    /// duplicate pair, one generic-Adt pair that unifies, ref and
    /// tuple heads, and a bare-parameter blanket.
    #[test]
    fn coherence_matches_naive_all_pairs() {
        let mut g = GlobalTys::new();
        let tr = def(10);
        let mut index = ImplIndex::new();
        let p0 = g.intern(TyKind::Param(ParamId(0)));
        // 40 distinct Adt heads, no overlaps among them.
        for i in 0..40u64 {
            let t = g.mk_adt(def(100 + i), &[]);
            add_impl(&mut g, &mut index, 1000 + i, tr, t, &[], 0, vec![]);
        }
        // A duplicate of the first Adt impl: one overlap.
        let dup = g.mk_adt(def(100), &[]);
        add_impl(&mut g, &mut index, 1100, tr, dup, &[], 0, vec![]);
        // Generic Adt patterns that unify with each other.
        let vec_p = g.mk_adt(def(200), &[GenericArg::Ty(p0)]);
        let vec_u8 = g.mk_adt(def(200), &[GenericArg::Ty(int(IntTy::U8))]);
        add_impl(&mut g, &mut index, 1101, tr, vec_p, &[], 1, vec![]);
        add_impl(&mut g, &mut index, 1102, tr, vec_u8, &[], 0, vec![]);
        // A shared-ref blanket and a concrete shared-ref impl.
        let ref_p = g.intern(TyKind::Ref(Region::Erased, Mut::Shared, p0));
        let ref_u8 = g.intern(TyKind::Ref(Region::Erased, Mut::Shared, int(IntTy::U8)));
        add_impl(&mut g, &mut index, 1103, tr, ref_p, &[], 1, vec![]);
        add_impl(&mut g, &mut index, 1104, tr, ref_u8, &[], 0, vec![]);
        // A tuple impl and an int impl: different heads.
        let tup_tys = g.intern_tys(&[int(IntTy::U8), int(IntTy::U16)]);
        let tup = g.intern(TyKind::Tuple(tup_tys));
        add_impl(&mut g, &mut index, 1105, tr, tup, &[], 0, vec![]);
        add_impl(&mut g, &mut index, 1106, tr, int(IntTy::I32), &[], 0, vec![]);
        // The naive loop: every pair of the trait, in index order.
        let mut naive = Vec::new();
        let ids = index.impls_of_trait(tr).to_vec();
        for (i, &a) in ids.iter().enumerate() {
            for &b in &ids[i + 1..] {
                let (ra, rb) = (index.get(a).clone(), index.get(b).clone());
                if index.pair_overlaps(&mut g, &ra, &rb, &[], &[], &is_local) {
                    naive.push((a, b));
                }
            }
        }
        naive.sort_by_key(|(a, b)| (a.0, b.0));
        let fast = index.coherence_overlaps(&mut g, &[], &[], &is_local, &|_| true);
        assert_eq!(fast, naive);
        // The duplicate, the generic-Adt pair, and the ref pair.
        assert_eq!(fast.len(), 3);
    }
}
