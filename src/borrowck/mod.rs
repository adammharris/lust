// Borrow checking on the IR, one function at a time.
//
// 1. Initialization: forward dataflow of maybe-init and maybe-moved locals. Moves are
//    tracked per field path, so moving `p.x` leaves `p.y` usable (a partial move).
// 2. Liveness: backward dataflow of live locals at every point (use-live), and of
//    locals whose pending `Drop` may touch their regions (drop-live, ARCH 5.4).
// 3. Regions (regions.rs): rustc's NLL. Each `&place` creates a loan with a region
//    var; constraints from statements and calls say which locals' regions the loan's
//    region must contain, and whether it must outlive the fn (a universal region).
// 4. Loan scopes: a loan is in scope from its borrow through every point where one of
//    those locals is live (everywhere reachable, for a universal region), until the
//    borrowed local is overwritten. This rejects NLL problem case 3 and every other
//    "Polonius accepts, NLL rejects" shape (ARCH 5.2).
// 5. Each access is checked against the in-scope loans it conflicts with, and region
//    relations the signature does not give are L0733.
mod regions;
pub use regions::{FnBound, ImplHead, ImplRegions, RPIT_PARAM, RegionSig, RegionTables, TraitLts, check_impl_supers, elision_regions, erase, impl_trait_method, normalize_self_projections, regions_of};
pub(crate) use regions::dyn_arg_tys;
pub(crate) use regions::{adt_region_count, lub_items_fit, lub_shapes_fit, paired_slot_regions};

use crate::check::collect::*;
use crate::diag::{Diag, Span, unsupported};
use crate::ir::*;
use crate::ty::*;
use std::collections::HashSet;

/// A bitset over locals or loans. Most bodies fit in one word, and that word
/// is stored inline, so temporary sets (new loans for one statement, live
/// loans at one point) need no heap allocation. Dataflow states do not use
/// this type: see `State`.
#[derive(Clone, PartialEq, Eq)]
struct BitSet(Words);

#[derive(Clone, PartialEq, Eq)]
enum Words {
    One(u64),
    Many(Vec<u64>),
}

impl BitSet {
    fn new(n: usize) -> BitSet {
        let w = n.div_ceil(64).max(1);
        BitSet(if w == 1 { Words::One(0) } else { Words::Many(vec![0; w]) })
    }
    fn words(&self) -> &[u64] {
        match &self.0 {
            Words::One(w) => std::slice::from_ref(w),
            Words::Many(v) => v,
        }
    }
    fn words_mut(&mut self) -> &mut [u64] {
        match &mut self.0 {
            Words::One(w) => std::slice::from_mut(w),
            Words::Many(v) => v,
        }
    }
    fn insert(&mut self, i: usize) {
        bit_set(self.words_mut(), i);
    }
    fn remove(&mut self, i: usize) {
        bit_unset(self.words_mut(), i);
    }
    fn union(&mut self, o: &BitSet) -> bool {
        bits_or(self.words_mut(), o.words())
    }
    fn clear(&mut self) {
        self.words_mut().fill(0);
    }
    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        bit_iter(self.words())
    }
}

// Bit operations on word slices: the rows of a `State` and the words of a `BitSet`.

fn bit_has(w: &[u64], i: usize) -> bool {
    w[i / 64] & (1 << (i % 64)) != 0
}

fn bit_set(w: &mut [u64], i: usize) {
    w[i / 64] |= 1 << (i % 64);
}

fn bit_unset(w: &mut [u64], i: usize) {
    w[i / 64] &= !(1 << (i % 64));
}

/// `dst |= src`; true if `dst` gained a bit.
fn bits_or(dst: &mut [u64], src: &[u64]) -> bool {
    let mut changed = 0;
    for (a, b) in dst.iter_mut().zip(src) {
        changed |= b & !*a;
        *a |= b;
    }
    changed != 0
}

/// The set bits in ascending order.
fn bit_iter(w: &[u64]) -> impl Iterator<Item = usize> + '_ {
    w.iter().enumerate().flat_map(|(wi, &x)| {
        let mut x = x;
        std::iter::from_fn(move || {
            if x == 0 {
                return None;
            }
            let b = x.trailing_zeros() as usize;
            x &= x - 1;
            Some(wi * 64 + b)
        })
    })
}

/// A known slice index position: from the front, or `len - k`
/// from the back (a pattern suffix index).
#[derive(Clone, Copy, PartialEq, Eq)]
enum IdxKey {
    Front(u64),
    Back(u64),
}

/// True when index position `a` is at or before `b`: only
/// same-kind positions compare (a front offset and a back
/// offset meet only at a known length).
fn idx_le(a: IdxKey, b: IdxKey) -> Option<bool> {
    match (a, b) {
        (IdxKey::Front(x), IdxKey::Front(y)) => Some(x <= y),
        (IdxKey::Back(x), IdxKey::Back(y)) => Some(x >= y),
        _ => None,
    }
}

/// True when index `i` is outside the range `[lo, hi)`.
fn idx_outside(i: IdxKey, lo: IdxKey, hi: IdxKey) -> bool {
    idx_le(i, lo).is_some_and(|le| le && i != lo) || idx_le(hi, i).is_some_and(|le| le)
}

struct Loan {
    place: Place,
    mutable: bool,
    /// The index range of a pattern-created subslice loan
    /// (`Body::pat_subslice`): element places outside it are
    /// disjoint from this loan.
    range: Option<(IdxKey, IdxKey)>,
    /// Where the borrow starts. Used as a labeled secondary span in diagnostics.
    span: Span,
    /// The last use of the local that first holds this loan, if it is after the borrow.
    last_use: Option<Span>,
    /// The local the borrow is first stored in (the borrow statement's destination).
    holder: Option<Local>,
}

/// One field path below a local, as encoded projections (`Field`/`Downcast`). An empty path
/// is the whole local. Used to track partial moves per field.
type Path = Vec<u64>;

/// Locals assigned exactly once, from a constant integer: the index
/// temporaries pattern and loop lowering make for fixed array slots.
/// A constant index into an array names one element like a field does,
/// so moves out of it are partial moves; any other index is not exact.
pub(crate) fn const_index_locals(body: &Body) -> std::collections::HashMap<Local, u64> {
    // Locals are dense indices into `body.locals`, so the scan is
    // two flat vectors (one hash map entry and insert per assign
    // was about 99M instructions on the 48k crate). Only the few
    // surviving locals enter the returned map, whose contents are
    // the same as a hashed scan would build.
    let mut writes: Vec<u32> = vec![0; body.locals.len()];
    let mut value: Vec<Option<u64>> = vec![None; body.locals.len()];
    let mut note_write = |dest: &Place, v: Option<u64>| {
        if dest.proj.is_empty() {
            let l = dest.local as usize;
            if l >= writes.len() {
                writes.resize(l + 1, 0);
                value.resize(l + 1, None);
            }
            writes[l] += 1;
            value[l] = v;
        }
    };
    for b in &body.blocks {
        for s in &b.stmts {
            if let StmtKind::Assign(dest, rv) = &s.kind {
                let v = match rv {
                    Rvalue::Use(Operand::Const(Const::Int(v, _))) if *v <= u64::MAX as u128 => Some(*v as u64),
                    _ => None,
                };
                note_write(dest, v);
            }
        }
        if let Terminator::Call { dest, .. } = &b.term {
            note_write(dest, None);
        }
    }
    value
        .into_iter()
        .enumerate()
        .filter_map(|(l, v)| if writes[l] == 1 { v.map(|v| (l as Local, v)) } else { None })
        .collect()
}

fn is_prefix(a: &[u64], b: &[u64]) -> bool {
    a.len() <= b.len() && a.iter().zip(b).all(|(x, y)| x == y)
}

/// The word layout of a `State` for one body: `n` locals, sets over locals
/// take `wn` words, and the move-path set `wm`.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Shape {
    n: usize,
    wn: usize,
    wm: usize,
}

/// The forward dataflow state at one program point. Every set lives in one
/// flat word vector, so copying a block's entry state is one memcpy and a
/// join is one pass of word ORs. (Per-local vectors and hash sets made
/// state copies most of borrowck's time on large crates.) The sets:
///
/// - `init`, `uninit`, `moved`: maybe-initialized, maybe-uninitialized,
///   and maybe-moved locals.
/// - `ever`: locals that may have been assigned since their storage began
///   (a move does not clear it). Rust's E0384 on an immutable local uses it.
/// - `paths`: the field paths that may have been moved out of their local,
///   one bit per entry of `Ck::mpaths`. The empty path means the whole
///   local may have been moved.
#[derive(Clone, PartialEq, Eq)]
struct State {
    sh: Shape,
    w: Vec<u64>,
}

impl State {
    fn new(sh: Shape) -> State {
        State { sh, w: vec![0; 4 * sh.wn + sh.wm] }
    }
    fn init(&self) -> &[u64] {
        &self.w[..self.sh.wn]
    }
    fn init_mut(&mut self) -> &mut [u64] {
        let wn = self.sh.wn;
        &mut self.w[..wn]
    }
    fn uninit(&self) -> &[u64] {
        &self.w[self.sh.wn..2 * self.sh.wn]
    }
    fn uninit_mut(&mut self) -> &mut [u64] {
        let wn = self.sh.wn;
        &mut self.w[wn..2 * wn]
    }
    fn moved(&self) -> &[u64] {
        &self.w[2 * self.sh.wn..3 * self.sh.wn]
    }
    fn moved_mut(&mut self) -> &mut [u64] {
        let wn = self.sh.wn;
        &mut self.w[2 * wn..3 * wn]
    }
    fn ever(&self) -> &[u64] {
        &self.w[3 * self.sh.wn..4 * self.sh.wn]
    }
    fn ever_mut(&mut self) -> &mut [u64] {
        let wn = self.sh.wn;
        &mut self.w[3 * wn..4 * wn]
    }
    fn paths(&self) -> &[u64] {
        &self.w[4 * self.sh.wn..]
    }
    fn paths_mut(&mut self) -> &mut [u64] {
        let a = 4 * self.sh.wn;
        &mut self.w[a..]
    }
    fn join(&mut self, o: &State) -> bool {
        bits_or(&mut self.w, &o.w)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Access {
    Read,
    Write,
    Move,
    BorrowShared,
    BorrowMut,
    /// Drop or StorageDead: ends the local's storage.
    Dead,
}

struct Ck<'b, 'p> {
    p: &'p Program,
    body: &'b Body<'p>,
    loans: Vec<Loan>,
    /// The index of a block's first statement in body-wide statement order.
    stmt_base: Vec<usize>,
    /// Loan created by each statement (`u32::MAX` if none), by body-wide index.
    loan_at: Vec<u32>,
    preds: Vec<Vec<u32>>,
    /// Successor blocks per block, computed once: with call terminators most
    /// blocks end in a call, and recomputing edges in every pass showed up
    /// in profiles.
    succs: Vec<Vec<Bb>>,
    /// The first point of each block. A block has one point per statement
    /// plus one for its terminator; point `point_base[b] + i` is the entry
    /// of statement `i` (or of the terminator, at `i == len`).
    point_base: Vec<usize>,
    /// Use-live locals at the entry of each point, `sh.wn` words per point.
    live_entry: Vec<u64>,
    /// Drop-live locals at the entry of each point (empty when no local's
    /// drop touches regions): locals whose later `Drop` may read a region.
    drop_entry: Vec<u64>,
    /// The whole writes that drop an old value in place (sorted by point):
    /// MIR drops the old value, then the local is dead until the write, so
    /// a loan only the old value held ends there (`loan_scopes`).
    drop_gap: Vec<(usize, Local)>,
    /// Loans in scope at the entry of each point, `wl` words per point.
    scope: Vec<u64>,
    /// Words per set over loans.
    wl: usize,
    /// The region solution (set before the reporting pass).
    sol: Option<regions::Solution>,
    errs: Vec<Diag>,
    seen: HashSet<(&'static str, Span)>,
    report: bool,
    /// Creation point of each loan.
    loan_block: Vec<u32>,
    loan_stmt: Vec<u32>,
    /// Defs of Adts with a user `Drop` impl (any impl of the lang `Drop`
    /// trait whose Self head is that Adt). Computed once per body from
    /// the impl index; the partial-move checks below read it.
    drop_heads: HashSet<crate::def::DefId>,
    /// Index locals with a known constant value (see `const_index_locals`).
    const_index: std::collections::HashMap<Local, u64>,
    /// Pattern index locals holding `len - k`, by local to
    /// (k, minimum length) (`Body::pat_back_index`).
    back_index: std::collections::HashMap<Local, (u64, u64)>,
    /// Pattern prefix index locals, by local to (index,
    /// minimum length) (`Body::pat_front_index`).
    front_index: std::collections::HashMap<Local, (u64, u64)>,
    /// The layout of every `State` of this body.
    sh: Shape,
    /// Every exact path the body moves out of (see `prefix_of`), as
    /// `(local, path)`, sorted. `State::paths` has one bit per entry.
    mpaths: Vec<(Local, Path)>,
    /// The `mpaths` index range of each local's paths.
    mpath_at: Vec<(u32, u32)>,
    /// Reused operand list of the statement being checked, so a statement
    /// visit does not allocate.
    ops_buf: Vec<&'b Operand>,
    /// The two-phase receiver and argument loans of the call being
    /// checked, while its arguments are: until the call activates them,
    /// they are shared borrows.
    reserved: Vec<usize>,
    /// Per local: it holds only one byte string literal's bytes
    /// (`ir::byte_blob_locals`), so its storage ending drops
    /// nothing a borrow of it reads. Codegen gives such a local
    /// static storage, so a borrow of it may escape the function,
    /// as a byte string literal is `&'static [u8; N]` in Rust.
    promoted: Vec<bool>,
}

/// The Adt defs that have a user `Drop` impl: every impl of the lang
/// `Drop` trait whose Self type head is an Adt. Conditional impls
/// count (the partial-move checks are conservative).
fn drop_heads(p: &Program) -> HashSet<crate::def::DefId> {
    let mut out = HashSet::new();
    for &id in p.gx.index.impls_of_trait(p.gx.lang.drop) {
        let rec = p.gx.index.get(id);
        if let Some(self_ty) = p.tys.args(rec.trait_ref.args).first().and_then(|g| g.as_ty()) {
            if let TyKind::Adt(def, _) = p.tys.kind(self_ty) {
                out.insert(def);
            }
        }
    }
    out
}

/// True when a type mentions an `impl Trait` (opaque) type anywhere.
fn mentions_opaque(tys: &impl TyIntern, t: Ty) -> bool {
    let args = |a: ArgsId| tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| mentions_opaque(tys, e)));
    match tys.kind(t) {
        TyKind::Opaque(..) => true,
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => mentions_opaque(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| mentions_opaque(tys, e)),
        TyKind::Adt(_, a) | TyKind::Closure(_, a) | TyKind::FnDef(_, a) | TyKind::Projection(_, a) => args(a),
        _ => false,
    }
}

/// The universal regions of a body's own signature: its fn's region
/// signature (a closure body's from the closure rule, an instance's from
/// its template), or one unrelated universal per slot when lust has none.
fn own_sig(p: &Program, body: &Body) -> regions::OwnSig {
    use crate::check::generics::FnClass;
    let f = body.fn_id;
    let class = p.gx.fn_class.get(f.0 as usize).copied().unwrap_or_default();
    let closure = p.gx.closure_fns.contains_key(&f);
    // Instances (and closures of instances) are not checked for universal
    // relations: rustc checks the template, which lust checks too, and the
    // instance sees through type params where the call rules are coarser.
    let of_instance = |g: LocalDefId| p.gx.fn_class.get(g.0 as usize) == Some(&FnClass::Instance);
    let check = class != FnClass::Instance
        && !(closure && p.gx.closure_fns.get(&f).and_then(|d| p.gx.closures.get(d)).is_some_and(|c| of_instance(c.parent)));
    let sig = p.regions.own_body_sig(p, f);
    regions::OwnSig::build(p, body, sig, closure, check)
}

/// True when a local of `body` mentions an `impl Trait` type that the
/// region pass does not track: one lowering did not mark in
/// `Body::opaque_locals` (held by value, a capture var per region the
/// opaque captures), unless the view holds no region of it.
fn untracked_opaque(p: &Program, body: &Body) -> bool {
    body.locals.iter().enumerate().any(|(i, l)| {
        mentions_opaque(&body.tys, l.ty)
            && crate::check::opaque::view_hold(p, &body.tys, l.ty) != crate::check::opaque::Hold::None
            && !body.opaque_locals.contains(&(i as Local))
    })
}

/// What a closure body needs between its captured and free argument
/// regions and `'static`, and what its output slots may hold (rustc's
/// closure requirements; `regions::End`), for its creator. A `call_out`
/// closure also gives what its output slots must outlive (`(Out(k),
/// x)`), which only `flow_closure_output` proves; every other creator
/// path skips those pairs, and `Builder::out_reqs_unproved` reports them. None when the
/// body has lowering errors or an `impl Trait` value the region pass does not
/// track (`untracked_opaque`).
fn closure_requirements(p: &Program, body: &Body) -> Option<Vec<(regions::End, regions::End)>> {
    if !body.lower_errs.is_empty() || untracked_opaque(p, body) {
        return None;
    }
    let mut ck = Ck::new(p, body);
    ck.collect_loans();
    let own = own_sig(p, body);
    if !own.closure {
        return None;
    }
    let ends = own.ends.clone();
    let call_out = own.call_out;
    let mut b = regions::Builder::new(p, body, own, ck.loans.len(), &ck.loan_at, &ck.stmt_base);
    b.build();
    let sol = b.solve();
    let end = |u: u32| ends.get(u as usize).copied().flatten();
    Some(
        sol.reqs
            .iter()
            .filter_map(|&(a, b)| Some((end(a)?, end(b)?)))
            .filter(|(a, b)| !matches!(a, regions::End::Out(_)) || call_out && !matches!(b, regions::End::Out(_)))
            .collect(),
    )
}

impl<'b, 'p> Ck<'b, 'p> {
    fn new(p: &'p Program, body: &'b Body<'p>) -> Self {
        let drop_heads = drop_heads(p);
        Ck {
            p,
            body,
            loans: Vec::new(),
            stmt_base: Vec::new(),
            loan_at: Vec::new(),
            preds: vec![Vec::new(); body.blocks.len()],
            succs: Vec::new(),
            point_base: Vec::new(),
            live_entry: Vec::new(),
            drop_entry: Vec::new(),
            drop_gap: Vec::new(),
            scope: Vec::new(),
            wl: 0,
            sol: None,
            errs: Vec::new(),
            seen: HashSet::new(),
            report: false,
            loan_block: Vec::new(),
            loan_stmt: Vec::new(),
            drop_heads,
            const_index: {
                let mut c = const_index_locals(body);
                if !body.index_exprs.is_empty() {
                    let user: HashSet<Local> = body.index_exprs.iter().copied().collect();
                    c.retain(|l, _| !user.contains(l));
                }
                c
            },
            back_index: body.pat_back_index.iter().map(|&(l, k, m)| (l, (k, m))).collect(),
            front_index: body.pat_front_index.iter().map(|&(l, i, m)| (l, (i, m))).collect(),
            sh: Shape { n: 0, wn: 0, wm: 0 },
            mpaths: Vec::new(),
            mpath_at: Vec::new(),
            ops_buf: Vec::new(),
            reserved: Vec::new(),
            promoted: crate::ir::byte_blob_locals(body).iter().map(|b| b.is_some()).collect(),
        }
    }
}

/// True for a mono instance body, or a closure body fn inside one (at any
/// depth). Its template, and the template's closures, are borrow-checked
/// once as written (`check::generics::template_check`, in `lust check` and
/// in builds alike), as rustc checks only the generic body.
fn in_instance(p: &Program, f: LocalDefId) -> bool {
    use crate::check::generics::FnClass;
    let mut f = f;
    loop {
        match p.gx.fn_class.get(f.0 as usize) {
            Some(FnClass::Instance) => return true,
            Some(FnClass::Closure) => match p.gx.closure_fns.get(&f).and_then(|d| p.gx.closures.get(d)) {
                Some(c) => f = c.parent,
                None => return false,
            },
            _ => return false,
        }
    }
}

/// Borrow-checks one function body. An instance body reports only its
/// lowering errors (`in_instance`): `lust check` makes no instances, so a build that
/// checked them would reject programs `lust check` accepts, where the
/// instance's concrete types (a `T` that holds a lifetime) meet the call
/// rules that the template's opaque params never reach.
pub fn borrowck(p: &Program, body: &Body) -> Vec<Diag> {
    if !body.lower_errs.is_empty() {
        return body.lower_errs.clone();
    }
    if in_instance(p, body.fn_id) {
        return Vec::new();
    }
    let mut ck = Ck::new(p, body);
    // An `impl Trait` value in a view body (a template check) is
    // tracked through `Body::opaque_locals`: its local gets a capture
    // var for every region the opaque captures, drop-live unless its
    // bounds say `Copy` (regions.rs `cap_var`). A local that mentions
    // an opaque without that mark (lowering did not hold it by value)
    // keeps the reject: its borrows would not be seen.
    if untracked_opaque(p, body) {
        return vec![Diag::new(
            "L0602",
            p.fn_def(body.fn_id).name_span,
            "the borrow checker does not track `impl Trait` values yet",
            "Return a named type instead of `impl Trait`.",
        )];
    }
    let own = own_sig(p, body);
    if own.check
        && let Some(d) = regions::impl_contract(p, body.fn_id)
    {
        ck.errs.push(d);
    }
    check_with(ck, own)
}

/// Borrow-checks the body of an anonymous const (lower.rs
/// `check_anon_consts`): no parameters, and a value of type `ret` (its
/// regions `'static`) in local 0, as a const item's initializer body.
pub fn borrowck_const(p: &Program, body: &Body, ret: Ty) -> Vec<Diag> {
    if !body.lower_errs.is_empty() {
        return body.lower_errs.clone();
    }
    if in_instance(p, body.fn_id) || untracked_opaque(p, body) {
        return Vec::new();
    }
    let sig = RegionSig::const_value(ret);
    let own = regions::OwnSig::build(p, body, Some(&sig), false, true);
    check_with(Ck::new(p, body), own)
}

/// The passes of `borrowck` after its own signature is known.
fn check_with<'b, 'p>(mut ck: Ck<'b, 'p>, own: regions::OwnSig) -> Vec<Diag> {
    let (p, body) = (ck.p, ck.body);
    ck.collect_loans();
    ck.collect_move_paths();
    let n = body.locals.len();
    ck.sh = Shape { n, wn: n.div_ceil(64).max(1), wm: ck.mpaths.len().div_ceil(64) };
    ck.wl = ck.loans.len().div_ceil(64);
    ck.compute_preds();
    let entry = ck.init_fixpoint();
    // A body with no loans needs no regions: no loan can conflict, and a
    // universal relation can only fail through a loan or a reference value
    // that flows between parameters, which the region pass checks below.
    // A dyn type with late-bound places (R11) may meet one with fixed
    // places, a type error only the region pass sees.
    let needs_regions = !ck.loans.is_empty() || own.n_univ > 0 || regions::may_entail_bounds(p, body) || regions::has_dyn_late(body);
    if needs_regions {
        let mut b = regions::Builder::new(p, body, own, ck.loans.len(), &ck.loan_at, &ck.stmt_base);
        b.build();
        let sol = b.solve();
        ck.errs.extend(sol.errs.iter().cloned());
        ck.sol = Some(sol);
        if !ck.loans.is_empty() {
            ck.liveness(&entry);
            ck.loan_scopes();
        }
    }
    static DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *DEBUG.get_or_init(|| std::env::var_os("LUST_BCK_DEBUG").is_some()) {
        ck.debug_dump();
    }
    ck.report_pass(&entry);
    ck.errs
}

fn successors(t: &Terminator) -> Vec<Bb> {
    match t {
        Terminator::Goto(b) => vec![*b],
        Terminator::If(_, a, b) => vec![*a, *b],
        Terminator::Switch(_, cases, other) => cases.iter().map(|c| c.1).chain(std::iter::once(*other)).collect(),
        Terminator::Call { next, unwind, .. } => std::iter::once(*next).chain(*unwind).collect(),
        _ => Vec::new(),
    }
}

/// Calls `f` for every operand read by an rvalue, in evaluation order.
fn rvalue_operands<'r>(rv: &'r Rvalue, f: &mut impl FnMut(&'r Operand)) {
    match rv {
        Rvalue::Use(o)
        | Rvalue::Un(_, o)
        | Rvalue::Cast(o, _)
        | Rvalue::Opt(_, Some(o))
        | Rvalue::Res(_, _, o)
        | Rvalue::MakeDyn { ptr: o, .. }
        | Rvalue::DynUpcast { ptr: o, .. }
        | Rvalue::DynMeta { ptr: o, .. }
        | Rvalue::DynData { ptr: o, .. } => f(o),
        Rvalue::Opt(_, None) => {}
        Rvalue::Bin(_, a, b) | Rvalue::StrCmp(_, a, b) | Rvalue::StringAdd(a, b) | Rvalue::Eq { a, b, .. } | Rvalue::Cmp { a, b, .. } => {
            f(a);
            f(b);
        }
        Rvalue::VecRepeat(_, a, b) => {
            f(a);
            f(b);
        }
        Rvalue::Aggregate(_, _, ops) | Rvalue::VecLit(_, ops) | Rvalue::TupleAgg(_, ops) | Rvalue::ArrayAgg(_, ops) => {
            ops.iter().for_each(f)
        }
        Rvalue::ArrayRepeat(_, o, _) => f(o),
        Rvalue::Format(parts) => parts.iter().for_each(|p| {
            if let FmtPart::Arg { value, .. } = p {
                f(value)
            }
        }),
        Rvalue::WriteFmt(dst, parts, _) | Rvalue::FormatArgs(Some(dst), parts) => {
            f(dst);
            parts_operands(parts, f);
        }
        Rvalue::FormatArgs(None, parts) => parts_operands(parts, f),
        Rvalue::Ref(..)
        | Rvalue::Discriminant(_)
        | Rvalue::SliceOf(_)
        | Rvalue::LenOf(_)
        | Rvalue::StaticLoad(_)
        | Rvalue::StaticRef(_)
        | Rvalue::FnValue(..)
        | Rvalue::ItemShim(..) => {}
        Rvalue::Subslice { lo, hi, .. } => {
            f(lo);
            if let Some(h) = hi {
                f(h);
            }
        }
    }
}

fn parts_operands<'r>(parts: &'r [FmtPart], f: &mut impl FnMut(&'r Operand)) {
    for p in parts {
        if let FmtPart::Arg { value, .. } = p {
            f(value);
        }
    }
}

/// True if two places may refer to overlapping memory.
/// `consts` are the constant index locals (`Ck::const_index`): two
/// different constant indexes, which only patterns make, name disjoint
/// elements, as rustc's `ConstantIndex`. Two different back
/// offsets (`Ck::back_index`) name disjoint elements too; a
/// front offset and a back offset may still meet.
fn overlap(
    a: &Place,
    b: &Place,
    consts: &std::collections::HashMap<Local, u64>,
    fronts: &std::collections::HashMap<Local, (u64, u64)>,
    backs: &std::collections::HashMap<Local, (u64, u64)>,
) -> bool {
    if a.local != b.local {
        return false;
    }
    // A pattern prefix index and a pattern back offset of one
    // slice are disjoint when they cannot meet at the
    // pattern's length lower bound or any greater length.
    let front_back = |i: &Local, j: &Local| {
        fronts.get(i).is_some_and(|&(c, mf)| backs.get(j).is_some_and(|&(k, mb)| c + k < mf.max(mb)))
    };
    for (x, y) in a.proj.iter().zip(&b.proj) {
        match (x, y) {
            (Proj::Field(i), Proj::Field(j)) if i != j => return false,
            (Proj::Index(i), Proj::Index(j)) if consts.get(i).is_some_and(|c| consts.get(j).is_some_and(|d| c != d)) => return false,
            (Proj::Index(i), Proj::Index(j)) if backs.get(i).is_some_and(|(c, _)| backs.get(j).is_some_and(|(d, _)| c != d)) => return false,
            (Proj::Index(i), Proj::Index(j)) if front_back(i, j) || front_back(j, i) => return false,
            _ => {}
        }
    }
    true
}

impl<'b, 'p> Ck<'b, 'p> {
    /// Prints the body, its loans, and their scopes (LUST_BCK_DEBUG).
    fn debug_dump(&self) {
        eprintln!("== borrowck {}", self.p.display_name(self.p.fn_info(self.body.fn_id).name));
        for (i, l) in self.body.locals.iter().enumerate() {
            let mut rs = Vec::new();
            regions::regions_of(&self.body.tys, l.ty, &mut rs);
            eprintln!("  _{i}: {:?} {} {rs:?}", l.name, crate::check::collect::ty_name(self.p, &self.body.tys, l.ty));
        }
        for (bi, b) in self.body.blocks.iter().enumerate() {
            eprintln!("  bb{bi}:");
            for (si, s) in b.stmts.iter().enumerate() {
                let q = self.point_base[bi] + si;
                let sc: Vec<usize> = if self.scope.is_empty() { Vec::new() } else { bit_iter(&self.scope[q * self.wl..(q + 1) * self.wl]).collect() };
                eprintln!("    [{q}] {:?}   scope={sc:?}", s.kind);
            }
            eprintln!("    term {:?}", b.term);
        }
        if let Some(sol) = &self.sol {
            for (i, l) in self.loans.iter().enumerate() {
                let us: Vec<usize> = bit_iter(sol.use_set(i)).collect();
                eprintln!("  loan {i}: {:?} mut={} univ={} ret={} use={us:?}", l.place, l.mutable, sol.univ[i], sol.to_ret[i]);
            }
        }
    }

    fn n_locals(&self) -> usize {
        self.body.locals.len()
    }
    fn local_name(&self, l: Local) -> String {
        match &self.body.locals[l as usize].name {
            Some(n) => format!("`{n}`"),
            None => "a temporary value".into(),
        }
    }
    fn err(&mut self, code: &'static str, span: Span, msg: String, fix: &str) {
        self.err_labeled(code, span, msg, fix, Vec::new());
    }

    /// Reports an error with labeled secondary spans (where a borrow starts, where it is used).
    fn err_labeled(&mut self, code: &'static str, span: Span, msg: String, fix: &str, labels: Vec<(Span, &'static str)>) {
        if self.report && self.seen.insert((code, span)) {
            let mut d = Diag::new(code, span, msg, fix);
            for (s, text) in labels {
                if s != span && s != Span::default() {
                    d = d.with_label(s, text);
                }
            }
            self.errs.push(d);
        }
    }

    /// Labels for a loan: where the borrow starts, and where the borrow is used later.
    fn loan_labels(loan: &Loan) -> Vec<(Span, &'static str)> {
        let mut labels = vec![(loan.span, if loan.mutable { "mutably borrowed here" } else { "borrowed here" })];
        if let Some(u) = loan.last_use {
            labels.push((u, "borrow later used here"));
        }
        labels
    }

    // ---------- Setup ----------

    fn collect_loans(&mut self) {
        let mut holders: Vec<Option<Local>> = Vec::new();
        let mut base = 0;
        for b in &self.body.blocks {
            self.stmt_base.push(base);
            base += b.stmts.len();
        }
        self.loan_at = vec![u32::MAX; base];
        for (bi, b) in self.body.blocks.iter().enumerate() {
            for (si, s) in b.stmts.iter().enumerate() {
                // SliceOf and Subslice make slice references, so they create
                // loans just like Ref (W-CORELANG); mutability comes from the
                // destination local's slice reference type.
                let loan_src: Option<(bool, &Place)> = match &s.kind {
                    StmtKind::Assign(_, Rvalue::Ref(m, place)) => Some((*m, place)),
                    StmtKind::Assign(dest, Rvalue::SliceOf(place)) => Some((self.slice_dest_mut(dest), place)),
                    StmtKind::Assign(_, Rvalue::Subslice { base, mutable, .. }) => Some((*mutable, base)),
                    _ => None,
                };
                // A promoted temporary (`&[]`) is `'static`: no loan.
                let loan_src = loan_src.filter(|(_, place)| !self.body.promoted.contains(&place.local));
                // A reference to a slice pattern's subslice temporary (a
                // `tail @ ..` binding) is no loan of the temporary: it is
                // the subslice's own loan of the base place (regions.rs
                // takes that loan's var for it).
                let loan_src = loan_src.filter(|(_, place)| !(place.proj.is_empty() && self.body.pat_subslice.contains(&place.local)));
                if let (StmtKind::Assign(dest, _), Some((m, place))) = (&s.kind, loan_src) {
                    self.loan_block.push(bi as u32);
                    self.loan_stmt.push(si as u32);
                    self.loan_at[self.stmt_base[bi] + si] = self.loans.len() as u32;
                    let holder = if dest.proj.is_empty() { Some(dest.local) } else { None };
                    holders.push(holder);
                    let range = match &s.kind {
                        StmtKind::Assign(dest, Rvalue::Subslice { lo, hi, inclusive, .. }) => self.subslice_range(dest, lo, hi, *inclusive),
                        _ => None,
                    };
                    self.loans.push(Loan { place: place.clone(), mutable: m, range, span: s.span, last_use: None, holder });
                }
            }
        }
        // For each loan, find the last read of a local that holds it. Holders start at the
        // borrow's destination local and follow plain copies. This is the "borrow later used
        // here" label. It is an approximation: it does not follow calls or aggregates.
        let mut copies: Vec<(Local, Local)> = Vec::new();
        for b in &self.body.blocks {
            for s in &b.stmts {
                if let StmtKind::Assign(dest, Rvalue::Use(Operand::Copy(p) | Operand::Move(p))) = &s.kind
                    && dest.proj.is_empty()
                    && p.proj.is_empty()
                {
                    copies.push((p.local, dest.local));
                }
            }
        }
        let mut uses: Vec<(Local, Span)> = Vec::new();
        for b in &self.body.blocks {
            for s in &b.stmts {
                let mut note = |o: &Operand| {
                    if let Operand::Copy(p) | Operand::Move(p) = o {
                        uses.push((p.local, s.span));
                    }
                };
                match &s.kind {
                    // A reborrow of a holder (for example for a method call) also counts as a use.
                    StmtKind::Assign(_, Rvalue::Ref(_, p))
                    | StmtKind::Assign(_, Rvalue::Discriminant(p))
                    | StmtKind::Assign(_, Rvalue::LenOf(p))
                    | StmtKind::Assign(_, Rvalue::SliceOf(p))
                    | StmtKind::Assign(_, Rvalue::Subslice { base: p, .. }) => uses.push((p.local, s.span)),
                    StmtKind::Assign(_, rv) => rvalue_operands(rv, &mut note),
                    StmtKind::Print { parts, .. } => parts_operands(parts, &mut note),
                    _ => {}
                }
            }
            let span = b.term_span;
            let mut note = |o: &Operand| {
                if let Operand::Copy(p) | Operand::Move(p) = o {
                    uses.push((p.local, span));
                }
            };
            match &b.term {
                Terminator::If(o, ..) | Terminator::Switch(o, ..) => note(o),
                Terminator::Call { target, args, .. } => {
                    if let CallTarget::Indirect(callee) = target {
                        note(&Operand::Copy(Place::local(*callee)));
                    }
                    args.iter().for_each(&mut note);
                }
                Terminator::Panic(parts) => parts_operands(parts, &mut note),
                _ => {}
            }
        }
        for (i, loan) in self.loans.iter_mut().enumerate() {
            let Some(first) = holders[i] else { continue };
            let mut holders_set = vec![first];
            let mut at = 0;
            while at < holders_set.len() {
                let from = holders_set[at];
                at += 1;
                for &(src, dst) in &copies {
                    if src == from && !holders_set.contains(&dst) {
                        holders_set.push(dst);
                    }
                }
            }
            loan.last_use =
                uses.iter().filter(|&&(l, s)| s.lo > loan.span.lo && holders_set.contains(&l)).map(|&(_, s)| s).max_by_key(|s| s.lo);
        }
    }

    /// Fills `mpaths`: the exact paths (`prefix_of`) of every move operand,
    /// at the same operand sites `operand` checks (rvalue and print
    /// operands, call arguments, branch conditions, panic arguments).
    /// Needs `const_index`.
    fn collect_move_paths(&mut self) {
        let mut all: Vec<(Local, Path)> = Vec::new();
        let mut note = |o: &Operand| {
            if let Operand::Move(p) = o
                && let (path, true) = self.prefix_of(p)
            {
                all.push((p.local, path));
            }
        };
        for b in &self.body.blocks {
            for s in &b.stmts {
                match &s.kind {
                    StmtKind::Assign(_, rv) => rvalue_operands(rv, &mut note),
                    StmtKind::Print { parts, .. } => parts_operands(parts, &mut note),
                    _ => {}
                }
            }
            match &b.term {
                Terminator::Call { args, .. } => args.iter().for_each(&mut note),
                Terminator::If(o, ..) | Terminator::Switch(o, ..) => note(o),
                Terminator::Panic(parts) => parts_operands(parts, &mut note),
                _ => {}
            }
        }
        all.sort();
        all.dedup();
        let mut at = vec![(0u32, 0u32); self.body.locals.len()];
        for (i, (l, _)) in all.iter().enumerate() {
            let e = &mut at[*l as usize];
            if e.1 == 0 {
                e.0 = i as u32;
            }
            e.1 = i as u32 + 1;
        }
        self.mpaths = all;
        self.mpath_at = at;
    }

    /// The `mpaths` indices of local `l`'s move paths.
    fn mpath_range(&self, l: usize) -> std::ops::Range<usize> {
        let (a, b) = self.mpath_at[l];
        a as usize..b as usize
    }

    /// The `mpaths` index of local `l`'s exact path `path`, if the body
    /// moves out of it.
    fn mpath_index(&self, l: usize, path: &[u64]) -> Option<usize> {
        self.mpath_range(l).find(|&i| self.mpaths[i].1 == path)
    }

    /// Clears every moved path of local `l`.
    fn clear_paths(&self, st: &mut State, l: usize) {
        for i in self.mpath_range(l) {
            bit_unset(st.paths_mut(), i);
        }
    }

    /// The moved paths of local `l` in `st`, in `mpaths` order.
    fn moved_paths<'s>(&'s self, st: &'s State, l: usize) -> impl Iterator<Item = &'s Path> + 's {
        self.mpath_range(l).filter(move |&i| bit_has(st.paths(), i)).map(move |i| &self.mpaths[i].1)
    }

    fn compute_preds(&mut self) {
        self.compute_points();
        self.succs = self.body.blocks.iter().map(|b| successors(&b.term)).collect();
        for &(from, to) in &self.body.false_edges {
            self.succs[from.0 as usize].push(to);
        }
        for bi in 0..self.succs.len() {
            for k in 0..self.succs[bi].len() {
                let s = self.succs[bi][k];
                self.preds[s.0 as usize].push(bi as u32);
            }
        }
    }

    // ---------- Liveness ----------

    fn uses_place(set: &mut BitSet, p: &Place) {
        set.insert(p.local as usize);
        for pr in &p.proj {
            if let Proj::Index(i) = pr {
                set.insert(*i as usize);
            }
        }
    }

    /// Backward transfer for one statement: live-in from live-out.
    fn live_stmt(s: &StmtKind, live: &mut BitSet) {
        match s {
            StmtKind::Assign(dest, rv) => {
                if dest.proj.is_empty() {
                    live.remove(dest.local as usize);
                } else {
                    Self::uses_place(live, dest);
                }
                let mut uses = |o: &Operand| {
                    if let Operand::Copy(p) | Operand::Move(p) = o {
                        Self::uses_place(live, p);
                    }
                };
                rvalue_operands(rv, &mut uses);
                if let Rvalue::Ref(_, p) | Rvalue::Discriminant(p) | Rvalue::SliceOf(p) | Rvalue::LenOf(p) = rv {
                    Self::uses_place(live, p);
                }
                if let Rvalue::Subslice { base, .. } = rv {
                    Self::uses_place(live, base);
                }
            }
            StmtKind::StorageDead(l) => live.remove(*l as usize),
            StmtKind::Drop(_) => {}
            StmtKind::FakeRead(l) => live.insert(*l as usize),
            StmtKind::Print { parts, .. } => parts_operands(parts, &mut |o| {
                if let Operand::Copy(p) | Operand::Move(p) = o {
                    Self::uses_place(live, p);
                }
            }),
        }
    }

    fn live_term(t: &Terminator, live: &mut BitSet) {
        fn uses(live: &mut BitSet, o: &Operand) {
            if let Operand::Copy(p) | Operand::Move(p) = o {
                Ck::uses_place(live, p);
            }
        }
        match t {
            Terminator::If(o, ..) | Terminator::Switch(o, ..) => uses(live, o),
            Terminator::Call { target, args, dest, .. } => {
                if dest.proj.is_empty() {
                    live.remove(dest.local as usize);
                } else {
                    Self::uses_place(live, dest);
                }
                if let CallTarget::Indirect(callee) = target {
                    live.insert(*callee as usize);
                }
                for o in args {
                    uses(live, o);
                }
            }
            Terminator::Return => live.insert(0),
            Terminator::Panic(parts) => parts_operands(parts, &mut |o| uses(live, o)),
            _ => {}
        }
    }

    /// The first point of each block, plus a sentinel past the last.
    fn compute_points(&mut self) {
        let mut base = 0;
        self.point_base.clear();
        for b in &self.body.blocks {
            self.point_base.push(base);
            base += b.stmts.len() + 1;
        }
        self.point_base.push(base);
    }

    /// Backward liveness to a fixpoint, then the live set at each point's
    /// entry. With `drop_uses`, this is drop-liveness: only a `Drop` whose
    /// point is marked uses its local; whole-local assignments and
    /// `StorageDead` kill. Otherwise every read is a use.
    fn backward(&self, drop_uses: Option<&[bool]>, init_entry: Option<&[Option<State>]>) -> Vec<u64> {
        let n = self.n_locals();
        let nb = self.body.blocks.len();
        let mut live_in = vec![BitSet::new(n); nb];
        let mut live = BitSet::new(n);
        // Successors first (back edges aside), then unreachable blocks, so a
        // sweep mostly sees final successor sets. Any order gives the same.
        let mut order: Vec<u32> = self.reverse_postorder();
        order.reverse();
        let mut listed = vec![false; nb];
        for &b in &order {
            listed[b as usize] = true;
        }
        order.extend((0..nb as u32).rev().filter(|&b| !listed[b as usize]));
        let mut changed = true;
        while changed {
            changed = false;
            for &bi in &order {
                let bi = bi as usize;
                self.block_backward(bi, &live_in, &mut live, drop_uses, None);
                // Drop-liveness ends where the local is not maybe-init:
                // a shared cleanup block's marked `Drop` (live on the
                // path that still owns the value) must not flow back
                // into blocks the value was already moved out of.
                if let Some(entry) = init_entry
                    && let Some(e) = &entry[bi]
                {
                    for (w, m) in live.words_mut().iter_mut().zip(e.init()) {
                        *w &= m;
                    }
                }
                if live != live_in[bi] {
                    live_in[bi] = live.clone();
                    changed = true;
                }
            }
        }
        let wn = self.sh.wn;
        let mut out = vec![0u64; self.point_base[nb] * wn];
        for bi in 0..nb {
            self.block_backward(bi, &live_in, &mut live, drop_uses, Some(&mut out));
            if let Some(entry) = init_entry
                && let Some(e) = &entry[bi]
            {
                let base = self.point_base[bi];
                for (w, m) in out[base * wn..(base + 1) * wn].iter_mut().zip(e.init()) {
                    *w &= m;
                }
            }
        }
        out
    }

    /// One block of `backward`: leaves the block's live-in set in `live`,
    /// and records each point's entry set in `out` when given.
    fn block_backward(&self, bi: usize, live_in: &[BitSet], live: &mut BitSet, drop_uses: Option<&[bool]>, mut out: Option<&mut Vec<u64>>) {
        let b = &self.body.blocks[bi];
        let wn = self.sh.wn;
        let base = self.point_base[bi];
        live.clear();
        for s in &self.succs[bi] {
            live.union(&live_in[s.0 as usize]);
        }
        match drop_uses {
            None => Self::live_term(&b.term, live),
            Some(du) => {
                if let Terminator::Call { dest, .. } = &b.term
                    && dest.proj.is_empty()
                {
                    Self::drop_def(live, dest.local, du[base + b.stmts.len()]);
                }
                // A whole-local move out ends the local's own `Drop`:
                // after it, the local is not drop-live, not even on
                // this call's unwind edge into a shared cleanup block
                // whose `Drop` of it is marked for another path.
                let mut kill = |o: &Operand| {
                    if let Operand::Move(p) = o
                        && p.proj.is_empty()
                    {
                        live.remove(p.local as usize);
                    }
                };
                match &b.term {
                    Terminator::Call { args, .. } => args.iter().for_each(&mut kill),
                    Terminator::If(o, ..) | Terminator::Switch(o, ..) => kill(o),
                    Terminator::Panic(parts) => parts_operands(parts, &mut kill),
                    _ => {}
                }
            }
        }
        let tp = base + b.stmts.len();
        if let Some(o) = out.as_deref_mut() {
            o[tp * wn..(tp + 1) * wn].copy_from_slice(live.words());
        }
        for (si, s) in b.stmts.iter().enumerate().rev() {
            match drop_uses {
                None => Self::live_stmt(&s.kind, live),
                Some(du) => {
                    match &s.kind {
                        StmtKind::Assign(dest, _) if dest.proj.is_empty() => Self::drop_def(live, dest.local, du[base + si]),
                        StmtKind::StorageDead(l) => live.remove(*l as usize),
                        StmtKind::Drop(l) if du[base + si] => live.insert(*l as usize),
                        _ => {}
                    }
                    // Whole-local moves out, as at a terminator.
                    let mut kill = |o: &Operand| {
                        if let Operand::Move(p) = o
                            && p.proj.is_empty()
                        {
                            live.remove(p.local as usize);
                        }
                    };
                    match &s.kind {
                        StmtKind::Assign(_, rv) => rvalue_operands(rv, &mut kill),
                        StmtKind::Print { parts, .. } => parts_operands(parts, &mut kill),
                        _ => {}
                    }
                }
            }
            if let Some(o) = out.as_deref_mut() {
                let p = base + si;
                o[p * wn..(p + 1) * wn].copy_from_slice(live.words());
            }
        }
    }

    /// Drop-liveness at a whole-local write of `l`: the write kills it,
    /// unless it drops an old opaque value in place (`use_old`, see
    /// `liveness`), which is a use of that value first.
    fn drop_def(live: &mut BitSet, l: Local, use_old: bool) {
        if use_old {
            live.insert(l as usize);
        } else {
            live.remove(l as usize);
        }
    }

    /// Use-liveness at every point, and drop-liveness when some local's
    /// drop touches its regions: a `Drop` of a maybe-initialized local with
    /// drop-live slots is a use of those regions (ARCH 5.4). `entry` is the
    /// init fixpoint, which says whether a local may be initialized at its
    /// `Drop` (a drop of a moved-out local runs no destructor).
    fn liveness(&mut self, entry: &[Option<State>]) {
        self.live_entry = self.backward(None, None);
        let drop_live = match &self.sol {
            Some(sol) if sol.drop_live.iter().any(|&d| d) => sol.drop_live.clone(),
            _ => return,
        };
        let mut uses = vec![false; self.point_base[self.body.blocks.len()]];
        let mut st = State::new(self.sh);
        let body = self.body;
        // A whole write of a maybe-initialized local whose drop uses its
        // regions drops the old value first, as the `Drop` rustc puts
        // before the write: a use of the old value's borrows (E0503 on
        // `x += 1; h = G(&mut y);` after `h = G(&mut x)`). A value the
        // write itself moves out first (`h = g(h)`) drops nothing. After
        // that drop the local is dead until the write (`drop_gap`), but
        // for an `impl Trait` value (`Body::opaque_locals`) rustc keeps
        // the borrows the old value captured in scope while the local
        // stays live (E0506 on `it = None; c.n = 1;` after
        // `it = Some(f(&c))`).
        let opaque: Vec<Local> = body.opaque_locals.iter().copied().filter(|l| !body.opaque_nodrop.contains(l)).collect();
        let mut gaps: Vec<(usize, Local)> = Vec::new();
        let mut overwrites = |st: &State, q: usize, dest: &Place, ops: &[&Operand]| {
            let l = dest.local;
            let hit = dest.proj.is_empty()
                && (drop_live[l as usize] || opaque.contains(&l))
                && bit_has(st.init(), l as usize)
                && !ops.iter().any(|o| matches!(o, Operand::Move(pl) if pl.local == l && pl.proj.is_empty()));
            if hit && !opaque.contains(&l) {
                gaps.push((q, l));
            }
            hit
        };
        let dropping = |l: Local| drop_live[l as usize] || opaque.contains(&l);
        for (bi, b) in body.blocks.iter().enumerate() {
            let writes = |p: &Place| p.proj.is_empty() && dropping(p.local);
            if !b.stmts.iter().any(|s| matches!(&s.kind, StmtKind::Drop(l) if drop_live[*l as usize]) || matches!(&s.kind, StmtKind::Assign(d, _) if writes(d)))
                && !matches!(&b.term, Terminator::Call { dest, .. } if writes(dest))
            {
                continue;
            }
            let Some(e) = &entry[bi] else { continue };
            st.w.copy_from_slice(&e.w);
            for (si, s) in b.stmts.iter().enumerate() {
                let q = self.point_base[bi] + si;
                match &s.kind {
                    StmtKind::Drop(l) if drop_live[*l as usize] && bit_has(st.init(), *l as usize) => uses[q] = true,
                    StmtKind::Assign(dest, rv) => {
                        let mut ops: Vec<&Operand> = Vec::new();
                        rvalue_operands(rv, &mut |o| ops.push(o));
                        uses[q] |= overwrites(&st, q, dest, &ops);
                    }
                    _ => {}
                }
                self.stmt(bi as u32, si as u32, &s.kind, s.span, &mut st);
            }
            let q = self.point_base[bi] + b.stmts.len();
            if let Terminator::Call { args, dest, .. } = &b.term
                && overwrites(&st, q, dest, &args.iter().collect::<Vec<_>>())
            {
                uses[q] = true;
            }
        }
        self.drop_gap = gaps;
        if uses.iter().any(|&u| u) {
            self.drop_entry = self.backward(Some(&uses), Some(entry));
        }
    }

    /// True when loan `li`'s region contains point `q`: it reaches a
    /// universal region, or a local whose (drop-live) slots it reaches is
    /// (drop-)live at `q`'s entry.
    fn contains(&self, li: usize, q: usize) -> bool {
        self.contains_but(li, q, None)
    }

    /// `contains`, with local `skip` (when given) taken as dead at `q`.
    fn contains_but(&self, li: usize, q: usize, skip: Option<Local>) -> bool {
        let Some(sol) = &self.sol else { return false };
        if sol.univ[li] {
            return true;
        }
        let wn = self.sh.wn;
        let hit = |live: &[u64], set: &[u64]| {
            live.iter().zip(set).enumerate().any(|(w, (a, b))| {
                let m = match skip {
                    Some(l) if l as usize / 64 == w => !(1u64 << (l % 64)),
                    _ => !0,
                };
                a & b & m != 0
            })
        };
        if hit(&self.live_entry[q * wn..(q + 1) * wn], sol.use_set(li)) {
            return true;
        }
        !self.drop_entry.is_empty() && hit(&self.drop_entry[q * wn..(q + 1) * wn], sol.drop_set(li))
    }

    /// The block and index of point `q`.
    fn point_at(&self, q: usize) -> (usize, usize) {
        let b = self.point_base.partition_point(|&s| s <= q) - 1;
        (b, q - self.point_base[b])
    }

    /// True when the statement or terminator at `q` overwrites or ends the
    /// local loan `li` borrows from: the loan does not survive past it
    /// (rustc `kill_borrows_on_place`).
    fn kills(&self, li: usize, q: usize) -> bool {
        let local = self.loans[li].place.local;
        let (b, i) = self.point_at(q);
        let block = &self.body.blocks[b];
        match block.stmts.get(i) {
            Some(s) => match &s.kind {
                StmtKind::Assign(dest, _) => dest.proj.is_empty() && dest.local == local,
                StmtKind::StorageDead(l) => *l == local,
                _ => false,
            },
            None => matches!(&block.term, Terminator::Call { dest, .. } if dest.proj.is_empty() && dest.local == local),
        }
    }

    /// Loan scopes (NLL): from the point after each borrow, every point
    /// reachable through points its region contains, stopping after a
    /// point that kills it.
    fn loan_scopes(&mut self) {
        let np = self.point_base[self.body.blocks.len()];
        let wl = self.wl;
        let mut scope = vec![0u64; np * wl];
        let mut stamp = vec![u32::MAX; np];
        let mut stack: Vec<usize> = Vec::new();
        for li in 0..self.loans.len() {
            let (lb, ls) = (self.loan_block[li] as usize, self.loan_stmt[li] as usize);
            stack.clear();
            stack.push(self.point_base[lb] + ls + 1);
            while let Some(q) = stack.pop() {
                if stamp[q] == li as u32 {
                    continue;
                }
                stamp[q] = li as u32;
                if !self.contains(li, q) {
                    continue;
                }
                bit_set(&mut scope[q * wl..(q + 1) * wl], li);
                if self.kills(li, q) {
                    continue;
                }
                // A loan only the dropped old value held ends at the drop.
                if let Ok(g) = self.drop_gap.binary_search_by_key(&q, |g| g.0)
                    && !self.contains_but(li, q, Some(self.drop_gap[g].1))
                {
                    continue;
                }
                let (b, i) = self.point_at(q);
                if i < self.body.blocks[b].stmts.len() {
                    stack.push(q + 1);
                } else {
                    for s in &self.succs[b] {
                        stack.push(self.point_base[s.0 as usize]);
                    }
                }
            }
        }
        self.scope = scope;
    }

    /// True when loan `li` is still needed after the statement or
    /// terminator at `q`: its region contains a following point.
    fn needed_after(&self, li: usize, q: usize) -> bool {
        let (b, i) = self.point_at(q);
        if i < self.body.blocks[b].stmts.len() {
            return self.contains(li, q + 1);
        }
        self.succs[b].iter().any(|s| self.contains(li, self.point_base[s.0 as usize]))
    }

    /// True when local `l`'s slots are reached by loan `li`'s region.
    fn carries(&self, li: usize, l: Local) -> bool {
        (l as usize) < self.n_locals() && self.sol.as_ref().is_some_and(|sol| bit_has(sol.use_set(li), l as usize))
    }

    /// The loans an access at point `q` conflicts with, when in scope: those
    /// needed after `q`, and those a sibling operand of the same statement
    /// still carries. Lust's IR reads a statement's operands in order and
    /// then writes, where MIR uses a temporary per operand: a later operand
    /// keeps its local's loans in scope (rustc E0503 on `x + *m`), and an
    /// earlier operand whose value holds regions keeps them until the
    /// statement completes. The accessed operand's own root counts too: its
    /// use keeps its regions live here, so a loan of itself that it carries
    /// (`tie(&'a mut N<'a>)`, then `take(d)`: rustc E0505) is in scope at its
    /// last use. `j` is the access's operand index (`None` for the final
    /// write); `carriers` are (root local, value holds regions) per operand,
    /// in order.
    fn live_for(&self, q: usize, j: Option<usize>, carriers: &[(Local, bool)]) -> BitSet {
        let mut out = BitSet::new(self.loans.len());
        if !self.report || self.loans.is_empty() || self.scope.is_empty() {
            return out;
        }
        let wl = self.wl;
        for li in bit_iter(&self.scope[q * wl..(q + 1) * wl]) {
            let sibling = carriers.iter().enumerate().any(|(i, &(root, regions))| {
                (Some(i) == j || regions || j.is_some_and(|j| i > j)) && self.carries(li, root)
            });
            if sibling || self.needed_after(li, q) {
                out.insert(li);
            }
        }
        out
    }

    /// Adds to `live` the loans in scope at `Drop(l)` (point `q`) that `l`'s
    /// own destructor holds: their region reaches `l`'s drop-live slots, so
    /// the drop uses them. A loan of `l` among them conflicts with the drop
    /// (rustc E0597 on `let r = tie(&mut d);` with `d: D<'a>`, `D: Drop`, and
    /// `tie(&'a mut D<'a>)`), though no later point needs it.
    fn drop_held(&self, q: usize, l: Local, live: &mut BitSet) {
        let Some(sol) = &self.sol else { return };
        if !self.report || self.scope.is_empty() || !sol.drop_live.get(l as usize).is_some_and(|&d| d) {
            return;
        }
        let wl = self.wl;
        for li in bit_iter(&self.scope[q * wl..(q + 1) * wl]) {
            if bit_has(sol.drop_set(li), l as usize) {
                live.insert(li);
            }
        }
    }

    /// The carriers of a statement's operands for `live_for`: each operand's
    /// root local and whether its value holds regions, then the destination's
    /// root when the write goes through a projection of a user variable (it
    /// is read last). A temporary root was made for this assignment's place,
    /// which Rust evaluates after the value (`v[0] = v[1]` borrows `v`
    /// mutably only after reading `v[1]`), so it does not count.
    fn carriers(&self, ops: &[&Operand], dest: Option<&Place>) -> Vec<(Local, bool)> {
        let mut out: Vec<(Local, bool)> = Vec::with_capacity(ops.len() + 1);
        for o in ops {
            match o {
                Operand::Copy(p) | Operand::Move(p) => out.push((p.local, self.has_regions(self.value_ty(p)))),
                Operand::Const(_) => out.push((u32::MAX, false)),
            }
        }
        if let Some(d) = dest
            && !d.proj.is_empty()
            && self.body.locals[d.local as usize].name.is_some()
        {
            out.push((d.local, false));
        }
        out
    }

    /// The type of the value at a place (`ERROR` when a step is unknown).
    fn value_ty(&self, p: &Place) -> Ty {
        let tys = &self.body.tys;
        let mut t = self.body.locals[p.local as usize].ty;
        let mut variant = 0;
        for pr in &p.proj {
            t = match *pr {
                Proj::Deref => match tys.kind(t) {
                    TyKind::Ref(_, _, i) => i,
                    _ => tys.adt_first_ty_arg(t).unwrap_or(ERROR),
                },
                Proj::Field(i) => {
                    let f = self.step_field_ty(t, variant, i);
                    variant = 0;
                    f
                }
                Proj::Downcast(v) => {
                    variant = v;
                    t
                }
                Proj::Index(_) => match tys.kind(t) {
                    TyKind::Array(e, _) | TyKind::Slice(e) => e,
                    _ => tys.vec_elem(t).unwrap_or(ERROR),
                },
            };
            if t == ERROR {
                return ERROR;
            }
        }
        t
    }

    /// True when a place goes through a dereference of a reference or raw
    /// pointer: the value it names is not owned by its root local, so it
    /// outlives the local's storage. A deref of a `Box` (or another owning
    /// pointer) stays inside the local: dropping the local frees it. A bare
    /// slice or `str` local is the fat pointer of a subslice (`v[1..]`):
    /// every place in it is behind that pointer.
    fn through_ref(&self, p: &Place) -> bool {
        let tys = &self.body.tys;
        let mut t = self.body.locals[p.local as usize].ty;
        if matches!(tys.kind(t), TyKind::Slice(_) | TyKind::Str) {
            return true;
        }
        let mut variant = 0;
        for pr in &p.proj {
            t = match *pr {
                Proj::Deref => match tys.kind(t) {
                    TyKind::Ref(..) | TyKind::RawPtr(..) => return true,
                    _ => tys.adt_first_ty_arg(t).unwrap_or(ERROR),
                },
                Proj::Field(i) => {
                    let f = self.step_field_ty(t, variant, i);
                    variant = 0;
                    f
                }
                Proj::Downcast(v) => {
                    variant = v;
                    t
                }
                Proj::Index(_) => match tys.kind(t) {
                    TyKind::Array(e, _) | TyKind::Slice(e) => e,
                    _ => tys.vec_elem(t).unwrap_or(ERROR),
                },
            };
            if t == ERROR {
                // Unknown below here: a deref in the rest still means the
                // value may live elsewhere (the old rule).
                return p.proj.contains(&Proj::Deref);
            }
        }
        false
    }

    /// True when `p` is reached through a deref of a shared reference or
    /// a raw pointer: a loan of such a place conflicts with nothing
    /// (rustc `ignore_borrow`; the reference is `Copy`, its referent
    /// cannot change, and region constraints keep the referent alive).
    /// An unknown type on the way counts as no such deref.
    fn through_shared_ref(&self, p: &Place) -> bool {
        let tys = &self.body.tys;
        let mut t = self.body.locals[p.local as usize].ty;
        let mut variant = 0;
        for pr in &p.proj {
            t = match *pr {
                Proj::Deref => match tys.kind(t) {
                    TyKind::Ref(_, Mut::Shared, _) | TyKind::RawPtr(..) => return true,
                    TyKind::Ref(_, Mut::Mut, inner) => inner,
                    _ => tys.adt_first_ty_arg(t).unwrap_or(ERROR),
                },
                Proj::Field(i) => {
                    let f = match (tys.option_elem(t), tys.result_args(t)) {
                        (Some(e), _) => e,
                        (_, Some((a, b))) => if variant == 0 { a } else { b },
                        _ => self.step_field_ty(t, variant, i),
                    };
                    variant = 0;
                    f
                }
                Proj::Downcast(v) => {
                    variant = v;
                    t
                }
                Proj::Index(_) => match tys.kind(t) {
                    TyKind::Array(e, _) | TyKind::Slice(e) => e,
                    _ => tys.vec_elem(t).unwrap_or(ERROR),
                },
            };
            if t == ERROR {
                return false;
            }
        }
        false
    }

    /// True when a type has region slots (unknown types count).
    fn has_regions(&self, t: Ty) -> bool {
        let tys = &self.body.tys;
        match tys.kind(t) {
            TyKind::Error | TyKind::Ref(..) => true,
            TyKind::Adt(_, a) => tys.is_chars_ty(t) || tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| self.has_regions(e))),
            TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| self.has_regions(e)),
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.has_regions(e),
            TyKind::Closure(_, a) => closure_fields(tys, a).iter().any(|&e| self.has_regions(e)),
            _ => false,
        }
    }

    // ---------- Forward dataflow and checks ----------

    fn entry_state(&self) -> State {
        let n = self.n_locals();
        let mut st = State::new(self.sh);
        for l in 0..n {
            if l >= 1 && l <= self.body.arg_count {
                bit_set(st.init_mut(), l);
                bit_set(st.ever_mut(), l);
            } else {
                bit_set(st.uninit_mut(), l);
            }
        }
        st
    }

    /// The blocks reachable from the entry, in reverse postorder: every
    /// block comes after all its predecessors except along back edges.
    fn reverse_postorder(&self) -> Vec<u32> {
        let nb = self.body.blocks.len();
        let mut seen = vec![false; nb];
        let mut post = Vec::with_capacity(nb);
        // (block, next successor index), an explicit DFS stack.
        let mut stack: Vec<(u32, usize)> = vec![(0, 0)];
        seen[0] = true;
        while let Some(top) = stack.last_mut() {
            let (b, k) = *top;
            match self.succs[b as usize].get(k) {
                Some(s) => {
                    top.1 += 1;
                    if !seen[s.0 as usize] {
                        seen[s.0 as usize] = true;
                        stack.push((s.0, 0));
                    }
                }
                None => {
                    post.push(b);
                    stack.pop();
                }
            }
        }
        post.reverse();
        post
    }

    /// The init dataflow to its fixpoint, without reporting: the entry state
    /// of each reachable block.
    fn init_fixpoint(&mut self) -> Vec<Option<State>> {
        let nb = self.body.blocks.len();
        let mut entry: Vec<Option<State>> = vec![None; nb];
        entry[0] = Some(self.entry_state());
        // Visit pending blocks in reverse postorder, in rounds: a block's
        // predecessors (back edges aside) run before it in the same round,
        // so most blocks run once and only loops take another round. The
        // fixpoint is the same in any visit order. `st` is the one scratch
        // state: each visit copies a block's entry state into it.
        let rpo = self.reverse_postorder();
        let mut pending = vec![false; nb];
        pending[0] = true;
        let mut st = State::new(self.sh);
        while pending.contains(&true) {
            for &b in &rpo {
                if !pending[b as usize] {
                    continue;
                }
                pending[b as usize] = false;
                st.w.copy_from_slice(&entry[b as usize].as_ref().unwrap().w);
                self.run_block(b, &mut st);
                for k in 0..self.succs[b as usize].len() {
                    let s = self.succs[b as usize][k];
                    let si = s.0 as usize;
                    let changed = match &mut entry[si] {
                        None => {
                            entry[si] = Some(st.clone());
                            true
                        }
                        Some(e) => e.join(&st),
                    };
                    // A successor later in the order runs in this round; one at
                    // or before `b` (a back edge) runs in the next.
                    pending[si] |= changed;
                }
            }
        }
        entry
    }

    /// One reporting pass over the final states of the init fixpoint.
    fn report_pass(&mut self, entry: &[Option<State>]) {
        self.report = true;
        let mut st = State::new(self.sh);
        for (b, e) in entry.iter().enumerate() {
            if let Some(e) = e {
                st.w.copy_from_slice(&e.w);
                self.run_block(b as u32, &mut st);
            }
        }
    }

    fn run_block(&mut self, b: u32, st: &mut State) {
        let body = self.body;
        let block = &body.blocks[b as usize];
        for (si, s) in block.stmts.iter().enumerate() {
            self.stmt(b, si as u32, &s.kind, s.span, st);
        }
        let span = block.term_span;
        let q = self.point_base[b as usize] + block.stmts.len();
        let mut ops: Vec<&Operand> = Vec::new();
        match &block.term {
            Terminator::Call { target, args, dest, .. } => self.call_term(b, *target, args, dest, span, st),
            Terminator::If(o, ..) | Terminator::Switch(o, ..) => ops.push(o),
            Terminator::Panic(parts) => parts_operands(parts, &mut |o| ops.push(o)),
            Terminator::Return if self.report => self.check_return(q, span),
            _ => {}
        }
        let carriers = if self.report { self.carriers(&ops, None) } else { Vec::new() };
        for (j, o) in ops.iter().enumerate() {
            let live = self.live_for(q, Some(j), &carriers);
            self.operand(o, span, st, &live);
        }
    }

    fn stmt(&mut self, b: u32, si: u32, s: &'b StmtKind, span: Span, st: &mut State) {
        let q = self.point_base[b as usize] + si as usize;
        match s {
            StmtKind::Assign(dest, rv) => {
                // Reads and moves in the right-hand side, in order.
                let mut ops = std::mem::take(&mut self.ops_buf);
                ops.clear();
                rvalue_operands(rv, &mut |o| ops.push(o));
                let carriers = if self.report { self.carriers(&ops, Some(dest)) } else { Vec::new() };
                for (j, o) in ops.iter().enumerate() {
                    let live = self.live_for(q, Some(j), &carriers);
                    self.operand(o, span, st, &live);
                }
                let borrow = match rv {
                    Rvalue::Ref(m, place) => Some((*m, place)),
                    Rvalue::SliceOf(place) => Some((self.slice_dest_mut(dest), place)),
                    Rvalue::Subslice { base, mutable, .. } => Some((*mutable, base)),
                    _ => None,
                };
                if let Some((m, place)) = borrow {
                    self.check_init(place, span, st);
                    let kind = if m { Access::BorrowMut } else { Access::BorrowShared };
                    if m {
                        self.check_mutability(place, span, st, true);
                    }
                    let live = match self.activation_live(b, si, rv) {
                        Some(live) => live,
                        None => self.live_for(q, Some(ops.len()), &carriers),
                    };
                    let p_range = match rv {
                        Rvalue::Subslice { lo, hi, inclusive, .. } => self.subslice_range(dest, lo, hi, *inclusive),
                        _ => None,
                    };
                    self.access(place, kind, span, &live, p_range);
                } else if let Rvalue::Discriminant(place) | Rvalue::LenOf(place) = rv {
                    self.check_init(place, span, st);
                    let live = self.live_for(q, Some(ops.len()), &carriers);
                    self.access(place, Access::Read, span, &live, None);
                }
                let live = self.live_for(q, None, &carriers);
                self.write_dest(dest, span, &live, st);
                self.ops_buf = ops;
            }
            StmtKind::Drop(l) | StmtKind::StorageDead(l) => {
                let place = Place::local(*l);
                let mut live = self.live_for(q, None, &[]);
                if matches!(s, StmtKind::Drop(_)) {
                    self.drop_held(q, *l, &mut live);
                }
                self.access(&place, Access::Dead, span, &live, None);
                let li = *l as usize;
                bit_unset(st.init_mut(), li);
                bit_set(st.uninit_mut(), li);
                if matches!(s, StmtKind::StorageDead(_)) {
                    self.clear_paths(st, li);
                    bit_unset(st.ever_mut(), li);
                }
            }
            // A use for liveness only, as rustc's `FakeRead` and
            // `PlaceMention`: it keeps a two-phase reservation, a `let`
            // binding, or a mentioned place live here, and it reads no
            // memory, so it checks no conflicts (`let _ = x;` while `x` is
            // mutably borrowed is fine).
            StmtKind::FakeRead(_) => {}
            StmtKind::Print { parts, .. } => {
                let mut ops: Vec<&Operand> = Vec::new();
                parts_operands(parts, &mut |o| ops.push(o));
                let carriers = if self.report { self.carriers(&ops, None) } else { Vec::new() };
                for (j, o) in ops.iter().enumerate() {
                    let live = self.live_for(q, Some(j), &carriers);
                    self.operand(o, span, st, &live);
                }
            }
        }
    }

    /// The write side of an assignment or a call's result store: mutability,
    /// conflicts with in-scope loans, and init state.
    fn write_dest(&mut self, dest: &Place, span: Span, live: &BitSet, st: &mut State) {
        if dest.proj.is_empty() {
            let l = dest.local as usize;
            // Rust checks ever-initialized here: a value moved out still
            // counts (`let a = s; drop(a); a = t;` is E0384).
            if !self.body.locals[l].mutable && bit_has(st.ever(), l) {
                let name = self.local_name(dest.local);
                self.err("L0302", span, format!("cannot assign twice to immutable variable {name}"), "Declare it with `let mut`.");
            }
            self.access(dest, Access::Write, span, live, None);
            bit_set(st.init_mut(), l);
            bit_set(st.ever_mut(), l);
            bit_unset(st.uninit_mut(), l);
            bit_unset(st.moved_mut(), l);
            self.clear_paths(st, l);
        } else {
            self.check_init_write(dest, span, st);
            self.check_mutability(dest, span, st, false);
            self.access(dest, Access::Write, span, live, None);
            // Writing a field puts back a field that was moved out, and every
            // field below it. Other moved fields stay moved.
            let l = dest.local as usize;
            if self.mpath_range(l).any(|i| bit_has(st.paths(), i)) {
                let (path, exact) = self.prefix_of(dest);
                if exact {
                    for i in self.mpath_range(l) {
                        if is_prefix(&path, &self.mpaths[i].1) {
                            bit_unset(st.paths_mut(), i);
                        }
                    }
                }
            }
        }
    }

    /// One `Call` terminator, checked like the assignment it ends: argument
    /// reads in order, then the write to `dest` after the call (as MIR
    /// writes a call's destination on its return edge). Loan flow through
    /// calls is in the region constraints (regions.rs).
    fn call_term(&mut self, b: u32, target: CallTarget, args: &[Operand], dest: &Place, span: Span, st: &mut State) {
        let q = self.point_base[b as usize] + self.body.blocks[b as usize].stmts.len();
        let mut ops: Vec<&Operand> = args.iter().collect();
        let callee_op;
        if let CallTarget::Indirect(callee) = target {
            callee_op = Operand::Copy(Place::local(callee));
            ops.insert(0, &callee_op);
        }
        let carriers = if self.report { self.carriers(&ops, Some(dest)) } else { Vec::new() };
        // Two-phase receivers and arguments (each lowered as reservation,
        // arguments, `FakeRead`, then `&mut`) are activated by the call
        // itself: the other arguments are read before them in Rust, so
        // their own loans act as shared borrows for them. Loans they
        // reborrow through (`r.push(v[0])` with `r = &mut v`) stay as they
        // are.
        let base = self.stmt_base[b as usize];
        self.reserved = self.two_phase_loans(b, args).into_iter().map(|k| self.loan_at[base + k] as usize).filter(|&li| li < self.loans.len()).collect();
        for (j, o) in ops.iter().enumerate() {
            let live = self.live_for(q, Some(j), &carriers);
            self.operand(o, span, st, &live);
        }
        self.reserved.clear();
        let live = self.live_for(q, None, &[]);
        self.write_dest(dest, span, &live, st);
    }

    /// The loans a two-phase activation (`&mut` statement `si` of block
    /// `b`, one of `two_phase_loans` of the call ending it) conflicts
    /// with: those live after the call, and those the call's operands
    /// carry in values that hold regions. The call's other operands are
    /// read before the activation in Rust (into temporaries in MIR), so
    /// a loan only they read (`self.walk(*c)` with `c = &self.v`) is no
    /// conflict; a reference operand that carries it (`self.walk2(c)`)
    /// is (rustc E0502). None for any other statement.
    fn activation_live(&self, b: u32, si: u32, rv: &Rvalue) -> Option<BitSet> {
        if !self.report || !matches!(rv, Rvalue::Ref(true, _)) {
            return None;
        }
        let block = &self.body.blocks[b as usize];
        let Terminator::Call { target, args, .. } = &block.term else { return None };
        let activations = self.two_phase_loans(b, args);
        if !activations.contains(&(si as usize)) {
            return None;
        }
        let mut ops: Vec<&Operand> = args.iter().collect();
        let callee_op;
        if let CallTarget::Indirect(callee) = target {
            callee_op = Operand::Copy(Place::local(*callee));
            ops.insert(0, &callee_op);
        }
        let carriers = self.carriers(&ops, None);
        let q = self.point_base[b as usize] + block.stmts.len();
        let mut live = self.live_for(q, None, &carriers);
        // The call's own activations are in scope at the call, this one
        // included: no conflict with themselves.
        let base = self.stmt_base[b as usize];
        for k in activations {
            let li = self.loan_at[base + k] as usize;
            if li < self.loans.len() {
                live.remove(li);
            }
        }
        Some(live)
    }

    /// The statement indexes (in block `b`) of the two-phase `&mut`
    /// receiver and arguments of the call ending `b` (lower.rs
    /// `call_arg_operands`): the block ends with pairs of a `FakeRead` of
    /// the reservation, an unnamed shared borrow of the same place made
    /// earlier (a `let` binding's `FakeRead` is not one), and the `&mut`
    /// of a temporary that an argument moves.
    fn two_phase_loans(&self, b: u32, args: &[Operand]) -> Vec<usize> {
        let stmts = &self.body.blocks[b as usize].stmts;
        let mut out = Vec::new();
        let mut k = stmts.len();
        while k >= 2 {
            let (StmtKind::FakeRead(r), StmtKind::Assign(t, Rvalue::Ref(true, place))) = (&stmts[k - 2].kind, &stmts[k - 1].kind) else { break };
            let moved = args.iter().any(|a| matches!(a, Operand::Move(a) if a.proj.is_empty() && a.local == t.local));
            if !t.proj.is_empty() || !moved || self.body.locals[*r as usize].name.is_some() {
                break;
            }
            // The reservation is made before the arguments run, so it is in
            // this block or (after an argument's call) an earlier one.
            let reserved = (0..=b as usize).rev().any(|bi| {
                self.body.blocks[bi].stmts.iter().rev().any(|s| {
                    matches!(&s.kind, StmtKind::Assign(d, Rvalue::Ref(false, p)) if d.proj.is_empty() && d.local == *r && p == place)
                })
            });
            if !reserved {
                break;
            }
            out.push(k - 1);
            k -= 2;
        }
        out
    }

    /// True when a slice-making assignment's destination is a `&mut [T]` local.
    fn slice_dest_mut(&self, dest: &Place) -> bool {
        dest.proj.is_empty() && matches!(self.body.tys.kind(self.body.locals[dest.local as usize].ty), TyKind::Ref(_, Mut::Mut, _))
    }

    /// The known position of an index or bound operand: a
    /// constant, a pattern constant index local, or a pattern
    /// back-index local.
    fn idx_key(&self, o: &Operand) -> Option<IdxKey> {
        match o {
            Operand::Const(Const::Int(v, _)) if *v <= u64::MAX as u128 => Some(IdxKey::Front(*v as u64)),
            Operand::Copy(p) | Operand::Move(p) if p.proj.is_empty() => {
                if let Some(&c) = self.const_index.get(&p.local) {
                    Some(IdxKey::Front(c))
                } else {
                    self.back_index.get(&p.local).map(|&(k, _)| IdxKey::Back(k))
                }
            }
            _ => None,
        }
    }

    /// The index range of a pattern-created subslice whose
    /// result lands in `dest` (`Body::pat_subslice`), when both
    /// bounds have known positions.
    fn subslice_range(&self, dest: &Place, lo: &Operand, hi: &Option<Operand>, inclusive: bool) -> Option<(IdxKey, IdxKey)> {
        if !dest.proj.is_empty() || !self.body.pat_subslice.contains(&dest.local) {
            return None;
        }
        let lo = self.idx_key(lo)?;
        let hi = match hi {
            None => IdxKey::Back(0),
            Some(o) => match (self.idx_key(o)?, inclusive) {
                (IdxKey::Front(v), true) => IdxKey::Front(v.checked_add(1)?),
                (k, false) => k,
                _ => return None,
            },
        };
        Some((lo, hi))
    }

    /// True when an access to place `p` (with subslice range
    /// `p_range` when the access creates one) may touch the
    /// memory of `loan`: `overlap`, plus the disjointness of a
    /// pattern subslice range and the pattern element places
    /// outside it.
    fn overlaps(&self, p: &Place, p_range: Option<(IdxKey, IdxKey)>, loan: &Loan) -> bool {
        if p.local == loan.place.local {
            // An element place just below a ranged loan's place.
            if let Some((lo, hi)) = loan.range
                && p.proj.len() > loan.place.proj.len()
                && p.proj[..loan.place.proj.len()] == loan.place.proj[..]
                && let Proj::Index(l) = p.proj[loan.place.proj.len()]
                && let Some(k) = self.idx_key(&Operand::Copy(Place::local(l)))
                && idx_outside(k, lo, hi)
            {
                return false;
            }
            // A ranged access against an element loan below it.
            if let Some((lo, hi)) = p_range
                && loan.place.proj.len() > p.proj.len()
                && loan.place.proj[..p.proj.len()] == p.proj[..]
                && let Proj::Index(l) = loan.place.proj[p.proj.len()]
                && let Some(k) = self.idx_key(&Operand::Copy(Place::local(l)))
                && idx_outside(k, lo, hi)
            {
                return false;
            }
            // Two ranged subslices of one place.
            if let (Some(a), Some(b)) = (p_range, loan.range)
                && p.proj == loan.place.proj
                && (idx_le(a.1, b.0) == Some(true) || idx_le(b.1, a.0) == Some(true))
            {
                return false;
            }
        }
        overlap(p, &loan.place, &self.const_index, &self.front_index, &self.back_index)
    }

    /// The type one `Field` projection down from `t` (in the variant a
    /// preceding `Downcast` selected), or the error type when unknown.
    fn step_field_ty(&self, t: Ty, variant: u32, i: u32) -> Ty {
        match self.body.tys.kind(t) {
            TyKind::Tuple(ts) => self.body.tys.tys_of(ts).get(i as usize).copied().unwrap_or(ERROR),
            TyKind::Adt(..) => match self.body.tys.local_adt(t) {
                Some(a) => self
                    .p
                    .adt(a)
                    .variants
                    .get(variant as usize)
                    .and_then(|v| v.fields.get(i as usize))
                    .map(|f| f.ty)
                    .unwrap_or(ERROR),
                None => ERROR,
            },
            _ if self.body.tys.option_elem(t).is_some() => self.body.tys.option_elem(t).unwrap(),
            _ => ERROR,
        }
    }

    /// The leading exact part of a place as an encoded path, and whether
    /// that is the whole place. Fields, downcasts, constant indexes
    /// into arrays, and a deref through a `Box` are exact; any other
    /// dereference or index is not, and the prefix still identifies
    /// the field the place reaches into.
    /// Encodings sit in the low two bits: 0 field, 1 downcast, 2 index,
    /// 3 box deref.
    fn prefix_of(&self, p: &Place) -> (Path, bool) {
        let mut path = Vec::new();
        let mut t = self.body.locals[p.local as usize].ty;
        let mut variant = 0u32;
        for pr in &p.proj {
            match pr {
                Proj::Field(i) => {
                    path.push((*i as u64) << 2);
                    t = self.step_field_ty(t, variant, *i);
                    variant = 0;
                }
                Proj::Downcast(v) => {
                    path.push(((*v as u64) << 2) | 1);
                    variant = *v;
                }
                Proj::Index(l) => match self.body.tys.kind(t) {
                    TyKind::Array(e, _) => match self.const_index.get(l) {
                        Some(&c) if c < (1 << 60) => {
                            path.push((c << 2) | 2);
                            t = e;
                        }
                        _ => return (path, false),
                    },
                    _ => return (path, false),
                },
                Proj::Deref => match self.body.tys.boxed_elem(t) {
                    // Moving out of a `Box` is legal in Rust and
                    // exact: the box owns its pointee outright.
                    Some(e) => {
                        path.push(3);
                        t = e;
                        variant = 0;
                    }
                    None => return (path, false),
                },
            }
        }
        (path, true)
    }

    fn operand(&mut self, o: &Operand, span: Span, st: &mut State, live: &BitSet) {
        match o {
            Operand::Copy(p) => {
                self.check_init(p, span, st);
                self.access(p, Access::Read, span, live, None);
            }
            Operand::Move(p) => {
                self.check_init(p, span, st);
                self.access(p, Access::Move, span, live, None);
                // A move out of a local, or out of one of its fields. Moving one field is a
                // partial move: sibling fields stay usable, but the moved field and every
                // value that contains it do not, until the field is assigned again. Rust
                // also forbids partial moves out of a type with a `Drop` impl (E0509);
                // `check_partial_move` enforces that. Codegen drops only the parts a
                // partially moved local still owns (`cgen::FnGen::elab_drop`).
                let (path, exact) = self.prefix_of(p);
                if exact && !path.is_empty() {
                    self.check_partial_move(p, span);
                }
                // `collect_move_paths` gave every exact moved place an entry.
                let l = p.local as usize;
                match if exact { self.mpath_index(l, &path) } else { None } {
                    Some(id) => {
                        if path.is_empty() {
                            bit_unset(st.init_mut(), l);
                            bit_set(st.uninit_mut(), l);
                            bit_set(st.moved_mut(), l);
                            self.clear_paths(st, l);
                        }
                        bit_set(st.paths_mut(), id);
                    }
                    None => self.bad_move(p, span, st),
                }
            }
            Operand::Const(_) => {}
        }
    }

    /// Follows a `Param(i)` head through `env` (the type arguments of
    /// the Adt application the type was read from). An unresolvable
    /// param stays a param: it is a generic of the enclosing fn, whose
    /// drop behavior is unknown here.
    fn head_resolve(&self, mut t: Ty, env: &[Ty]) -> Ty {
        while let TyKind::Param(p) = self.body.tys.kind(t) {
            match env.get(p.0 as usize) {
                Some(&next) if next != t => t = next,
                _ => break,
            }
        }
        t
    }

    /// The type arguments of an Adt application, head-resolved through
    /// `env`, as the env for reading that Adt's field types.
    fn adt_env(&self, t: Ty, env: &[Ty]) -> Vec<Ty> {
        match self.body.tys.adt_parts(t) {
            Some((_, args)) => self.body.tys.args(args).iter().map(|g| self.head_resolve(g.as_ty().unwrap_or(ERROR), env)).collect(),
            None => Vec::new(),
        }
    }

    /// Rust's E0509 on an exact field path: no field moves out of a
    /// type with a `Drop` impl, at any step of the path. Copy fields
    /// are exempt: copying out is legal even from a `Drop` type.
    fn check_partial_move(&mut self, p: &Place, span: Span) {
        if !self.report {
            return;
        }
        let mut cur = self.body.locals[p.local as usize].ty;
        let mut env: Vec<Ty> = Vec::new();
        let mut variant = 0u32;
        let mut drop_container: Option<Ty> = None;
        for pr in &p.proj {
            match pr {
                Proj::Downcast(v) => variant = *v,
                Proj::Field(i) => {
                    let container = self.head_resolve(cur, &env);
                    if let Some((def, _)) = self.body.tys.adt_parts(container) {
                        if self.drop_heads.contains(&def) && self.body.tys.local_adt(container).is_some() {
                            drop_container = Some(container);
                        }
                    }
                    let next = match self.body.tys.kind(container) {
                        TyKind::Tuple(ts) => self.body.tys.tys_of(ts).get(*i as usize).copied().unwrap_or(ERROR),
                        TyKind::Adt(..) if self.body.tys.option_elem(container).is_some() => {
                            self.body.tys.option_elem(container).unwrap_or(ERROR)
                        }
                        TyKind::Adt(..) if self.body.tys.result_args(container).is_some() => {
                            let (a, b) = self.body.tys.result_args(container).unwrap();
                            if variant == 0 { a } else { b }
                        }
                        TyKind::Adt(..) => match self.body.tys.local_adt(container) {
                            Some(a) => {
                                let f = self.p.adt(a).variants.get(variant as usize).and_then(|v| v.fields.get(*i as usize));
                                match f {
                                    Some(f) => {
                                        let ty = f.ty;
                                        env = self.adt_env(container, &env);
                                        ty
                                    }
                                    None => ERROR,
                                }
                            }
                            None => ERROR,
                        },
                        _ => ERROR,
                    };
                    if next == ERROR {
                        return;
                    }
                    cur = next;
                    variant = 0;
                }
                Proj::Index(_) => {
                    // A constant index into an array is a partial move
                    // like a field; an array has no `Drop` impl of its own.
                    let container = self.head_resolve(cur, &env);
                    match self.body.tys.kind(container) {
                        TyKind::Array(e, _) => cur = e,
                        _ => return,
                    }
                }
                Proj::Deref => {
                    // Through a `Box`: the box itself is the one
                    // container a move may cross despite its Drop
                    // impl; the pointee's own Drop still counts
                    // for the field steps that follow.
                    let container = self.head_resolve(cur, &env);
                    match self.body.tys.boxed_elem(container) {
                        Some(e) => {
                            cur = e;
                            variant = 0;
                        }
                        None => return,
                    }
                }
            }
        }
        let moved = self.head_resolve(cur, &env);
        if is_copy(self.p, &self.body.tys, moved) {
            return;
        }
        // A generic field is a move unless the bounds make it Copy:
        // the template check's body store carries its param env, so
        // `is_copy` above answers a param from its bounds.
        if let Some(container) = drop_container {
            self.err(
                "L0305",
                span,
                format!("cannot move out of {}, because it implements `Drop`", ty_name(self.p, &self.body.tys, container)),
                "Borrow the field with `&`, clone it, or use `std::mem::replace` (not yet supported) style code.",
            );
        }
    }

    /// The container type at the first `Index` step of `place`, when
    /// it indexes an array, a slice, or a `Vec`. Field and deref
    /// steps before the index step through their types.
    fn index_container_ty(&self, place: &Place) -> Option<Ty> {
        let mut t = self.body.locals[place.local as usize].ty;
        let mut variant = 0;
        for pr in &place.proj {
            match pr {
                Proj::Field(i) => {
                    t = self.step_field_ty(t, variant, *i);
                    variant = 0;
                }
                Proj::Downcast(v) => variant = *v,
                Proj::Deref => {
                    if let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
                        t = inner;
                    }
                }
                Proj::Index(_) => {
                    return match self.body.tys.kind(t) {
                        TyKind::Array(..) | TyKind::Slice(_) => Some(t),
                        _ if self.body.tys.vec_elem(t).is_some() => Some(t),
                        _ => None,
                    };
                }
            }
        }
        None
    }

    /// The diagnostic for a move out of an index read, in rustc's
    /// text classes (E0508 for an array or slice, E0507 for a
    /// `Vec`): a direct `Index` place, or the synthetic borrow
    /// temporary lowering routes a non-Copy index read through
    /// (`lower::operand_raw`), whose loan still names the indexed
    /// place. A named reference local keeps the plain reference
    /// text instead, as in rustc (`let x = *r;` is E0507 behind a
    /// reference, not E0508).
    fn index_move_diag(&self, p: &Place, st: &State) -> Option<(String, &'static str)> {
        let container = self.index_container_ty(p).or_else(|| {
            if self.body.locals[p.local as usize].name.is_some() {
                return None;
            }
            let _ = st;
            self.loans.iter().filter(|l| l.holder == Some(p.local)).find_map(|l| self.index_container_ty(&l.place))
        })?;
        let name = self.container_name(container);
        Some(match self.body.tys.kind(container) {
            TyKind::Array(..) => (
                format!("cannot move out of type `{name}`, a non-copy array"),
                "Borrow the element with `&a[i]`, clone it, or move it out with an array pattern such as `let [x, ..] = a;`.",
            ),
            TyKind::Slice(_) => (
                format!("cannot move out of type `{name}`, a non-copy slice"),
                "Borrow the element with `&s[i]`, or clone it with `s[i].clone()`.",
            ),
            _ => (format!("cannot move out of index of `{name}`"), "Borrow the element with `&v[i]`, or clone it with `v[i].clone()`."),
        })
    }

    /// A container type name for `index_move_diag`: like
    /// `ty_name`, but an array length prints its value when the
    /// body knows it (the shared printer shows `_` today).
    fn container_name(&self, t: Ty) -> String {
        match self.body.tys.kind(t) {
            TyKind::Array(e, c) => match self.body.tys.const_kind(c) {
                ConstKind::Int(n) => format!("[{}; {}]", self.container_name(e), n),
                _ => ty_name(self.p, &self.body.tys, t),
            },
            TyKind::Slice(e) => format!("[{}]", self.container_name(e)),
            _ => ty_name(self.p, &self.body.tys, t),
        }
    }

    fn bad_move(&mut self, p: &Place, span: Span, st: &State) {
        if let Some((msg, fix)) = self.index_move_diag(p, st) {
            self.err("L0305", span, msg, fix);
        } else if p.proj.contains(&Proj::Deref) {
            self.err(
                "L0305",
                span,
                "cannot move out of a reference".into(),
                "Clone the value with `.clone()`, or borrow it with `&` instead of moving it.",
            );
        } else if p.proj.iter().any(|x| matches!(x, Proj::Index(_))) {
            // Name the indexed thing: a Vec's elements sit behind its
            // buffer, an array or slice index with a variable index
            // cannot name one element either.
            let mut t = self.body.locals[p.local as usize].ty;
            let mut variant = 0;
            for pr in &p.proj {
                match pr {
                    Proj::Field(i) => {
                        t = self.step_field_ty(t, variant, *i);
                        variant = 0;
                    }
                    Proj::Downcast(v) => variant = *v,
                    Proj::Deref => {
                        if let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
                            t = inner;
                        }
                    }
                    Proj::Index(_) => break,
                }
            }
            let what = if self.body.tys.vec_elem(t).is_some() { "a Vec index" } else { "an index" };
            self.err(
                "L0305",
                span,
                format!("cannot move out of {what}"),
                "Borrow the element with `&v[i]`, or clone it with `v[i].clone()`.",
            );
        } else if self.report && self.seen.insert(("L9001", span)) {
            let mut d = unsupported(span, "moving a field out of a struct or enum");
            d.fix = "Clone the field with `.clone()`, or match on a reference (`match &value`) and borrow it.".into();
            self.errs.push(d);
        }
    }

    fn check_init(&mut self, p: &Place, span: Span, st: &State) {
        if !self.report {
            return;
        }
        let l = p.local as usize;
        let (path, _) = self.prefix_of(p);
        // A moved field blocks uses of itself, of fields below it, and of every value
        // that contains it. A sibling field is fine. A place that is not exact below
        // its prefix (`arr[i]`) may reach any moved path under that prefix.
        let hit = self.moved_paths(st, l).find_map(|m| {
            if is_prefix(m, &path) {
                Some("use of moved value")
            } else if is_prefix(&path, m) {
                Some("use of partially moved value")
            } else {
                None
            }
        });
        if let Some(what) = hit {
            let name = self.local_name(p.local);
            let fix = "Clone the value before the move with `.clone()`, or borrow it with `&` instead of moving it.";
            self.err("L0301", span, format!("{what}: {name}"), fix);
            return;
        }
        if bit_has(st.uninit(), l) {
            let name = self.local_name(p.local);
            if bit_has(st.moved(), l) {
                let fix = "Clone the value before the move with `.clone()`, or borrow it with `&` instead of moving it.";
                self.err("L0301", span, format!("use of moved value: {name}"), fix);
            } else {
                self.err(
                    "L0310",
                    span,
                    format!("{name} is used before it is assigned on some path"),
                    "Assign a value on every path before this use.",
                );
            }
        }
    }

    /// The check for a write through a projection (`p.x = ...`). Writing a moved-out
    /// field puts it back, and writing a value puts back every moved field below it.
    /// Writing under a moved-out field, or into a value that was never assigned, is
    /// still an error.
    fn check_init_write(&mut self, p: &Place, span: Span, st: &State) {
        if !self.report {
            return;
        }
        let l = p.local as usize;
        let (path, exact) = self.prefix_of(p);
        if self.moved_paths(st, l).any(|m| is_prefix(m, &path) && !(exact && m.len() == path.len())) {
            let name = self.local_name(p.local);
            let fix = "Clone the value before the move with `.clone()`, or borrow it with `&` instead of moving it.";
            self.err("L0301", span, format!("use of moved value: {name}"), fix);
            return;
        }
        if bit_has(st.uninit(), l) && self.moved_paths(st, l).next().is_none() {
            let name = self.local_name(p.local);
            if bit_has(st.moved(), l) {
                let fix = "Clone the value before the move with `.clone()`, or borrow it with `&` instead of moving it.";
                self.err("L0301", span, format!("use of moved value: {name}"), fix);
            } else {
                self.err(
                    "L0310",
                    span,
                    format!("{name} is used before it is assigned on some path"),
                    "Assign a value on every path before this use.",
                );
            }
        }
    }

    /// Writes and `&mut` borrows need a `mut` root local, or a path through `&mut` references only.
    fn check_mutability(&mut self, p: &Place, span: Span, _st: &State, borrow: bool) {
        if !self.report {
            return;
        }
        let mut t = self.body.locals[p.local as usize].ty;
        let mut through_ref = false;
        let mut variant = 0;
        for pr in &p.proj {
            match (self.body.tys.kind(t), pr) {
                (TyKind::Ref(_, m, inner), Proj::Deref) => {
                    if !m.is_mut() {
                        let fix = "Take a `&mut` reference instead of `&`.";
                        if borrow {
                            self.err("L0308", span, "cannot borrow data behind a `&` reference as mutable".into(), fix);
                        } else {
                            self.err("L0309", span, "cannot assign through a `&` reference".into(), fix);
                        }
                        return;
                    }
                    through_ref = true;
                    t = inner;
                }
                (_, Proj::Deref) if self.body.tys.rc_elem(t).is_some() => {
                    if borrow {
                        self.err("L0308", span, "cannot borrow data in an `Rc` as mutable".into(), "Use `Rc::make_mut` or `Rc::get_mut` for mutable access.");
                    } else {
                        self.err("L0309", span, "cannot assign to data in an `Rc`".into(), "Use `Rc::make_mut` or `Rc::get_mut` for mutable access.");
                    }
                    return;
                }
                // A `Ref` guard is shared access; a `RefMut` is unique
                // (DerefMut), like a `Box` for writes.
                (_, Proj::Deref) if self.body.tys.guard_elem(t).is_some_and(|g| !g.1) => {
                    if borrow {
                        self.err("L0308", span, "cannot borrow data in a `Ref` as mutable".into(), "Take the borrow with `borrow_mut()`.");
                    } else {
                        self.err("L0309", span, "cannot assign to data in a `Ref`".into(), "Take the borrow with `borrow_mut()`.");
                    }
                    return;
                }
                (_, Proj::Deref) if self.body.tys.guard_elem(t).is_some() => t = self.body.tys.guard_elem(t).unwrap().0,
                (_, Proj::Deref) if self.body.tys.boxed_elem(t).is_some() => t = self.body.tys.boxed_elem(t).unwrap(),
                (_, Proj::Index(_)) if self.body.tys.vec_elem(t).is_some() => t = self.body.tys.vec_elem(t).unwrap(),
                (TyKind::Array(e, _) | TyKind::Slice(e), Proj::Index(_)) => t = e,
                (TyKind::Tuple(ts), Proj::Field(i)) => {
                    t = self.body.tys.tys_of(ts).get(*i as usize).copied().unwrap_or(ERROR);
                }
                (TyKind::Adt(..), Proj::Field(i)) if self.body.tys.local_adt(t).is_some() => {
                    t = self.step_field_ty(t, variant, *i);
                    variant = 0;
                }
                (TyKind::Adt(..), Proj::Downcast(v)) => variant = *v,
                (_, Proj::Field(_)) if self.body.tys.option_elem(t).is_some() => {
                    t = self.body.tys.option_elem(t).unwrap();
                    variant = 0;
                }
                (_, Proj::Field(_)) if self.body.tys.result_args(t).is_some() => {
                    let (a, b) = self.body.tys.result_args(t).unwrap();
                    t = if variant == 0 { a } else { b };
                    variant = 0;
                }
                _ => {}
            }
        }
        if !through_ref && !self.body.locals[p.local as usize].mutable {
            let name = self.local_name(p.local);
            if borrow {
                self.err(
                    "L0308",
                    span,
                    format!("cannot borrow {name} as mutable, because it is not declared as mutable"),
                    "Declare it with `let mut`.",
                );
            } else {
                self.err(
                    "L0302",
                    span,
                    format!("cannot assign to a field of {name}, because it is not declared as mutable"),
                    "Declare it with `let mut`.",
                );
            }
        }
    }

    /// Checks one access against the loans live after the statement.
    fn access(&mut self, p: &Place, kind: Access, span: Span, live_loans: &BitSet, p_range: Option<(IdxKey, IdxKey)>) {
        if !self.report {
            return;
        }
        for li in live_loans.iter() {
            let loan = &self.loans[li];
            if self.through_shared_ref(&loan.place) {
                continue;
            }
            // A write to a whole local is shallow: writing a reference local itself does
            // not touch the value behind it, so a loan on `*a` does not block `a = ...`.
            if kind == Access::Write && p.proj.is_empty() && loan.place.proj.first() == Some(&Proj::Deref) && self.through_ref(&loan.place) {
                continue;
            }
            // Storage ending for a byte string literal's temp drops
            // nothing: its bytes are a const blob (see `promoted`).
            if kind == Access::Dead && self.promoted.get(loan.place.local as usize).copied().unwrap_or(false) {
                continue;
            }
            let mutable = loan.mutable && !self.reserved.contains(&li);
            let conflict = match kind {
                Access::Read | Access::BorrowShared => mutable && self.overlaps(p, p_range, loan),
                Access::Write | Access::Move | Access::BorrowMut => self.overlaps(p, p_range, loan),
                Access::Dead => loan.place.local == p.local && !self.through_ref(&loan.place),
            };
            if !conflict {
                continue;
            }
            let name = self.local_name(loan.place.local);
            let to_ret = self.sol.as_ref().is_some_and(|s| s.to_ret[li]);
            let (code, msg, fix) = match (kind, mutable) {
                (Access::Dead, _) if to_ret => (
                    "L0307",
                    format!("cannot return a reference to {name}, which is owned by this function"),
                    "Return an owned value instead (for example `String` instead of `&str`).",
                ),
                (Access::Dead, _) if self.body.locals[loan.place.local as usize].name.is_none() => (
                    "L0306",
                    "a temporary value is dropped while it is still borrowed".to_string(),
                    "Store the value in a variable with `let` first, so it lives long enough.",
                ),
                (Access::Dead, _) => (
                    "L0306",
                    format!("{name} does not live long enough: it is dropped while still borrowed"),
                    "Declare the value in an outer scope, or stop using the reference before the value goes out of scope.",
                ),
                (Access::Move, _) => (
                    "L0311",
                    format!("cannot move out of {name} because it is borrowed"),
                    "Stop using the reference before the move, or clone the value.",
                ),
                (Access::BorrowMut, true) => (
                    "L0304",
                    format!("cannot borrow {name} as mutable more than once at a time"),
                    "Finish using the first `&mut` reference before taking another one.",
                ),
                (Access::BorrowMut, false) => (
                    "L0303",
                    format!("cannot borrow {name} as mutable because it is also borrowed as immutable"),
                    "Finish using the shared reference before taking a `&mut` reference.",
                ),
                (Access::BorrowShared, _) => (
                    "L0303",
                    format!("cannot borrow {name} as immutable because it is also borrowed as mutable"),
                    "Finish using the `&mut` reference first.",
                ),
                (Access::Write, _) => (
                    "L0312",
                    format!("cannot assign to {name} because it is borrowed"),
                    "Finish using the reference before the assignment.",
                ),
                (Access::Read, _) => {
                    ("L0303", format!("cannot use {name} because it is mutably borrowed"), "Finish using the `&mut` reference first.")
                }
            };
            let labels = Self::loan_labels(loan);
            self.err_labeled(code, span, msg, fix, labels);
            return;
        }
    }

    /// At a return, every local's storage ends: a loan of a local (not
    /// through a reference) still in scope there must outlive the body,
    /// because its region reaches the return value or a universal region.
    fn check_return(&mut self, q: usize, span: Span) {
        if self.scope.is_empty() {
            return;
        }
        let wl = self.wl;
        let in_scope: Vec<usize> = bit_iter(&self.scope[q * wl..(q + 1) * wl]).collect();
        for li in in_scope {
            let loan = &self.loans[li];
            if self.through_ref(&loan.place) {
                continue;
            }
            let name = self.local_name(loan.place.local);
            let labels = Self::loan_labels(loan);
            let to_ret = self.sol.as_ref().is_some_and(|s| s.to_ret[li]);
            if to_ret {
                self.err_labeled(
                    "L0307",
                    span,
                    format!("cannot return a reference to {name}, which is owned by this function"),
                    "Return an owned value instead (for example `String` instead of `&str`).",
                    labels,
                );
            } else {
                self.err_labeled(
                    "L0306",
                    span,
                    format!("{name} does not live long enough: it is still borrowed when the function returns"),
                    "Borrow from a parameter instead, or store an owned value.",
                    labels,
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{BitSet, Shape, State, bit_has, bit_iter, bit_set};

    /// The flat state keeps every set apart: a bit in one set shows up in
    /// no other set, and a join reports only new bits.
    #[test]
    fn flat_state_sets_are_disjoint() {
        let sh = Shape { n: 70, wn: 2, wm: 1 };
        let mut a = State::new(sh);
        bit_set(a.uninit_mut(), 69);
        bit_set(a.paths_mut(), 5);
        bit_set(a.moved_mut(), 3);
        bit_set(a.ever_mut(), 4);
        assert!(bit_has(a.uninit(), 69) && !bit_has(a.init(), 69) && !bit_has(a.moved(), 69));
        assert!(bit_has(a.ever(), 4) && !bit_has(a.moved(), 4) && !bit_has(a.ever(), 3));
        assert_eq!(bit_iter(a.paths()).collect::<Vec<_>>(), vec![5]);
        assert!(bit_has(a.moved(), 3) && !bit_has(a.init(), 3));
        let mut b = State::new(sh);
        assert!(b.join(&a), "new bits are a change");
        assert!(!b.join(&a), "the same bits are not");
        assert!(b == a);
    }

    /// One-word sets stay inline; wider sets spill to the heap form; both
    /// answer the same operations across the boundary.
    #[test]
    fn bitset_inline_and_wide_forms_agree() {
        let mut one = BitSet::new(64);
        one.insert(0);
        one.insert(63);
        assert!(bit_has(one.words(), 0) && bit_has(one.words(), 63) && !bit_has(one.words(), 1));
        assert_eq!(one.iter().collect::<Vec<_>>(), vec![0, 63]);
        one.remove(0);
        assert!(!bit_has(one.words(), 0) && one.iter().next().is_some());

        let mut wide = BitSet::new(200);
        wide.insert(64);
        wide.insert(199);
        assert!(bit_has(wide.words(), 64) && bit_has(wide.words(), 199) && !bit_has(wide.words(), 63));
        assert_eq!(wide.iter().collect::<Vec<_>>(), vec![64, 199]);
        let mut other = BitSet::new(200);
        other.insert(199);
        assert!(!wide.union(&other), "no new bit, no change");
        other.insert(65);
        assert!(wide.union(&other), "a new bit is a change");
        wide.clear();
        assert!(wide.iter().next().is_none());
    }
}
