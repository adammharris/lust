// Mono IR fingerprints and the in-session IR cache (docs/ARCH.md
// sections 4.2 and 8.4). One instance per fn today, so the instance
// fingerprint is the fingerprint of the fn's lowered IR body: locals
// and types hashed deeply (named Adt layouts fold in through
// `graph::hash_ty_deep`), call targets by stable disk identity, and
// statement locations relative to the fn's first line (the C the
// backend emits embeds those). The fingerprint has no slot numbers:
// a slot renumber (a compaction) moves a body's own slot or one in
// its `CachedBody::used_at_gen` (the slots cgen recorded it prints,
// `FnOut::used`), and the daemon re-emits its C from the cached IR
// here with no front-end redo (no re-lex, re-parse, re-check, or
// re-lower). Unit objects key on their C text (cache.rs).
//
// `CachedBody` is the session form of one IR body with every
// session-local id translated out: types become structural trees,
// fn and Adt and static references become stable defs, string
// constants become their contents. `rebuild` interns it back into a
// later request's program; the caller verifies the rebuilt body's
// fingerprint equals the cached one and falls back to a recheck on
// any mismatch or unresolvable reference, so a translation gap is a
// slowdown, never a wrong answer. Cached bodies are only reused
// while their file's text stands (spans stay valid); the caller
// checks that through `CachedBody::file_hash`.
use super::graph;
use crate::ast::{BinOp, FmtSpec, UnOp};
use crate::check::collect::Program;
use crate::check::Builtin;
use crate::def::{DefId, DiskDefId, LocalDefId};
use crate::diag::{SourceMap, Span};
use crate::intern::{FxHasher, FxMap};
use crate::ir::*;
use crate::ty::*;
use std::hash::{Hash, Hasher};

/// Hashes one def by stable identity under this program (the same
/// form `graph::hash_def` uses).
fn hash_def(h: &mut FxHasher, p: &Program, def: DefId) {
    graph::hash_def_pub(h, p, def);
}

/// One statement's packed source position, relative to the fn's first
/// line, as cgen embeds it: (file path, relative line, column). The
/// path rides in because a multi-file crate's spans name many files.
fn hash_span(h: &mut FxHasher, map: &SourceMap, base_line: u32, span: Span) {
    if span.file == crate::diag::FileId::STD_SITE {
        span.hash(h);
        return;
    }
    let at = map.call_site(span);
    map.path(at.file).hash(h);
    let (line, col) = map.line_display_col(at);
    (line.saturating_sub(base_line), col).hash(h);
}

fn hash_place(h: &mut FxHasher, place: &Place) {
    place.local.hash(h);
    (place.proj.len() as u64).hash(h);
    for p in &place.proj {
        match p {
            Proj::Deref => 0u8.hash(h),
            Proj::Field(i) => (1u8, i).hash(h),
            Proj::Downcast(i) => (2u8, i).hash(h),
            Proj::Index(l) => (3u8, l).hash(h),
        }
    }
}

fn hash_const(h: &mut FxHasher, p: &Program, c: &Const) {
    match c {
        Const::Int(v, ty) => (0u8, v, ty.name()).hash(h),
        Const::Float(bits, ty) => (1u8, bits, ty.name()).hash(h),
        Const::Bool(b) => (2u8, b).hash(h),
        Const::Char(c) => (3u8, c).hash(h),
        Const::Str(i) => {
            4u8.hash(h);
            p.ast.strings.get(*i as usize).map_or("", String::as_str).hash(h);
        }
        Const::Bytes(b) => {
            6u8.hash(h);
            b.as_slice().hash(h);
        }
        Const::StrBytes(b) => {
            7u8.hash(h);
            b.as_slice().hash(h);
        }
        Const::Unit => 5u8.hash(h),
    }
}

fn hash_operand(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, o: &Operand, seen: &mut graph::DeepMemo) {
    match o {
        Operand::Copy(place) => {
            0u8.hash(h);
            hash_place(h, place);
        }
        Operand::Move(place) => {
            1u8.hash(h);
            hash_place(h, place);
        }
        Operand::Const(c) => {
            2u8.hash(h);
            hash_const(h, p, c);
        }
    }
    let _ = (tys, seen);
}

fn hash_fmt(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, parts: &[FmtPart], seen: &mut graph::DeepMemo) {
    (parts.len() as u64).hash(h);
    for part in parts {
        match part {
            FmtPart::Lit(s) => {
                0u8.hash(h);
                s.hash(h);
            }
            FmtPart::Arg { value, ty, debug, spec, width, prec } => {
                (1u8, debug).hash(h);
                spec.hash(h);
                hash_operand(h, p, tys, value, seen);
                for c in [width, prec].into_iter().flatten() {
                    hash_operand(h, p, tys, c, seen);
                }
                graph::hash_ty_deep(h, p, tys, *ty, seen);
            }
        }
    }
}

fn hash_rvalue(h: &mut FxHasher, p: &Program, tys: &impl TyIntern, r: &Rvalue, seen: &mut graph::DeepMemo) {
    let ty = |h: &mut FxHasher, t: Ty, seen: &mut graph::DeepMemo| graph::hash_ty_deep(h, p, tys, t, seen);
    let ops = |h: &mut FxHasher, os: &[Operand], seen: &mut graph::DeepMemo| {
        (os.len() as u64).hash(h);
        for o in os {
            hash_operand(h, p, tys, o, seen);
        }
    };
    match r {
        Rvalue::Use(o) => {
            0u8.hash(h);
            hash_operand(h, p, tys, o, seen);
        }
        Rvalue::Ref(m, place) => {
            (1u8, m).hash(h);
            hash_place(h, place);
        }
        Rvalue::Bin(op, a, b) => {
            2u8.hash(h);
            std::mem::discriminant(op).hash(h);
            hash_operand(h, p, tys, a, seen);
            hash_operand(h, p, tys, b, seen);
        }
        Rvalue::Un(op, a) => {
            3u8.hash(h);
            std::mem::discriminant(op).hash(h);
            hash_operand(h, p, tys, a, seen);
        }
        Rvalue::Cast(o, t) => {
            4u8.hash(h);
            hash_operand(h, p, tys, o, seen);
            ty(h, *t, seen);
        }
        Rvalue::Aggregate(adt, variant, os) => {
            (5u8, variant).hash(h);
            hash_def(h, p, p.def_of_adt(*adt));
            ops(h, os, seen);
        }
        Rvalue::Opt(t, o) => {
            6u8.hash(h);
            ty(h, *t, seen);
            match o {
                Some(o) => hash_operand(h, p, tys, o, seen),
                None => 0u8.hash(h),
            }
        }
        Rvalue::Res(t, is_ok, o) => {
            (23u8, is_ok).hash(h);
            ty(h, *t, seen);
            hash_operand(h, p, tys, o, seen);
        }
        Rvalue::VecLit(t, os) => {
            7u8.hash(h);
            ty(h, *t, seen);
            ops(h, os, seen);
        }
        Rvalue::VecRepeat(t, a, b) => {
            8u8.hash(h);
            ty(h, *t, seen);
            hash_operand(h, p, tys, a, seen);
            hash_operand(h, p, tys, b, seen);
        }
        Rvalue::Eq { a, b, ty: t, ne } => {
            (9u8, ne).hash(h);
            hash_operand(h, p, tys, a, seen);
            hash_operand(h, p, tys, b, seen);
            ty(h, *t, seen);
        }
        Rvalue::Cmp { op, a, b, ty: t } => {
            24u8.hash(h);
            std::mem::discriminant(op).hash(h);
            hash_operand(h, p, tys, a, seen);
            hash_operand(h, p, tys, b, seen);
            ty(h, *t, seen);
        }
        Rvalue::StrCmp(op, a, b) => {
            10u8.hash(h);
            std::mem::discriminant(op).hash(h);
            hash_operand(h, p, tys, a, seen);
            hash_operand(h, p, tys, b, seen);
        }
        Rvalue::StringAdd(a, b) => {
            11u8.hash(h);
            hash_operand(h, p, tys, a, seen);
            hash_operand(h, p, tys, b, seen);
        }
        Rvalue::Format(parts) => {
            12u8.hash(h);
            hash_fmt(h, p, tys, parts, seen);
        }
        Rvalue::Discriminant(place) => {
            13u8.hash(h);
            hash_place(h, place);
        }
        Rvalue::TupleAgg(t, os) => {
            14u8.hash(h);
            ty(h, *t, seen);
            ops(h, os, seen);
        }
        Rvalue::ArrayAgg(t, os) => {
            15u8.hash(h);
            ty(h, *t, seen);
            ops(h, os, seen);
        }
        Rvalue::ArrayRepeat(t, o, n) => {
            (16u8, n).hash(h);
            ty(h, *t, seen);
            hash_operand(h, p, tys, o, seen);
        }
        Rvalue::SliceOf(place) => {
            17u8.hash(h);
            hash_place(h, place);
        }
        Rvalue::Subslice { base, lo, hi, inclusive, mutable } => {
            (18u8, inclusive, mutable).hash(h);
            hash_place(h, base);
            hash_operand(h, p, tys, lo, seen);
            match hi {
                Some(o) => hash_operand(h, p, tys, o, seen),
                None => 0u8.hash(h),
            }
        }
        Rvalue::LenOf(place) => {
            19u8.hash(h);
            hash_place(h, place);
        }
        Rvalue::StaticLoad(i) => {
            20u8.hash(h);
            hash_static(h, p, *i);
        }
        Rvalue::StaticRef(i) => {
            21u8.hash(h);
            hash_static(h, p, *i);
        }
        Rvalue::FnValue(f, t) => {
            22u8.hash(h);
            hash_def(h, p, p.def_id(*f));
            ty(h, *t, seen);
        }
        Rvalue::ItemShim(item, t) => {
            50u8.hash(h);
            ty(h, *item, seen);
            ty(h, *t, seen);
        }
        Rvalue::MakeDyn { ptr, src, dyn_ty } => {
            23u8.hash(h);
            hash_operand(h, p, tys, ptr, seen);
            ty(h, *src, seen);
            ty(h, *dyn_ty, seen);
            // The vtable's entries are part of the emitted C: each
            // shim's slot (in the used-slots hash) and its signature.
            if let Some(vid) = crate::check::generics::vtable_for(p, tys, *src, *dyn_ty) {
                for f in vtable_fns(p, vid) {
                    hash_def(h, p, p.def_id(f));
                    let info = p.fn_info(f);
                    for &t in info.params.iter().chain(std::iter::once(&info.ret)) {
                        ty(h, t, seen);
                    }
                }
            }
        }
        Rvalue::DynUpcast { ptr, path } => {
            24u8.hash(h);
            hash_operand(h, p, tys, ptr, seen);
            path.hash(h);
        }
        Rvalue::DynMeta { ptr, word } => {
            (25u8, word).hash(h);
            hash_operand(h, p, tys, ptr, seen);
        }
        Rvalue::DynData { ptr, ty: t } => {
            41u8.hash(h);
            hash_operand(h, p, tys, ptr, seen);
            ty(h, *t, seen);
        }
        Rvalue::WriteFmt(dst, parts, stream) => {
            (40u8, stream).hash(h);
            hash_operand(h, p, tys, dst, seen);
            hash_fmt(h, p, tys, parts, seen);
        }
        Rvalue::FormatArgs(env, parts) => {
            (42u8, env.is_some()).hash(h);
            if let Some(env) = env {
                hash_operand(h, p, tys, env, seen);
            }
            hash_fmt(h, p, tys, parts, seen);
        }
    }
}

/// Every fn a vtable's entries call, its super vtables included.
fn vtable_fns(p: &Program, vid: u32) -> Vec<LocalDefId> {
    let mut out = Vec::new();
    let mut work = vec![vid];
    let mut seen: Vec<u32> = Vec::new();
    while let Some(v) = work.pop() {
        if seen.contains(&v) {
            continue;
        }
        seen.push(v);
        let vt = &p.gx.vtables[v as usize];
        out.extend(vt.methods.iter().copied());
        work.extend(vt.supers.iter().copied());
    }
    out
}

/// A static reference by stable def, never by collect index (indices
/// shift when statics are added; see `compile::slot_update`'s item
/// sequence guard for the matching reuse rule).
fn hash_static(h: &mut FxHasher, p: &Program, idx: u32) {
    match p.static_defs.get(idx as usize) {
        Some(&def) => hash_def(h, p, def),
        None => 0u64.hash(h),
    }
}

/// The instance fingerprint of one lowered body (section 4.2): stable
/// across sessions and slot assignments, sensitive to everything the
/// emitted C depends on except slot numbers themselves (those ride
/// in the unit's used-slots hash) and the fn's absolute position
/// (locations hash relative to `base_line`).
pub(crate) fn ir_fingerprint(p: &Program, body: &Body, map: &SourceMap, base_line: u32) -> u64 {
    let mut h = FxHasher::default();
    "ir-v1".hash(&mut h);
    hash_def(&mut h, p, p.def_id(body.fn_id));
    // `#[track_caller]` changes the fn's C signature and every panic
    // location in it (check/caller.rs).
    crate::check::caller::is_track_caller(p, body.fn_id).hash(&mut h);
    (body.arg_count as u64).hash(&mut h);
    let mut seen = graph::DeepMemo::default();
    (body.locals.len() as u64).hash(&mut h);
    for l in &body.locals {
        graph::hash_ty_deep(&mut h, p, &body.tys, l.ty, &mut seen);
        l.mutable.hash(&mut h);
    }
    (body.blocks.len() as u64).hash(&mut h);
    for b in &body.blocks {
        (b.stmts.len() as u64).hash(&mut h);
        for s in &b.stmts {
            hash_span(&mut h, map, base_line, s.span);
            match &s.kind {
                StmtKind::Assign(place, r) => {
                    0u8.hash(&mut h);
                    hash_place(&mut h, place);
                    hash_rvalue(&mut h, p, &body.tys, r, &mut seen);
                }
                StmtKind::Drop(l) => (1u8, l).hash(&mut h),
                StmtKind::StorageDead(l) => (2u8, l).hash(&mut h),
                StmtKind::FakeRead(l) => (3u8, l).hash(&mut h),
                StmtKind::Print { stderr, newline, parts } => {
                    (4u8, stderr, newline).hash(&mut h);
                    hash_fmt(&mut h, p, &body.tys, parts, &mut seen);
                }
            }
        }
        hash_span(&mut h, map, base_line, b.term_span);
        match &b.term {
            Terminator::Goto(t) => (0u8, t.0).hash(&mut h),
            Terminator::If(o, a, c) => {
                1u8.hash(&mut h);
                hash_operand(&mut h, p, &body.tys, o, &mut seen);
                (a.0, c.0).hash(&mut h);
            }
            Terminator::Switch(o, cases, other) => {
                2u8.hash(&mut h);
                hash_operand(&mut h, p, &body.tys, o, &mut seen);
                (cases.len() as u64).hash(&mut h);
                for (v, t) in cases {
                    (v, t.0).hash(&mut h);
                }
                other.0.hash(&mut h);
            }
            Terminator::Call { target, args, dest, next, unwind } => {
                3u8.hash(&mut h);
                match target {
                    CallTarget::Fn(f) => {
                        0u8.hash(&mut h);
                        hash_def(&mut h, p, p.def_id(*f));
                        // A `#[track_caller]` callee takes the call's location.
                        crate::check::caller::is_track_caller(p, *f).hash(&mut h);
                    }
                    CallTarget::Builtin(b) => {
                        // With its payload: `SliceTrimAscii(0)` and `(1)`
                        // have the same types and emit different C.
                        1u8.hash(&mut h);
                        b.hash(&mut h);
                    }
                    CallTarget::Intrinsic(i) => (2u8, i).hash(&mut h),
                    CallTarget::Indirect(l) => (3u8, l).hash(&mut h),
                    CallTarget::Dyn(k) => (4u8, k).hash(&mut h),
                }
                (args.len() as u64).hash(&mut h);
                for a in args {
                    hash_operand(&mut h, p, &body.tys, a, &mut seen);
                }
                hash_place(&mut h, dest);
                next.0.hash(&mut h);
                unwind.map_or(0, |u| u.0 + 1).hash(&mut h);
            }
            Terminator::Return => 4u8.hash(&mut h),
            Terminator::Unreachable => 5u8.hash(&mut h),
            Terminator::MatchExhausted => 7u8.hash(&mut h),
            Terminator::Panic(parts) => {
                6u8.hash(&mut h);
                hash_fmt(&mut h, p, &body.tys, parts, &mut seen);
            }
        }
    }
    for &(b, i, u) in &body.stmt_unwind {
        (b.0, i, u.0).hash(&mut h);
    }
    // cgen gives a promoted temp static storage, not a frame slot.
    body.promoted.hash(&mut h);
    h.finish()
}

// ---------- Cached body translation ----------

/// A structural type tree: one entry per distinct `Ty` in a cached
/// body, children by index into the same table.
#[derive(Clone, Debug)]
enum TyTree {
    Error,
    Unit,
    Bool,
    Char,
    Never,
    Int(IntTy),
    Float(FloatTy),
    Str,
    Ref(Region, Mut, u32),
    RawPtr(Mut, u32),
    Slice(u32),
    Array(u32, ConstKind),
    Tuple(Vec<u32>),
    Adt(DefId, Vec<ArgTree>),
    FnPtr { count: u32, is_unsafe: bool, extern_c: bool, free_slots: u32, free_region: Region, own_out: u32, out_slots: u8, binders: u64, inputs: Vec<u32>, output: u32 },
    FnDef(DefId, Vec<ArgTree>),
    Closure(DefId, Vec<ArgTree>),
    Dyn { region: Region, principal: Option<(u32, TraitRefTree)>, supertraits: Vec<(u32, TraitRefTree)>, auto: (bool, bool, bool, bool, bool) },
    Opaque(DefId, Vec<ArgTree>),
    Param(ParamId),
    Projection(AssocId, Vec<ArgTree>),
    Infer(bool),
}

#[derive(Clone, Debug)]
enum ArgTree {
    Ty(u32),
    Lifetime(Region),
    Const(ConstKind),
}

#[derive(Clone, Debug)]
struct TraitRefTree {
    def: DefId,
    args: Vec<ArgTree>,
    bindings: Vec<(DefId, ArgTree)>,
}

/// One IR body's cached form. See the module docs.
pub(crate) struct CachedBody {
    /// Hash of the fn's file text when cached: spans are only valid
    /// while it stands.
    pub file_hash: u64,
    /// The slot this fn owned when its C was emitted, and the slots
    /// its C printed then (`FnOut::used`), each with its fn's stable id.
    /// A difference against today's assignment is the re-emit trigger.
    pub slot_at_gen: u32,
    pub used_at_gen: Vec<(DiskDefId, u32)>,
    /// `ir_fingerprint` of the source body; a rebuild must match it.
    pub ir_fp: u64,
    arg_count: usize,
    tys: Vec<TyTree>,
    locals: Vec<(u32, bool, Option<String>)>,
    blocks: Vec<CachedBlock>,
    stmt_unwind: Vec<(Bb, u32, Bb)>,
    promoted: Vec<Local>,
}

#[derive(Clone, Debug)]
struct CachedBlock {
    stmts: Vec<CachedStmt>,
    term: CachedTerm,
    term_span: Span,
}

#[derive(Clone, Debug)]
struct CachedStmt {
    kind: CachedStmtKind,
    span: Span,
}

#[derive(Clone, Debug)]
enum CachedStmtKind {
    Assign(Place, CachedRvalue),
    Drop(Local),
    StorageDead(Local),
    FakeRead(Local),
    Print { stderr: bool, newline: bool, parts: Vec<CachedFmt> },
}

#[derive(Clone, Debug)]
enum CachedOperand {
    Copy(Place),
    Move(Place),
    Const(CachedConst),
}

#[derive(Clone, Debug)]
enum CachedConst {
    Int(u128, IntTy),
    Float(u64, FloatTy),
    Bool(bool),
    Char(char),
    Str(String),
    // The blob's bytes travel with the cached body: no AST table
    // index stays valid across rebuilds.
    Bytes(Vec<u8>),
    // A synthesized `&str` (`type_name`): its bytes travel too.
    StrBytes(Vec<u8>),
    Unit,
}

#[derive(Clone, Debug)]
enum CachedFmt {
    Lit(String),
    Arg { value: CachedOperand, ty: u32, debug: bool, spec: FmtSpec, width: Option<CachedOperand>, prec: Option<CachedOperand> },
}

#[derive(Clone, Debug)]
enum CachedRvalue {
    Use(CachedOperand),
    Ref(bool, Place),
    Bin(BinOp, CachedOperand, CachedOperand),
    Un(UnOp, CachedOperand),
    Cast(CachedOperand, u32),
    Aggregate(DefId, u32, Vec<CachedOperand>),
    Opt(u32, Option<CachedOperand>),
    Res(u32, bool, CachedOperand),
    VecLit(u32, Vec<CachedOperand>),
    VecRepeat(u32, CachedOperand, CachedOperand),
    Eq { a: CachedOperand, b: CachedOperand, ty: u32, ne: bool },
    Cmp { op: BinOp, a: CachedOperand, b: CachedOperand, ty: u32 },
    StrCmp(BinOp, CachedOperand, CachedOperand),
    StringAdd(CachedOperand, CachedOperand),
    Format(Vec<CachedFmt>),
    Discriminant(Place),
    TupleAgg(u32, Vec<CachedOperand>),
    ArrayAgg(u32, Vec<CachedOperand>),
    ArrayRepeat(u32, CachedOperand, u64),
    SliceOf(Place),
    Subslice { base: Place, lo: CachedOperand, hi: Option<CachedOperand>, inclusive: bool, mutable: bool },
    LenOf(Place),
    StaticLoad(DefId),
    StaticRef(DefId),
    FnValue(DiskDefId, u32),
    ItemShim(u32, u32),
    MakeDyn(CachedOperand, u32, u32),
    DynUpcast(CachedOperand, Vec<u32>),
    DynMeta(CachedOperand, u32),
    DynData(CachedOperand, u32),
    WriteFmt(CachedOperand, Vec<CachedFmt>, Option<bool>),
    FormatArgs(Option<CachedOperand>, Vec<CachedFmt>),
}

#[derive(Clone, Debug)]
enum CachedTerm {
    Goto(Bb),
    If(CachedOperand, Bb, Bb),
    Switch(CachedOperand, Vec<(u32, Bb)>, Bb),
    Call { target: CachedTarget, args: Vec<CachedOperand>, dest: Place, next: Bb, unwind: Option<Bb> },
    Return,
    Unreachable,
    MatchExhausted,
    Panic(Vec<CachedFmt>),
}

#[derive(Clone, Debug)]
enum CachedTarget {
    Fn(DiskDefId),
    Builtin(Builtin),
    Intrinsic(u32),
    Indirect(Local),
    Dyn(u32),
}

/// Builds `TyTree`s from one body's type store, memoized per `Ty`.
struct TreeBuilder<'x> {
    tys: &'x dyn TyIntern,
    memo: FxMap<Ty, u32>,
    out: Vec<TyTree>,
}

impl TreeBuilder<'_> {
    fn args(&mut self, a: ArgsId) -> Vec<ArgTree> {
        self.tys
            .args(a)
            .iter()
            .map(|a| match a {
                GenericArg::Ty(t) => ArgTree::Ty(self.ty(*t)),
                GenericArg::Lifetime(r) => ArgTree::Lifetime(*r),
                GenericArg::Const(c) => ArgTree::Const(self.tys.const_kind(*c)),
            })
            .collect()
    }

    fn trait_ref(&mut self, tr: &TraitRef) -> TraitRefTree {
        TraitRefTree {
            def: tr.def,
            args: self.args(tr.args),
            bindings: self
                .tys
                .bindings(tr.bindings)
                .iter()
                .map(|(d, a)| {
                    let a = match a {
                        GenericArg::Ty(t) => ArgTree::Ty(self.ty(*t)),
                        GenericArg::Lifetime(r) => ArgTree::Lifetime(*r),
                        GenericArg::Const(c) => ArgTree::Const(self.tys.const_kind(*c)),
                    };
                    (*d, a)
                })
                .collect(),
        }
    }

    fn ty(&mut self, t: Ty) -> u32 {
        if let Some(&i) = self.memo.get(&t) {
            return i;
        }
        let idx = self.out.len() as u32;
        self.memo.insert(t, idx);
        self.out.push(TyTree::Error);
        let tree = match self.tys.kind(t) {
            TyKind::Error => TyTree::Error,
            TyKind::Unit => TyTree::Unit,
            TyKind::Bool => TyTree::Bool,
            TyKind::Char => TyTree::Char,
            TyKind::Never => TyTree::Never,
            TyKind::Int(i) => TyTree::Int(i),
            TyKind::Float(f) => TyTree::Float(f),
            TyKind::Str => TyTree::Str,
            TyKind::Ref(r, m, inner) => TyTree::Ref(r, m, self.ty(inner)),
            TyKind::RawPtr(m, inner) => TyTree::RawPtr(m, self.ty(inner)),
            TyKind::Slice(inner) => TyTree::Slice(self.ty(inner)),
            TyKind::Array(inner, n) => {
                let inner = self.ty(inner);
                TyTree::Array(inner, self.tys.const_kind(n))
            }
            TyKind::Tuple(ts) => TyTree::Tuple(self.tys.tys_of(ts).iter().map(|t| self.ty(*t)).collect()),
            TyKind::Adt(def, a) => TyTree::Adt(def, self.args(a)),
            TyKind::FnPtr(sig) => {
                let sig = self.tys.sig(sig);
                let inputs = self.tys.tys_of(sig.value.inputs).iter().map(|t| self.ty(*t)).collect();
                TyTree::FnPtr {
                    count: sig.count,
                    is_unsafe: sig.value.is_unsafe,
                    extern_c: sig.value.extern_c,
                    free_slots: sig.value.free_slots,
                    free_region: sig.value.free_region,
                    own_out: sig.value.own_out,
                    out_slots: sig.value.out_slots,
                    binders: sig.value.binders,
                    inputs,
                    output: self.ty(sig.value.output),
                }
            }
            TyKind::FnDef(def, a) => TyTree::FnDef(def, self.args(a)),
            TyKind::Closure(def, a) => TyTree::Closure(def, self.args(a)),
            TyKind::Dyn(bounds, r) => {
                let b = self.tys.dyn_bounds(bounds);
                let principal = b.principal.as_ref().map(|pr| (pr.count, self.trait_ref(&pr.value)));
                let supertraits = b.supertraits.iter().map(|st| (st.count, self.trait_ref(&st.value))).collect();
                TyTree::Dyn { region: r, principal, supertraits, auto: (b.auto.send, b.auto.sync, b.auto.unpin, b.auto.unwind_safe, b.auto.ref_unwind_safe) }
            }
            TyKind::Opaque(def, a) => TyTree::Opaque(def, self.args(a)),
            TyKind::Param(i) => TyTree::Param(i),
            TyKind::Projection(assoc, a) => TyTree::Projection(assoc, self.args(a)),
            TyKind::Infer(v) => TyTree::Infer(v.is_int()),
        };
        self.out[idx as usize] = tree;
        idx
    }
}

/// Interns `TyTree`s back into one body-local store.
struct TreeIntern<'x> {
    trees: &'x [TyTree],
    memo: Vec<Option<Ty>>,
}

impl TreeIntern<'_> {
    fn args(&mut self, tys: &mut Tys, args: &[ArgTree]) -> Option<ArgsId> {
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            out.push(match a {
                ArgTree::Ty(i) => GenericArg::Ty(self.ty(tys, *i)?),
                ArgTree::Lifetime(r) => GenericArg::Lifetime(*r),
                ArgTree::Const(c) => GenericArg::Const(tys.intern_const(*c)),
            });
        }
        Some(tys.intern_args(&out))
    }

    fn trait_ref(&mut self, tys: &mut Tys, tr: &TraitRefTree) -> Option<TraitRef> {
        let args = self.args(tys, &tr.args)?;
        let mut bindings = Vec::with_capacity(tr.bindings.len());
        for (d, a) in &tr.bindings {
            let a = match a {
                ArgTree::Ty(i) => GenericArg::Ty(self.ty(tys, *i)?),
                ArgTree::Lifetime(r) => GenericArg::Lifetime(*r),
                ArgTree::Const(c) => GenericArg::Const(tys.intern_const(*c)),
            };
            bindings.push((*d, a));
        }
        Some(TraitRef { def: tr.def, args, bindings: tys.intern_bindings(&bindings) })
    }

    fn ty(&mut self, tys: &mut Tys, i: u32) -> Option<Ty> {
        if let Some(t) = self.memo.get(i as usize).copied().flatten() {
            return Some(t);
        }
        let tree = self.trees.get(i as usize)?.clone();
        let t = match &tree {
            TyTree::Error => tys.intern(TyKind::Error),
            TyTree::Unit => tys.intern(TyKind::Unit),
            TyTree::Bool => tys.intern(TyKind::Bool),
            TyTree::Char => tys.intern(TyKind::Char),
            TyTree::Never => tys.intern(TyKind::Never),
            TyTree::Int(x) => tys.intern(TyKind::Int(*x)),
            TyTree::Float(x) => tys.intern(TyKind::Float(*x)),
            TyTree::Str => tys.intern(TyKind::Str),
            TyTree::Ref(r, m, inner) => {
                let inner = self.ty(tys, *inner)?;
                tys.intern(TyKind::Ref(*r, *m, inner))
            }
            TyTree::RawPtr(m, inner) => {
                let inner = self.ty(tys, *inner)?;
                tys.intern(TyKind::RawPtr(*m, inner))
            }
            TyTree::Slice(inner) => {
                let inner = self.ty(tys, *inner)?;
                tys.intern(TyKind::Slice(inner))
            }
            TyTree::Array(inner, n) => {
                let inner = self.ty(tys, *inner)?;
                let n = tys.intern_const(*n);
                tys.intern(TyKind::Array(inner, n))
            }
            TyTree::Tuple(ts) => {
                let mut out = Vec::with_capacity(ts.len());
                for t in ts {
                    out.push(self.ty(tys, *t)?);
                }
                let id = tys.intern_tys(&out);
                tys.intern(TyKind::Tuple(id))
            }
            TyTree::Adt(def, a) => {
                let a = self.args(tys, a)?;
                tys.intern(TyKind::Adt(*def, a))
            }
            TyTree::FnPtr { count, is_unsafe, extern_c, free_slots, free_region, own_out, out_slots, binders, inputs, output } => {
                let mut out = Vec::with_capacity(inputs.len());
                for t in inputs {
                    out.push(self.ty(tys, *t)?);
                }
                let inputs = tys.intern_tys(&out);
                let output = self.ty(tys, *output)?;
                let sig = tys.intern_sig(Binder { count: *count, value: FnSig { inputs, output, is_unsafe: *is_unsafe, extern_c: *extern_c, free_slots: *free_slots, free_region: *free_region, own_out: *own_out, out_slots: *out_slots, binders: *binders } });
                tys.intern(TyKind::FnPtr(sig))
            }
            TyTree::FnDef(def, a) => {
                let a = self.args(tys, a)?;
                tys.intern(TyKind::FnDef(*def, a))
            }
            TyTree::Closure(def, a) => {
                let a = self.args(tys, a)?;
                tys.intern(TyKind::Closure(*def, a))
            }
            TyTree::Dyn { region, principal, supertraits, auto } => {
                let principal = match principal {
                    Some((count, tr)) => Some(Binder { count: *count, value: self.trait_ref(tys, tr)? }),
                    None => None,
                };
                let mut supers = Vec::with_capacity(supertraits.len());
                for (count, tr) in supertraits {
                    supers.push(Binder { count: *count, value: self.trait_ref(tys, tr)? });
                }
                let bounds = tys.intern_dyn_bounds(DynBounds {
                    principal,
                    supertraits: supers.into_boxed_slice(),
                    auto: AutoTraits { send: auto.0, sync: auto.1, unpin: auto.2, unwind_safe: auto.3, ref_unwind_safe: auto.4 },
                });
                tys.intern(TyKind::Dyn(bounds, *region))
            }
            TyTree::Opaque(def, a) => {
                let a = self.args(tys, a)?;
                tys.intern(TyKind::Opaque(*def, a))
            }
            TyTree::Param(x) => tys.intern(TyKind::Param(*x)),
            TyTree::Projection(assoc, a) => {
                let a = self.args(tys, a)?;
                tys.intern(TyKind::Projection(*assoc, a))
            }
            // Inference variables have no stable reconstruction; a
            // checked body's locals never hold one.
            TyTree::Infer(_) => return None,
        };
        if (i as usize) < self.memo.len() {
            self.memo[i as usize] = Some(t);
        }
        Some(t)
    }
}

fn cache_operand(_b: &mut TreeBuilder, p: &Program, o: &Operand) -> CachedOperand {
    match o {
        Operand::Copy(place) => CachedOperand::Copy(place.clone()),
        Operand::Move(place) => CachedOperand::Move(place.clone()),
        Operand::Const(c) => CachedOperand::Const(match c {
            Const::Int(v, t) => CachedConst::Int(*v, *t),
            Const::Float(v, t) => CachedConst::Float(*v, *t),
            Const::Bool(x) => CachedConst::Bool(*x),
            Const::Char(x) => CachedConst::Char(*x),
            Const::Str(i) => CachedConst::Str(p.ast.strings.get(*i as usize).cloned().unwrap_or_default()),
            Const::Bytes(b) => CachedConst::Bytes(b.as_slice().to_vec()),
            Const::StrBytes(b) => CachedConst::StrBytes(b.as_slice().to_vec()),
            Const::Unit => CachedConst::Unit,
        }),
    }
}

fn cache_fmt(b: &mut TreeBuilder, p: &Program, parts: &[FmtPart]) -> Vec<CachedFmt> {
    parts
        .iter()
        .map(|part| match part {
            FmtPart::Lit(s) => CachedFmt::Lit(s.clone()),
            FmtPart::Arg { value, ty, debug, spec, width, prec } => CachedFmt::Arg {
                value: cache_operand(b, p, value),
                ty: b.ty(*ty),
                debug: *debug,
                spec: *spec,
                width: width.as_ref().map(|o| cache_operand(b, p, o)),
                prec: prec.as_ref().map(|o| cache_operand(b, p, o)),
            },
        })
        .collect()
}

fn cache_rvalue(b: &mut TreeBuilder, p: &Program, r: &Rvalue) -> CachedRvalue {
    let os = |b: &mut TreeBuilder, os: &[Operand]| os.iter().map(|o| cache_operand(b, p, o)).collect::<Vec<_>>();
    match r {
        Rvalue::Use(o) => CachedRvalue::Use(cache_operand(b, p, o)),
        Rvalue::Ref(m, place) => CachedRvalue::Ref(*m, place.clone()),
        Rvalue::Bin(op, a, c) => CachedRvalue::Bin(*op, cache_operand(b, p, a), cache_operand(b, p, c)),
        Rvalue::Un(op, a) => CachedRvalue::Un(*op, cache_operand(b, p, a)),
        Rvalue::Cast(o, t) => CachedRvalue::Cast(cache_operand(b, p, o), b.ty(*t)),
        Rvalue::Aggregate(adt, v, operands) => CachedRvalue::Aggregate(p.def_of_adt(*adt), *v, os(b, operands)),
        Rvalue::Opt(t, o) => CachedRvalue::Opt(b.ty(*t), o.as_ref().map(|o| cache_operand(b, p, o))),
        Rvalue::Res(t, is_ok, o) => CachedRvalue::Res(b.ty(*t), *is_ok, cache_operand(b, p, o)),
        Rvalue::VecLit(t, operands) => CachedRvalue::VecLit(b.ty(*t), os(b, operands)),
        Rvalue::VecRepeat(t, a, c) => CachedRvalue::VecRepeat(b.ty(*t), cache_operand(b, p, a), cache_operand(b, p, c)),
        Rvalue::Eq { a, b: c, ty, ne } => {
            CachedRvalue::Eq { a: cache_operand(b, p, a), b: cache_operand(b, p, c), ty: b.ty(*ty), ne: *ne }
        }
        Rvalue::Cmp { op, a, b: c, ty } => {
            CachedRvalue::Cmp { op: *op, a: cache_operand(b, p, a), b: cache_operand(b, p, c), ty: b.ty(*ty) }
        }
        Rvalue::StrCmp(op, a, c) => CachedRvalue::StrCmp(*op, cache_operand(b, p, a), cache_operand(b, p, c)),
        Rvalue::StringAdd(a, c) => CachedRvalue::StringAdd(cache_operand(b, p, a), cache_operand(b, p, c)),
        Rvalue::Format(parts) => CachedRvalue::Format(cache_fmt(b, p, parts)),
        Rvalue::Discriminant(place) => CachedRvalue::Discriminant(place.clone()),
        Rvalue::TupleAgg(t, operands) => CachedRvalue::TupleAgg(b.ty(*t), os(b, operands)),
        Rvalue::ArrayAgg(t, operands) => CachedRvalue::ArrayAgg(b.ty(*t), os(b, operands)),
        Rvalue::ArrayRepeat(t, o, n) => CachedRvalue::ArrayRepeat(b.ty(*t), cache_operand(b, p, o), *n),
        Rvalue::SliceOf(place) => CachedRvalue::SliceOf(place.clone()),
        Rvalue::Subslice { base, lo, hi, inclusive, mutable } => CachedRvalue::Subslice {
            base: base.clone(),
            lo: cache_operand(b, p, lo),
            hi: hi.as_ref().map(|o| cache_operand(b, p, o)),
            inclusive: *inclusive,
            mutable: *mutable,
        },
        Rvalue::LenOf(place) => CachedRvalue::LenOf(place.clone()),
        Rvalue::StaticLoad(i) => CachedRvalue::StaticLoad(p.static_defs[*i as usize]),
        Rvalue::StaticRef(i) => CachedRvalue::StaticRef(p.static_defs[*i as usize]),
        Rvalue::FnValue(f, t) => CachedRvalue::FnValue(p.disk_id(*f), b.ty(*t)),
        Rvalue::ItemShim(item, t) => CachedRvalue::ItemShim(b.ty(*item), b.ty(*t)),
        Rvalue::MakeDyn { ptr, src, dyn_ty } => CachedRvalue::MakeDyn(cache_operand(b, p, ptr), b.ty(*src), b.ty(*dyn_ty)),
        Rvalue::DynUpcast { ptr, path } => CachedRvalue::DynUpcast(cache_operand(b, p, ptr), path.clone()),
        Rvalue::DynMeta { ptr, word } => CachedRvalue::DynMeta(cache_operand(b, p, ptr), *word),
        Rvalue::DynData { ptr, ty } => CachedRvalue::DynData(cache_operand(b, p, ptr), b.ty(*ty)),
        Rvalue::WriteFmt(dst, parts, stream) => CachedRvalue::WriteFmt(cache_operand(b, p, dst), cache_fmt(b, p, parts), *stream),
        Rvalue::FormatArgs(env, parts) => CachedRvalue::FormatArgs(env.as_ref().map(|e| cache_operand(b, p, e)), cache_fmt(b, p, parts)),
    }
}

/// Translates one lowered body into its cached form. `used_at_gen`
/// pairs each slot its C prints (`FnOut::used`) with that slot's fn.
pub(crate) fn cache_body(p: &Program, body: &Body, file_hash: u64, slot: u32, used_at_gen: Vec<(DiskDefId, u32)>, ir_fp: u64) -> CachedBody {
    let mut b = TreeBuilder { tys: &body.tys, memo: FxMap::default(), out: Vec::new() };
    let locals = body.locals.iter().map(|l| (b.ty(l.ty), l.mutable, l.name.clone())).collect();
    let blocks = body
        .blocks
        .iter()
        .map(|blk| CachedBlock {
            stmts: blk
                .stmts
                .iter()
                .map(|s| CachedStmt {
                    span: s.span,
                    kind: match &s.kind {
                        StmtKind::Assign(place, r) => CachedStmtKind::Assign(place.clone(), cache_rvalue(&mut b, p, r)),
                        StmtKind::Drop(l) => CachedStmtKind::Drop(*l),
                        StmtKind::StorageDead(l) => CachedStmtKind::StorageDead(*l),
                        StmtKind::FakeRead(l) => CachedStmtKind::FakeRead(*l),
                        StmtKind::Print { stderr, newline, parts } => {
                            CachedStmtKind::Print { stderr: *stderr, newline: *newline, parts: cache_fmt(&mut b, p, parts) }
                        }
                    },
                })
                .collect(),
            term: match &blk.term {
                Terminator::Goto(t) => CachedTerm::Goto(*t),
                Terminator::If(o, a, c) => CachedTerm::If(cache_operand(&mut b, p, o), *a, *c),
                Terminator::Switch(o, cases, other) => CachedTerm::Switch(cache_operand(&mut b, p, o), cases.clone(), *other),
                Terminator::Call { target, args, dest, next, unwind } => CachedTerm::Call {
                    target: match target {
                        CallTarget::Fn(f) => CachedTarget::Fn(p.disk_id(*f)),
                        CallTarget::Builtin(x) => CachedTarget::Builtin(*x),
                        CallTarget::Intrinsic(i) => CachedTarget::Intrinsic(*i),
                        CallTarget::Indirect(l) => CachedTarget::Indirect(*l),
                        CallTarget::Dyn(k) => CachedTarget::Dyn(*k),
                    },
                    args: args.iter().map(|a| cache_operand(&mut b, p, a)).collect(),
                    dest: dest.clone(),
                    next: *next,
                    unwind: *unwind,
                },
                Terminator::Return => CachedTerm::Return,
                Terminator::Unreachable => CachedTerm::Unreachable,
                Terminator::MatchExhausted => CachedTerm::MatchExhausted,
                Terminator::Panic(parts) => CachedTerm::Panic(cache_fmt(&mut b, p, parts)),
            },
            term_span: blk.term_span,
        })
        .collect();
    let stmt_unwind = body.stmt_unwind.clone();
    let promoted = body.promoted.clone();
    CachedBody { file_hash, slot_at_gen: slot, used_at_gen, ir_fp, arg_count: body.arg_count, tys: b.out, locals, blocks, stmt_unwind, promoted }
}

/// Rebuilds one cached body against today's program. None when any
/// reference does not resolve (a renamed fn, a missing Adt or
/// static, a string literal the new Ast does not hold): the caller
/// rechecks the fn instead.
pub(crate) fn rebuild<'p>(p: &'p Program, cached: &CachedBody, fn_id: LocalDefId) -> Option<Body<'p>> {
    let mut tys = Tys::new(&p.tys);
    let mut intern = TreeIntern { trees: &cached.tys, memo: vec![None; cached.tys.len()] };
    let mut locals = Vec::with_capacity(cached.locals.len());
    for (ty, mutable, name) in &cached.locals {
        locals.push(LocalDecl { ty: intern.ty(&mut tys, *ty)?, mutable: *mutable, name: name.clone() });
    }
    let mut strings: FxMap<&str, u32> = FxMap::default();
    for (i, s) in p.ast.strings.iter().enumerate() {
        strings.entry(s.as_str()).or_insert(i as u32);
    }
    let local_of = |disk: &DiskDefId| -> Option<LocalDefId> {
        let l = p.local_def(disk.hash)?;
        (p.disk_id(l) == *disk).then_some(l)
    };
    fn operand(
        intern: &mut TreeIntern,
        tys: &mut Tys,
        strings: &FxMap<&str, u32>,
        o: &CachedOperand,
    ) -> Option<Operand> {
        let _ = intern;
        let _ = tys;
        Some(match o {
            CachedOperand::Copy(place) => Operand::Copy(place.clone()),
            CachedOperand::Move(place) => Operand::Move(place.clone()),
            CachedOperand::Const(c) => Operand::Const(match c {
                CachedConst::Int(v, t) => Const::Int(*v, *t),
                CachedConst::Float(v, t) => Const::Float(*v, *t),
                CachedConst::Bool(x) => Const::Bool(*x),
                CachedConst::Char(x) => Const::Char(*x),
                CachedConst::Str(s) => Const::Str(*strings.get(s.as_str())?),
                CachedConst::Bytes(bs) => Const::Bytes(crate::ast::ByteBlob::new(bs.clone())),
                CachedConst::StrBytes(bs) => Const::StrBytes(crate::ast::ByteBlob::new(bs.clone())),
                CachedConst::Unit => Const::Unit,
            }),
        })
    }
    fn fmt(
        intern: &mut TreeIntern,
        tys: &mut Tys,
        strings: &FxMap<&str, u32>,
        parts: &[CachedFmt],
    ) -> Option<Vec<FmtPart>> {
        parts
            .iter()
            .map(|part| match part {
                CachedFmt::Lit(s) => Some(FmtPart::Lit(s.clone())),
                CachedFmt::Arg { value, ty, debug, spec, width, prec } => {
                    let count = |intern: &mut TreeIntern, tys: &mut Tys, c: &Option<CachedOperand>| match c {
                        Some(c) => operand(intern, tys, strings, c).map(Some),
                        None => Some(None),
                    };
                    Some(FmtPart::Arg {
                        value: operand(intern, tys, strings, value)?,
                        ty: intern.ty(tys, *ty)?,
                        debug: *debug,
                        spec: *spec,
                        width: count(intern, tys, width)?,
                        prec: count(intern, tys, prec)?,
                    })
                }
            })
            .collect()
    }
    fn rvalue(
        intern: &mut TreeIntern,
        tys: &mut Tys,
        p: &Program,
        strings: &FxMap<&str, u32>,
        local_of: &dyn Fn(&DiskDefId) -> Option<LocalDefId>,
        r: &CachedRvalue,
    ) -> Option<Rvalue> {
        let os = |intern: &mut TreeIntern, tys: &mut Tys, os: &[CachedOperand]| -> Option<Vec<Operand>> {
            os.iter().map(|o| operand(intern, tys, strings, o)).collect()
        };
        Some(match r {
            CachedRvalue::Use(o) => Rvalue::Use(operand(intern, tys, strings, o)?),
            CachedRvalue::Ref(m, place) => Rvalue::Ref(*m, place.clone()),
            CachedRvalue::Bin(op, a, c) => Rvalue::Bin(*op, operand(intern, tys, strings, a)?, operand(intern, tys, strings, c)?),
            CachedRvalue::Un(op, a) => Rvalue::Un(*op, operand(intern, tys, strings, a)?),
            CachedRvalue::Cast(o, t) => Rvalue::Cast(operand(intern, tys, strings, o)?, intern.ty(tys, *t)?),
            CachedRvalue::Aggregate(def, v, operands) => {
                Rvalue::Aggregate(p.adt_by_def(*def)?, *v, os(intern, tys, operands)?)
            }
            CachedRvalue::Opt(t, o) => {
                Rvalue::Opt(intern.ty(tys, *t)?, match o { Some(o) => Some(operand(intern, tys, strings, o)?), None => None })
            }
            CachedRvalue::Res(t, is_ok, o) => Rvalue::Res(intern.ty(tys, *t)?, *is_ok, operand(intern, tys, strings, o)?),
            CachedRvalue::VecLit(t, operands) => Rvalue::VecLit(intern.ty(tys, *t)?, os(intern, tys, operands)?),
            CachedRvalue::VecRepeat(t, a, c) => {
                Rvalue::VecRepeat(intern.ty(tys, *t)?, operand(intern, tys, strings, a)?, operand(intern, tys, strings, c)?)
            }
            CachedRvalue::Eq { a, b: c, ty, ne } => Rvalue::Eq {
                a: operand(intern, tys, strings, a)?,
                b: operand(intern, tys, strings, c)?,
                ty: intern.ty(tys, *ty)?,
                ne: *ne,
            },
            CachedRvalue::Cmp { op, a, b: c, ty } => Rvalue::Cmp {
                op: *op,
                a: operand(intern, tys, strings, a)?,
                b: operand(intern, tys, strings, c)?,
                ty: intern.ty(tys, *ty)?,
            },
            CachedRvalue::StrCmp(op, a, c) => Rvalue::StrCmp(*op, operand(intern, tys, strings, a)?, operand(intern, tys, strings, c)?),
            CachedRvalue::StringAdd(a, c) => Rvalue::StringAdd(operand(intern, tys, strings, a)?, operand(intern, tys, strings, c)?),
            CachedRvalue::Format(parts) => Rvalue::Format(fmt(intern, tys, strings, parts)?),
            CachedRvalue::Discriminant(place) => Rvalue::Discriminant(place.clone()),
            CachedRvalue::TupleAgg(t, operands) => Rvalue::TupleAgg(intern.ty(tys, *t)?, os(intern, tys, operands)?),
            CachedRvalue::ArrayAgg(t, operands) => Rvalue::ArrayAgg(intern.ty(tys, *t)?, os(intern, tys, operands)?),
            CachedRvalue::ArrayRepeat(t, o, n) => Rvalue::ArrayRepeat(intern.ty(tys, *t)?, operand(intern, tys, strings, o)?, *n),
            CachedRvalue::SliceOf(place) => Rvalue::SliceOf(place.clone()),
            CachedRvalue::Subslice { base, lo, hi, inclusive, mutable } => Rvalue::Subslice {
                base: base.clone(),
                lo: operand(intern, tys, strings, lo)?,
                hi: match hi { Some(o) => Some(operand(intern, tys, strings, o)?), None => None },
                inclusive: *inclusive,
                mutable: *mutable,
            },
            CachedRvalue::LenOf(place) => Rvalue::LenOf(place.clone()),
            CachedRvalue::StaticLoad(def) => Rvalue::StaticLoad(p.static_by_def(*def)?),
            CachedRvalue::StaticRef(def) => Rvalue::StaticRef(p.static_by_def(*def)?),
            CachedRvalue::FnValue(disk, t) => Rvalue::FnValue(local_of(disk)?, intern.ty(tys, *t)?),
            CachedRvalue::ItemShim(item, t) => Rvalue::ItemShim(intern.ty(tys, *item)?, intern.ty(tys, *t)?),
            CachedRvalue::MakeDyn(o, src, dyn_ty) => {
                Rvalue::MakeDyn { ptr: operand(intern, tys, strings, o)?, src: intern.ty(tys, *src)?, dyn_ty: intern.ty(tys, *dyn_ty)? }
            }
            CachedRvalue::DynUpcast(o, path) => Rvalue::DynUpcast { ptr: operand(intern, tys, strings, o)?, path: path.clone() },
            CachedRvalue::DynMeta(o, word) => Rvalue::DynMeta { ptr: operand(intern, tys, strings, o)?, word: *word },
            CachedRvalue::DynData(o, t) => Rvalue::DynData { ptr: operand(intern, tys, strings, o)?, ty: intern.ty(tys, *t)? },
            CachedRvalue::WriteFmt(o, parts, stream) => Rvalue::WriteFmt(operand(intern, tys, strings, o)?, fmt(intern, tys, strings, parts)?, *stream),
            CachedRvalue::FormatArgs(o, parts) => Rvalue::FormatArgs(
                match o {
                    Some(o) => Some(operand(intern, tys, strings, o)?),
                    None => None,
                },
                fmt(intern, tys, strings, parts)?,
            ),
        })
    }
    let mut blocks = Vec::with_capacity(cached.blocks.len());
    for blk in &cached.blocks {
        let mut stmts = Vec::with_capacity(blk.stmts.len());
        for s in &blk.stmts {
            stmts.push(Stmt {
                span: s.span,
                kind: match &s.kind {
                    CachedStmtKind::Assign(place, r) => StmtKind::Assign(place.clone(), rvalue(&mut intern, &mut tys, p, &strings, &local_of, r)?),
                    CachedStmtKind::Drop(l) => StmtKind::Drop(*l),
                    CachedStmtKind::StorageDead(l) => StmtKind::StorageDead(*l),
                    CachedStmtKind::FakeRead(l) => StmtKind::FakeRead(*l),
                    CachedStmtKind::Print { stderr, newline, parts } => {
                        StmtKind::Print { stderr: *stderr, newline: *newline, parts: fmt(&mut intern, &mut tys, &strings, parts)? }
                    }
                },
            });
        }
        let term = match &blk.term {
            CachedTerm::Goto(t) => Terminator::Goto(*t),
            CachedTerm::If(o, a, c) => Terminator::If(operand(&mut intern, &mut tys, &strings, o)?, *a, *c),
            CachedTerm::Switch(o, cases, other) => Terminator::Switch(operand(&mut intern, &mut tys, &strings, o)?, cases.clone(), *other),
            CachedTerm::Call { target, args, dest, next, unwind } => Terminator::Call {
                target: match target {
                    CachedTarget::Fn(disk) => CallTarget::Fn(local_of(disk)?),
                    CachedTarget::Builtin(x) => CallTarget::Builtin(*x),
                    CachedTarget::Intrinsic(i) => CallTarget::Intrinsic(*i),
                    CachedTarget::Indirect(l) => CallTarget::Indirect(*l),
                    CachedTarget::Dyn(k) => CallTarget::Dyn(*k),
                },
                args: args.iter().map(|a| operand(&mut intern, &mut tys, &strings, a)).collect::<Option<Vec<_>>>()?,
                dest: dest.clone(),
                next: *next,
                unwind: *unwind,
            },
            CachedTerm::Return => Terminator::Return,
            CachedTerm::Unreachable => Terminator::Unreachable,
            CachedTerm::MatchExhausted => Terminator::MatchExhausted,
            CachedTerm::Panic(parts) => Terminator::Panic(fmt(&mut intern, &mut tys, &strings, parts)?),
        };
        blocks.push(BlockData { stmts, term, term_span: blk.term_span });
    }
    Some(Body { fn_id, tys, locals, blocks, arg_count: cached.arg_count, reads: graph::Reads::new(), lower_errs: Vec::new(), annotations: Vec::new(), promoted: cached.promoted.clone(), index_exprs: Vec::new(), pat_back_index: Vec::new(), pat_front_index: Vec::new(), pat_subslice: Vec::new(), dyn_coerce: Vec::new(), false_edges: Vec::new(), opaque_locals: Vec::new(), opaque_nodrop: Vec::new(), stmt_unwind: cached.stmt_unwind.clone() })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::{check_fn, collect};
    use crate::def::{CrateIds, LOCAL_CRATE};
    use crate::diag::{FileId, SourceMap};
    use crate::intern::{Interner, Known};
    use crate::{lexer, lower, parser};

    const SRC: &str = "\
struct Foo { x: i64 }
impl Foo { fn get(&self) -> i64 { self.x } }
fn helper(a: i64) -> i64 { a * 2 }
fn seven() -> &'static i64 { &7 }
fn total(v: &Vec<i64>) -> (i64, &'static (u8, char)) { (v.iter().sum(), &(3, 'z')) }
fn main() {
    let f = Foo { x: helper(20) };
    let mut v = Vec::new();
    v.push(f.get() + *seven() - 7);
    println!(\"{} {} {:?}\", v.len(), f.get() + 2, total(&v));
}
";

    fn lowered(src: &str, run: impl FnOnce(&Program, &SourceMap, Vec<Body>)) {
        lowered_with(src, false, run)
    }

    /// `lowered` with `Program::unwind` set as a panic=unwind build sets it.
    fn lowered_with(src: &str, unwind: bool, run: impl FnOnce(&Program, &SourceMap, Vec<Body>)) {
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let mut program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        program.unwind = unwind;
        let mut map = SourceMap::default();
        map.add_file("test.rs", src);
        let bodies = (0..program.fns.len())
            .map(|i| {
                let f = LocalDefId(i as u32);
                let (ck, errs) = check_fn(&program, f);
                assert!(errs.is_empty(), "{errs:?}");
                lower::lower(&program, f, ck)
            })
            .collect();
        run(&program, &map, bodies);
    }

    /// A cached body rebuilds in a fresh program (the next request)
    /// with the same IR fingerprint and byte-identical C under the
    /// same slot assignment, and correct C under a renumbered one
    /// (the fingerprint stands; only slot prints move). Under panic=abort
    /// and panic=unwind: the promoted temps (`seven`'s `&7`, `total`'s
    /// `&(3, 'z')`) and the statement cleanup entries survive the round
    /// trip and the iterator expansion cgen runs first (`total`'s `sum`).
    #[test]
    fn cached_body_rebuilds_with_same_fingerprint_and_c() {
        for unwind in [false, true] {
            let (mut promoted, mut unwinds, mut expanded) = (0, 0, 0);
            lowered_with(SRC, unwind, |p, map, bodies| {
                let slots: Vec<u32> = (0..bodies.len() as u32).collect();
                for (i, body) in bodies.iter().enumerate() {
                    promoted += body.promoted.len();
                    unwinds += body.stmt_unwind.len();
                    for ex in [crate::lower::iter::expand(p, body), crate::lower::tls::expand(p, body)] {
                        if let Ok(Some(x)) = ex {
                            expanded += 1;
                            // It adds cleanup entries for the statements it adds.
                            assert_eq!(x.promoted, body.promoted, "fn {i} expansion keeps the promoted temps");
                            assert!(body.stmt_unwind.iter().all(|e| x.stmt_unwind.contains(e)), "fn {i} expansion keeps the cleanup entries");
                        }
                    }
                    let fp = ir_fingerprint(p, body, map, 1);
                    let used = crate::cgen::gen_fn(p, body, map, 1, &slots).used;
                    let pairs: Vec<(DiskDefId, u32)> = used.iter().map(|&u| (p.disk_id(LocalDefId(u)), u)).collect();
                    let cached = cache_body(p, body, 7, i as u32, pairs, fp);
                    // Rebuild against a fresh collect of the same source.
                    lowered_with(SRC, unwind, |p2, map2, _| {
                        let rebuilt = rebuild(p2, &cached, LocalDefId(i as u32)).expect("rebuild resolves");
                        assert_eq!((&rebuilt.promoted, &rebuilt.stmt_unwind), (&body.promoted, &body.stmt_unwind), "fn {i} round trip keeps them");
                        assert_eq!(ir_fingerprint(p2, &rebuilt, map2, 1), fp, "fn {i} fingerprint survives the round trip");
                        let a = crate::cgen::gen_fn(p, body, map, 1, &slots);
                        let b = crate::cgen::gen_fn(p2, &rebuilt, map2, 1, &slots);
                        assert_eq!(a.code_text(), b.code_text(), "fn {i} C is identical under the same slots");
                        // Renumbered slots: same fingerprint, C differs
                        // only where slot numbers print.
                        let shifted: Vec<u32> = slots.iter().map(|s| s + 10).collect();
                        let c = crate::cgen::gen_fn(p2, &rebuilt, map2, 1, &shifted);
                        assert_eq!(ir_fingerprint(p2, &rebuilt, map2, 1), fp, "fingerprint is slot-free");
                        if a.code_text().contains("lust_fns[") || a.code_text().contains("lust_tramps[") {
                            assert_ne!(a.code_text(), c.code_text(), "fn {i} slot prints move under a renumber");
                        }
                    });
                }
            });
            assert!(promoted >= 2 && expanded >= 1, "the source has promoted temps and an expansion: {promoted} {expanded}");
            assert_eq!(unwinds > 0, unwind, "cleanup entries exist exactly under panic=unwind");
        }
    }

    /// Every builtin payload is part of the fingerprint: these pairs have
    /// the same operand and result types and emit different C (or select
    /// a different std path).
    #[test]
    fn ir_fingerprint_hashes_builtin_payloads() {
        use crate::check::own::Owner;
        use crate::check::sync::SyncOp;
        use crate::ty::sync::SyncTy;
        use Builtin as B;
        let pairs = [
            (B::SliceTrimAscii(0), B::SliceTrimAscii(1)),
            (B::SliceTrimAscii(1), B::SliceTrimAscii(2)),
            (B::SliceSplitEnd(false), B::SliceSplitEnd(true)),
            (B::SliceSplitAt(false), B::SliceSplitAt(true)),
            (B::StrSplitAt(false), B::StrSplitAt(true)),
            (B::SliceStrip(false), B::SliceStrip(true)),
            (B::SliceAsChunks(false), B::SliceAsChunks(true)),
            (B::ParseInt(IntTy::I32), B::ParseInt(IntTy::U32)),
            (B::FromStrRadix(IntTy::I64), B::FromStrRadix(IntTy::U8)),
            (B::ParseFloat(FloatTy::F32), B::ParseFloat(FloatTy::F64)),
            (B::OwnSliceAlloc(Owner::Box), B::OwnSliceAlloc(Owner::Rc)),
            (B::OwnFrom(Owner::Rc), B::OwnFrom(Owner::Arc)),
            (B::Sync(SyncOp::AtomicNew(SyncTy::AtomicBool)), B::Sync(SyncOp::AtomicDefault(SyncTy::AtomicBool))),
            (B::Sync(SyncOp::AtomicLoad), B::Sync(SyncOp::AtomicStore)),
        ];
        lowered(SRC, |p, map, bodies| {
            let (mut body, at) = bodies
                .into_iter()
                .find_map(|b| {
                    let at = b.blocks.iter().position(|blk| matches!(blk.term, Terminator::Call { .. }))?;
                    Some((b, at))
                })
                .expect("a body with a call");
            let mut fp_with = |x: Builtin| {
                let Terminator::Call { target, .. } = &mut body.blocks[at].term else { unreachable!() };
                *target = CallTarget::Builtin(x);
                ir_fingerprint(p, &body, map, 1)
            };
            for (a, b) in pairs {
                assert_ne!(fp_with(a), fp_with(b), "{a:?} and {b:?} hash apart");
            }
        });
    }

    /// The fingerprint tracks body content and layout, not positions:
    /// a body edit and a field edit move it; blank lines above the fn
    /// (whole-fn move) do not.
    #[test]
    fn ir_fingerprint_tracks_content_not_position() {
        let fp_of = |src: &str| -> Vec<u64> {
            let mut out = Vec::new();
            lowered(src, |p, map, bodies| {
                // base_line 0 with absolute lines would move with the
                // fn; the driver passes the fn's own line. Mirror it
                // per body through the name span line.
                out = bodies
                    .iter()
                    .map(|b| {
                        let line = map.line_col(p.fn_def(b.fn_id).name_span).0;
                        ir_fingerprint(p, b, map, line)
                    })
                    .collect();
            });
            out
        };
        let base = fp_of(SRC);
        assert_eq!(base, fp_of(&format!("\n\n{SRC}")), "whole-fn moves keep fingerprints");
        assert_ne!(base, fp_of(&SRC.replace("a * 2", "a * 3")), "body edit moves the fingerprint");
        let field = SRC.replace("struct Foo { x: i64 }", "struct Foo { x: i64, y: u8 }").replace("Foo { x: helper(20) }", "Foo { x: helper(20), y: 0 }");
        assert_ne!(base, fp_of(&field), "layout edit moves fingerprints");
        // Derive lists left the layout (sigedit P3.3): a body whose lowering
        // reads one (Copy moves, glue calls) changes its MIR, and a build
        // after a derive edit regenerates every body (`build_derives_moved`).
        assert_eq!(base, fp_of(&SRC.replace("struct Foo { x: i64 }", "#[derive(Clone)]\nstruct Foo { x: i64 }")), "an unused derive keeps fingerprints");
    }

    /// `#[track_caller]` changes the fn's C signature and its panic
    /// locations, and every direct call passes one more argument: adding
    /// it moves the fn's fingerprint and its caller's (a warm daemon
    /// reused both units before).
    #[test]
    fn ir_fingerprint_tracks_track_caller() {
        // A plain panic: this helper compiles without the std splice, so
        // std's (source) `Option::unwrap` is not there.
        const TC: &str = "fn g(x: u8) -> u8 {\n    if x == 0 {\n        panic!(\"zero\");\n    }\n    x\n}\nfn main() {\n    println!(\"{}\", g(0));\n}\n";
        let fp_of = |src: &str| -> Vec<(String, u64)> {
            let mut out = Vec::new();
            lowered(src, |p, map, bodies| {
                out = bodies
                    .iter()
                    .map(|b| {
                        let def = &p.fn_def(b.fn_id);
                        (p.name(def.name).to_string(), ir_fingerprint(p, b, map, map.line_col(def.name_span).0))
                    })
                    .collect();
            });
            out
        };
        let (base, tc) = (fp_of(TC), fp_of(&format!("#[track_caller]\n{TC}")));
        for name in ["g", "main"] {
            let get = |v: &[(String, u64)]| v.iter().find(|(n, _)| n == name).map(|x| x.1);
            assert!(get(&base).is_some(), "{name} is lowered");
            assert_ne!(get(&base), get(&tc), "#[track_caller] on g moves {name}'s fingerprint");
        }
    }

    /// `FnOut::used` holds every slot a fn's C prints: the daemon's
    /// slot-moved re-emit and dead-callee checks read it. The IR-only
    /// list it replaced missed closures an adapter chain calls through
    /// `closure_call_c` (fx-unitcache). Builds one program with adapter
    /// chains, a generic fn taking a closure, a fn pointer, a `dyn` call,
    /// and `sort_by_key`, then checks each fn's C against its list.
    #[test]
    fn fn_out_used_covers_every_printed_slot() {
        use crate::driver::compile::compile;
        use crate::driver::session::Session;
        use crate::protocol::{Cmd, Request, SessionKey};
        let dir = std::env::temp_dir().join(format!("lust-used-slots-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("used.rs");
        std::fs::write(
            &file,
            "trait Area {\n    fn area(&self) -> u64;\n}\nstruct Sq(u64);\nimpl Area for Sq {\n    fn area(&self) -> u64 {\n        self.0 * self.0\n    }\n}\n\
             fn apply<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 {\n    f(x)\n}\nfn twice(x: u64) -> u64 {\n    x * 2\n}\n\
             fn main() {\n    let v: Vec<u32> = (1..=9).collect();\n\
             \x20   let n = v.iter().copied().inspect(|x| if *x < 2 { println!(\"pull {x}\") }).skip(1).filter(|x| *x % 3 != 0).map(|x| x * 7).count();\n\
             \x20   let fp: fn(u64) -> u64 = twice;\n    let d: Box<dyn Area> = Box::new(Sq(3));\n\
             \x20   let mut s = v.clone();\n    s.sort_by_key(|x| (*x * 5) % 4);\n\
             \x20   println!(\"{n} {} {} {} {s:?}\", apply(|x| x + 1, 4), fp(5), d.area());\n}\n",
        )
        .unwrap();
        let key = SessionKey::synthetic(&file, false);
        let req = Request {
            cmd: Cmd::Build,
            file: key.krate.root.clone(),
            session: key.clone(),
            out: dir.join("used.bin"),
            json: false,
            timings: false,
            debug: false,
            emit_c: None,
            max_errors: 20,
            run_args: None,
            harness: false, cc: false,
            client: Default::default(),
        };
        let mut s = Session::new(dir.join("obj"), false, key);
        let r = compile(&req, &mut s);
        assert_eq!(r.code, 0, "{}", r.stderr);
        for (slot, out) in s.caches.out.iter().enumerate() {
            for table in ["lust_fns[", "lust_tramps["] {
                let code = out.code_text();
                for (at, _) in code.match_indices(table) {
                    let digits: String = code[at + table.len()..].chars().take_while(|c| c.is_ascii_digit()).collect();
                    let printed: u32 = digits.parse().unwrap();
                    assert!(out.used.binary_search(&printed).is_ok(), "slot {slot} prints {table}{printed}] but its used list is {:?}", out.used);
                }
            }
        }
        // main prints its own slot, the adapter closures, the sort key
        // closure, `apply`'s instance, `twice`'s trampoline, and a shim.
        let most = s.caches.out.iter().map(|o| o.used.len()).max();
        assert!(most >= Some(7), "main prints the slots of the fns it reaches: {most:?}");
        let _ = std::fs::remove_dir_all(&dir);
    }
}
