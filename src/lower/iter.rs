// Expansion of the iterator builtins into plain IR (W-STD-A phase 3,
// ty/iter.rs).
//
// Check and borrowck see each iterator method as one builtin call
// (check/iter.rs). Codegen calls `expand` first, so every such call
// becomes ordinary IR: closure body calls, switches on `Option`, slice
// places, and explicit drops, with Rust 1.99's semantics per kind (pull
// order, early exits, drop points, `size_hint`, and `collect`'s
// capacity rules). It runs after borrowck on purpose: borrowck checks
// the call's summary (its args and result), which covers everything
// the expansion does, and the places the expansion makes are not user
// borrows.
//
// Every `emit_*` function starts in `self.cur` and leaves `self.cur`
// at the block that follows the value it wrote.
use crate::check::Builtin;
use crate::check::closure::ClosureKind;
use crate::check::collect::{Program, is_copy};
use crate::diag::Span;
use crate::ir::*;
use crate::ty::iter::{self as it, IterKind};
use crate::ty::*;

mod char_range;
mod range_from;
mod splice;

type R = Result<(), String>;

/// How many references wrap `t` (`&&T` is 2).
fn ref_depth(tys: &Tys, mut t: Ty) -> usize {
    let mut n = 0;
    while let TyKind::Ref(_, _, inner) = tys.kind(t) {
        n += 1;
        t = inner;
    }
    n
}

/// True for the builtins this pass rewrites. `IterVecIntoIter` and
/// the `vec::IntoIter` element moves stay calls: codegen emits them.
pub(crate) fn expands(b: Builtin) -> bool {
    use Builtin as B;
    matches!(
        b,
        B::IterIter
            | B::IterIterMut
            | B::IterNext
            | B::IterNextBack
            | B::IterSizeHint
            | B::IterLen
            | B::RangeStartBound
            | B::RangeEndBound
            | B::BoundAsRef
            | B::BoundMap
            | B::BoundCloned
            | B::RangeIsEmpty
            | B::RangeContains
            | B::VecResizeWith
            | B::VecSplice
            | B::RangeInclStart
            | B::RangeInclEnd
            | B::IterMap
            | B::IterFilter
            | B::IterFilterMap
            | B::IterMapWhile
            | B::IterEnumerate
            | B::IterRev
            | B::IterTake
            | B::IterSkip
            | B::IterStepBy
            | B::IterChain
            | B::IterZip
            | B::IterCopied
            | B::IterCloned
            | B::IterTakeWhile
            | B::IterSkipWhile
            | B::IterPeekable
            | B::IterPeek
            | B::IterNextIf
            | B::IterNextIfEq
            | B::IterInspect
            | B::IterCount
            | B::IterEq
            | B::IterNe
            | B::IterLast
            | B::IterNth
            | B::IterAny
            | B::IterAll
            | B::IterFind
            | B::IterFindMap
            | B::IterPosition
            | B::IterRposition
            | B::IterWindows
            | B::IterChunks
            | B::IterSliceSplit
            | B::IterChunkBy
            | B::IterUtf8Chunks
            | B::IterRemainder
            | B::IterNextBack
            | B::StrCharIndices
            | B::StrBytes
            | B::EntryOrInsertWith
            | B::EntryOrInsertWithKey
            | B::EntryAndModify
            | B::IterFlatten
            | B::IterFlattenInto
            | B::IterFlatMap
            | B::HashFromArray
            | B::DlEntries
            | B::DmEntries
            | B::StrSplit
            | B::StrMatches
            | B::StrEncodeUtf16
            | B::StrParse
            | B::IterSizeHint
            | B::IterFold
            | B::IterTryFold
            | B::IterForEach
            | B::IterPartition
            | B::IterUnzip
            | B::IterMin
            | B::IterMax
            | B::IterMinByKey
            | B::IterMaxByKey
            | B::IterCollect
            | B::FromIter
            | B::IterSum
            | B::IterProduct
            | B::HashExtend
            | B::VecExtend
            | B::StringExtend
            | B::IterArrayIntoIter
            | B::ArrayIterAsSlice
            | B::IterRepeatN
            | B::SliceJoinBorrow
            | B::SliceConcatBorrow
            | B::SliceCloneFromWritten
            | B::ArrayFromFn
            | B::ArrayMap
            | B::IterOptRes
            | B::IterLen
            | B::ConvInto
    )
}

/// The body with every iterator builtin call expanded, or None when it
/// has none (the common case: no copy is made).
pub fn expand<'g>(p: &Program, body: &Body<'g>) -> Result<Option<Body<'g>>, String> {
    let has = body.blocks.iter().any(|b| matches!(b.term, Terminator::Call { target: CallTarget::Builtin(x), .. } if expands(x)));
    if !has {
        return Ok(None);
    }
    let copy = Body {
        fn_id: body.fn_id,
        tys: body.tys.clone(),
        locals: body.locals.clone(),
        blocks: body.blocks.clone(),
        arg_count: body.arg_count,
        reads: Default::default(),
        lower_errs: Vec::new(),
        annotations: Vec::new(),
        // cgen gives these static storage: a reference to one may escape.
        promoted: body.promoted.clone(),
        index_exprs: Vec::new(),
        pat_back_index: Vec::new(),
        pat_front_index: Vec::new(),
        pat_subslice: Vec::new(),
        dyn_coerce: Vec::new(),
        false_edges: Vec::new(),
        opaque_locals: Vec::new(),
        opaque_nodrop: Vec::new(),
        stmt_unwind: body.stmt_unwind.clone(),
    };
    let mut ex = Ex { p, body: copy, cur: Bb(0), span: Span::default(), fold: false, unw: None, shim_line: 166 };
    let n = ex.body.blocks.len();
    for b in 0..n {
        let Terminator::Call { target: CallTarget::Builtin(x), .. } = ex.body.blocks[b].term else { continue };
        if !expands(x) {
            continue;
        }
        let term = std::mem::replace(&mut ex.body.blocks[b].term, Terminator::Unreachable);
        let Terminator::Call { args, dest, next, unwind, .. } = term else { unreachable!() };
        ex.cur = Bb(b as u32);
        ex.span = ex.body.blocks[b].term_span;
        ex.unw = unwind;
        ex.builtin(x, args, dest)?;
        ex.goto(next);
    }
    Ok(Some(ex.body))
}

struct Ex<'b, 'g> {
    p: &'b Program,
    body: Body<'g>,
    cur: Bb,
    span: Span,
    /// The pull is a step of std's `try_fold`, not `next`: `find`,
    /// `position`, `any`, `all`, `find_map` on a borrowed iterator,
    /// core's `advance_by`, and the inner pulls of Filter, FilterMap,
    /// and SkipWhile (their `next` is a `find`). Take and Skip then step
    /// as their `try_fold` does (`next_in`).
    fold: bool,
    /// The expanded call's cleanup successor: every call and statement
    /// of its expansion that can unwind continues there (panic=unwind).
    unw: Option<Bb>,
    /// The core/src/ops/function.rs line of the Fn trait method a
    /// primitive method item's shim runs in (`call_fn`): `call_mut`
    /// (166) for an adapter's `FnMut` bound, `call` (79) behind a `&`.
    shim_line: u32,
}

impl Ex<'_, '_> {
    // ---------- IR building ----------

    fn local(&mut self, ty: Ty) -> Local {
        self.body.locals.push(LocalDecl { ty, mutable: true, name: None });
        let l = self.body.locals.len() as Local - 1;
        // panic=unwind: a local of the expansion that owns droppable data
        // (a `vec::IntoIter`, a collected Vec) drops in the cleanup of
        // everything after it, before the expanded call's own cleanup.
        // The drop is flag-guarded, so it is a no-op until the local holds
        // a value and after it moved out.
        if let Some(next) = self.unw.filter(|_| self.p.unwind)
            && crate::check::collect::needs_drop(self.p, &self.body.tys, ty)
        {
            let span = self.span;
            self.body.blocks.push(BlockData { stmts: vec![Stmt { kind: StmtKind::Drop(l), span }], term: Terminator::Goto(next), term_span: span });
            self.unw = Some(Bb(self.body.blocks.len() as u32 - 1));
        }
        l
    }
    fn block(&mut self) -> Bb {
        self.body.blocks.push(BlockData { stmts: Vec::new(), term: Terminator::Unreachable, term_span: self.span });
        Bb(self.body.blocks.len() as u32 - 1)
    }
    fn push(&mut self, kind: StmtKind) {
        let span = self.span;
        let unwinds = !matches!(kind, StmtKind::StorageDead(_) | StmtKind::FakeRead(_));
        let stmts = &mut self.body.blocks[self.cur.0 as usize].stmts;
        stmts.push(Stmt { kind, span });
        if let Some(u) = self.unw.filter(|_| unwinds && self.p.unwind) {
            let n = stmts.len() as u32 - 1;
            self.body.stmt_unwind.push((self.cur, n, u));
        }
    }
    fn assign(&mut self, pl: Place, rv: Rvalue) {
        self.push(StmtKind::Assign(pl, rv));
    }
    fn drop_local(&mut self, l: Local) {
        self.push(StmtKind::Drop(l));
    }
    fn term(&mut self, t: Terminator) {
        if let Some(u) = self.unw.filter(|_| self.p.unwind && matches!(t, Terminator::Panic(_))) {
            let n = self.body.blocks[self.cur.0 as usize].stmts.len() as u32;
            self.body.stmt_unwind.push((self.cur, n, u));
        }
        let b = &mut self.body.blocks[self.cur.0 as usize];
        b.term = t;
        b.term_span = self.span;
    }
    fn goto(&mut self, b: Bb) {
        self.term(Terminator::Goto(b));
    }
    /// Ends the current block with a call and continues after it.
    fn call(&mut self, target: CallTarget, args: Vec<Operand>, dest: Place) {
        let next = self.block();
        self.term(Terminator::Call { target, args, dest, next, unwind: self.unw });
        self.cur = next;
    }
    fn call_builtin(&mut self, b: Builtin, args: Vec<Operand>, dest: Place) {
        self.call(CallTarget::Builtin(b), args, dest);
    }
    /// Ends the current block on a bool and returns (then, else).
    fn branch(&mut self, cond: Operand) -> (Bb, Bb) {
        let (t, f) = (self.block(), self.block());
        self.term(Terminator::If(cond, t, f));
        (t, f)
    }
    /// Ends the current block on an `Option` place: (some, none).
    fn switch_opt(&mut self, opt: &Place) -> (Bb, Bb) {
        let d = self.local(int(IntTy::U32));
        self.assign(Place::local(d), Rvalue::Discriminant(opt.clone()));
        let (s, n) = (self.block(), self.block());
        self.term(Terminator::Switch(Operand::Copy(Place::local(d)), vec![(1, s)], n));
        (s, n)
    }
    fn payload(opt: &Place) -> Place {
        opt.project(Proj::Downcast(1)).project(Proj::Field(0))
    }
    fn usize_c(n: u64) -> Operand {
        Operand::Const(Const::Int(n as u128, IntTy::Usize))
    }
    fn u32_c(n: u32) -> Operand {
        Operand::Const(Const::Int(n as u128, IntTy::U32))
    }
    /// A copy or a move of a place, by its type.
    fn take(&self, pl: Place, ty: Ty) -> Operand {
        if is_copy(self.p, &self.body.tys, ty) { Operand::Copy(pl) } else { Operand::Move(pl) }
    }
    /// A new bool local holding `a op b`.
    fn cmp(&mut self, op: crate::ast::BinOp, a: Operand, b: Operand) -> Operand {
        let c = self.local(BOOL);
        self.assign(Place::local(c), Rvalue::Bin(op, a, b));
        Operand::Copy(Place::local(c))
    }
    /// A new reference local to a place.
    fn ref_to(&mut self, mutable: bool, pl: Place, ty: Ty) -> Local {
        let rt = self.body.tys.mk_ref(mutable, ty);
        let r = self.local(rt);
        self.assign(Place::local(r), Rvalue::Ref(mutable, pl));
        r
    }
    /// `dest = mem::replace(&mut *pl, None)`: an `Option::take` on a
    /// place inside an iterator. A move out of the place plus an
    /// assign of `None` would drop the moved-out value twice: drop
    /// elaboration cannot track partial moves through a deref, so the
    /// assign still drops the old contents.
    fn take_none(&mut self, pl: Place, ty: Ty, dest: Place) {
        let nl = self.local(ty);
        self.none(&Place::local(nl), ty);
        let r = self.ref_to(true, pl, ty);
        self.call_builtin(Builtin::MemReplace, vec![Operand::Move(Place::local(r)), Operand::Move(Place::local(nl))], dest);
    }
    fn some(&mut self, dest: &Place, opt_ty: Ty, v: Operand) {
        self.assign(dest.clone(), Rvalue::Opt(opt_ty, Some(v)));
    }
    fn none(&mut self, dest: &Place, opt_ty: Ty) {
        self.assign(dest.clone(), Rvalue::Opt(opt_ty, None));
    }
    fn tuple_ty(&mut self, ts: &[Ty]) -> Ty {
        let id = self.body.tys.intern_tys(ts);
        self.body.tys.intern(TyKind::Tuple(id))
    }

    // ---------- Types ----------

    fn place_ty(&mut self, pl: &Place) -> Result<Ty, String> {
        let mut t = self.body.locals[pl.local as usize].ty;
        let mut variant: Option<u32> = None;
        for pr in &pl.proj {
            let tys = &mut self.body.tys;
            t = match *pr {
                Proj::Deref => match tys.kind(t) {
                    TyKind::Ref(_, _, i) => i,
                    _ => tys.smart_elem(t).ok_or("iterator expansion: deref of a non-pointer place")?,
                },
                Proj::Downcast(v) => {
                    variant = Some(v);
                    continue;
                }
                Proj::Field(i) => {
                    let v = variant.take();
                    if let Some(e) = tys.option_elem(t) {
                        e
                    } else if let Some((a, b)) = tys.result_args(t) {
                        if v == Some(1) { b } else { a }
                    } else if let TyKind::Tuple(ts) = tys.kind(t) {
                        tys.tys_of(ts)[i as usize]
                    } else if let Some(fs) = it::field_tys(tys, t) {
                        fs[i as usize]
                    } else if let TyKind::Closure(_, a) = tys.kind(t) {
                        crate::check::collect::closure_fields(tys, a)[i as usize]
                    } else if let Some(a) = tys.local_adt(t) {
                        self.p.adt(a).variants[v.unwrap_or(0) as usize].fields[i as usize].ty
                    } else {
                        return Err("iterator expansion: field of an unknown place type".into());
                    }
                }
                Proj::Index(_) => match tys.kind(t) {
                    TyKind::Slice(e) | TyKind::Array(e, _) => e,
                    _ => tys.vec_elem(t).ok_or("iterator expansion: index of a non-sequence place")?,
                },
            };
        }
        Ok(t)
    }

    fn op_ty(&mut self, o: &Operand) -> Result<Ty, String> {
        match o {
            Operand::Copy(pl) | Operand::Move(pl) => self.place_ty(pl),
            Operand::Const(Const::Int(_, i)) => Ok(int(*i)),
            Operand::Const(Const::Bool(_)) => Ok(BOOL),
            Operand::Const(Const::Char(_)) => Ok(CHAR),
            Operand::Const(Const::Unit) => Ok(UNIT),
            // A string literal (a `"..".into()` receiver, W-STD-B).
            Operand::Const(Const::Str(_)) => Ok(REF_STR),
            Operand::Const(Const::StrBytes(_)) => Ok(REF_STR),
            Operand::Const(_) => Err("iterator expansion: unexpected constant operand".into()),
        }
    }

    fn item(&mut self, ty: Ty) -> Result<Ty, String> {
        it::item_ty(&mut self.body.tys, ty).ok_or_else(|| "iterator expansion: no item type".into())
    }

    fn kind_args(&self, ty: Ty) -> Option<(IterKind, Vec<Ty>)> {
        it::iter_parts(&self.body.tys, ty)
    }

    /// The place an operand names, moved into a fresh local first when
    /// it is a constant (no iterator is).
    fn op_place(&mut self, o: Operand, ty: Ty) -> Place {
        match o {
            Operand::Copy(pl) | Operand::Move(pl) => pl,
            c => {
                let l = self.local(ty);
                self.assign(Place::local(l), Rvalue::Use(c));
                Place::local(l)
            }
        }
    }

    // ---------- Callables ----------

    /// `dest = f(args..)` for the closure value at `f_place` (type
    /// `f_ty`), called through `FnMut`: the env goes by `&` for an
    /// `Fn` closure and by `&mut` for an `FnMut` one.
    fn call_fn(&mut self, f_ty: Ty, f_place: Place, args: Vec<Operand>, dest: Place) -> R {
        // A reference to a callable (`fold(0, &u32::div_euclid)`, `&c`):
        // core's `impl FnMut for &F` calls `F::call`, and `&mut F`
        // calls `F::call_mut`.
        if let TyKind::Ref(_, m, inner) = self.body.tys.kind(f_ty) {
            let line = if m.is_mut() { 166 } else { 79 };
            let saved = std::mem::replace(&mut self.shim_line, line);
            let r = self.call_fn(inner, f_place.deref(), args, dest);
            self.shim_line = saved;
            return r;
        }
        // A box around a callable calls what it holds (`impl FnMut for
        // Box<F>`); a `dyn Fn` or `dyn FnMut` value calls its vtable's call
        // entry through a reference, as a call of the value does
        // (check/closure.rs). Check rejects a `dyn FnOnce` here.
        if let Some(inner) = self.body.tys.boxed_elem(f_ty) {
            return self.call_fn(inner, f_place.deref(), args, dest);
        }
        if let Some(pr) = crate::check::object::principal_of(&self.body.tys, f_ty) {
            let lang = &self.p.gx.lang;
            if pr.def != lang.fn_ && pr.def != lang.fn_mut {
                return Err("iterator expansion: a `dyn FnOnce` behind an FnMut bound".into());
            }
            let r = self.ref_to(pr.def == lang.fn_mut, f_place, f_ty);
            let mut ops = vec![Operand::Move(Place::local(r))];
            ops.extend(args);
            self.call(CallTarget::Dyn(crate::check::object::VT_HEADER), ops, dest);
            return Ok(());
        }
        // A fn pointer, fn item, or tuple constructor (W-CHECK-G): a plain
        // call, as `Ctx::callable_res` resolves a call of the value.
        match self.body.tys.kind(f_ty) {
            TyKind::FnPtr(_) => {
                let l = self.local(f_ty);
                self.assign(Place::local(l), Rvalue::Use(Operand::Copy(f_place)));
                self.call(CallTarget::Indirect(l), args, dest);
                return Ok(());
            }
            TyKind::FnDef(def, fargs) => {
                // `Some`, `Ok`, or `Err` as the callable (`.map(Some)`):
                // the variant comes from the const arg, as below.
                // `Box::new`, `Rc::new`, and `String::from` call their
                // builtin (`Ctx::builtin_item_value`).
                let b = self.body.tys.builtins();
                let (option, result) = (b.option, b.result);
                let builtin = [(b.boxed, Builtin::BoxNew), (b.rc, Builtin::RcNew), (b.string, Builtin::StringFrom)];
                if def == option || def == result {
                    let ty = self.place_ty(&dest)?;
                    let ok = matches!(self.body.tys.args(fargs).first(), Some(GenericArg::Const(c)) if matches!(self.body.tys.const_kind(*c), ConstKind::Int(0)));
                    let op = args.into_iter().next().ok_or("iterator expansion: a constructor call takes one argument")?;
                    let rv = if def == option { Rvalue::Opt(ty, Some(op)) } else { Rvalue::Res(ty, ok, op) };
                    self.assign(dest, rv);
                    return Ok(());
                }
                if let Some(&(_, bf)) = builtin.iter().find(|(d, _)| *d == def) {
                    // `String::as_str` shares the String def: its item
                    // const is 1 (check `builtin_item_value`, tf-str).
                    let bf = if def == b.string
                        && matches!(self.body.tys.args(fargs).first(), Some(GenericArg::Const(c)) if matches!(self.body.tys.const_kind(*c), ConstKind::Int(1)))
                    {
                        Builtin::StringAsStr
                    } else {
                        bf
                    };
                    self.call(CallTarget::Builtin(bf), args, dest);
                    return Ok(());
                }
                // A primitive builtin method item
                // (`take_while(u8::is_ascii_digit)`, TRIAGE T12):
                // its `FnDef` args carry the builtin code third
                // (`prim_item_value`).
                if def == crate::ty::prim_fn_def() {
                    let code = match self.body.tys.args(fargs).get(2) {
                        Some(GenericArg::Const(c)) => match self.body.tys.const_kind(*c) {
                            ConstKind::Int(v) => v as u32,
                            _ => u32::MAX,
                        },
                        _ => u32::MAX,
                    };
                    if let Some(bf) = crate::check::prim_builtin_of_code(code) {
                        if bf == Builtin::PrimFromCast {
                            let ty = self.place_ty(&dest)?;
                            let op = args.into_iter().next().ok_or("iterator expansion: a conversion takes one argument")?;
                            self.assign(dest, Rvalue::Cast(op, ty));
                            return Ok(());
                        }
                        // The adapters call it as `FnMut::call_mut` (or
                        // `call` behind a `&`, `shim_line`): a
                        // `#[track_caller]` panic reports that shim's
                        // line in core/src/ops/function.rs, as rustc's
                        // fn item shim does.
                        let saved = std::mem::replace(&mut self.span, Span::std_site(15, self.shim_line, 5));
                        self.call(CallTarget::Builtin(bf), args, dest);
                        self.span = saved;
                        return Ok(());
                    }
                }
                if let Some(a) = self.p.adt_by_def(def) {
                    let v = match self.body.tys.args(fargs).first() {
                        Some(GenericArg::Const(c)) => match self.body.tys.const_kind(*c) {
                            ConstKind::Int(v) => v as u32,
                            _ => 0,
                        },
                        _ => 0,
                    };
                    // A generic Adt builds its mono instance (the dest's type).
                    let a = self.place_ty(&dest).ok().and_then(|t| self.body.tys.local_adt(t)).unwrap_or(a);
                    self.assign(dest, Rvalue::Aggregate(a, v, args));
                    return Ok(());
                }
                // A trait fn value check left as a builtin marker
                // (check/traitpath.rs): the FnDef names the trait
                // method, and the call expands by the trait.
                if def == crate::check::generics::to_string_defs().1 {
                    self.call(CallTarget::Builtin(Builtin::ToString), args, dest);
                    return Ok(());
                }
                if let Some(tdef) = self.p.gx.index.trait_of_method(def) {
                    let lang = &self.p.gx.lang;
                    if tdef == lang.from || tdef == lang.into {
                        let dest_ty = self.place_ty(&dest)?;
                        let x = args.into_iter().next().ok_or("iterator expansion: a conversion takes one argument")?;
                        let src = self.op_ty(&x)?;
                        return if crate::check::convert::std_from(self.p, &self.body.tys, dest_ty, src).is_some() {
                            self.conv(x, dest, dest_ty)
                        } else {
                            // A numeric widening `From`: a cast.
                            self.assign(dest, Rvalue::Cast(x, dest_ty));
                            Ok(())
                        };
                    }
                    if tdef == lang.clone {
                        self.call(CallTarget::Builtin(Builtin::Clone), args, dest);
                        return Ok(());
                    }
                    if tdef == lang.default {
                        let dest_ty = self.place_ty(&dest)?;
                        match self.body.tys.kind(dest_ty) {
                            TyKind::Int(it) => self.assign(dest, Rvalue::Use(Operand::Const(Const::Int(0, it)))),
                            TyKind::Bool => self.assign(dest, Rvalue::Use(Operand::Const(Const::Bool(false)))),
                            TyKind::Char => self.assign(dest, Rvalue::Use(Operand::Const(Const::Char('\0')))),
                            TyKind::Unit => self.assign(dest, Rvalue::Use(Operand::Const(Const::Unit))),
                            TyKind::Float(f) => self.assign(dest, Rvalue::Use(Operand::Const(Const::Float(0, f)))),
                            _ => self.call(CallTarget::Builtin(Builtin::DefaultGlue), Vec::new(), dest),
                        }
                        return Ok(());
                    }
                    if self.p.gx.index.trait_record(tdef).is_some_and(|r| self.p.interner.get(r.name) == "ToString") {
                        self.call(CallTarget::Builtin(Builtin::ToString), args, dest);
                        return Ok(());
                    }
                }
                let f = self.p.local_def(def.hash).ok_or("iterator expansion: fn item not found")?;
                let gargs: Vec<GenericArg> = self.body.tys.args(fargs).to_vec();
                let f = if gargs.is_empty() {
                    f
                } else {
                    crate::check::generics::instance_for(self.p, &self.body.tys, f, &gargs)
                        .ok_or("iterator expansion: no instance of the fn item")?
                };
                self.call(CallTarget::Fn(f), args, dest);
                return Ok(());
            }
            _ => {}
        }
        let TyKind::Closure(def, _) = self.body.tys.kind(f_ty) else {
            return Err("iterator expansion: the callable is not a closure".into());
        };
        let Some(entry) = self.p.gx.closures.get(&def) else {
            return Err("iterator expansion: closure body not registered".into());
        };
        let (body_fn, kind) = (entry.body_fn, entry.kind);
        let env = match kind {
            ClosureKind::Fn => self.ref_to(false, f_place, f_ty),
            ClosureKind::FnMut => self.ref_to(true, f_place, f_ty),
            ClosureKind::FnOnce => return Err("iterator expansion: an FnOnce closure behind an FnMut bound".into()),
        };
        let mut ops = vec![Operand::Move(Place::local(env))];
        ops.extend(args);
        self.call(CallTarget::Fn(body_fn), ops, dest);
        Ok(())
    }

    /// `dest = f(args..)` through `FnOnce::call_once` for the callable in
    /// local `f`: an `FnOnce` closure moves in; any other callable goes by
    /// `call_fn` and drops right after the call, as `call_once` does.
    fn call_fn_once(&mut self, fty: Ty, f: Local, args: Vec<Operand>, dest: Place) -> R {
        if let TyKind::Closure(def, _) = self.body.tys.kind(fty)
            && let Some(entry) = self.p.gx.closures.get(&def)
            && entry.kind == ClosureKind::FnOnce
        {
            let body_fn = entry.body_fn;
            let mut ops = vec![Operand::Move(Place::local(f))];
            ops.extend(args);
            self.call(CallTarget::Fn(body_fn), ops, dest);
            return Ok(());
        }
        self.call_fn(fty, Place::local(f), args, dest)?;
        self.drop_local(f);
        Ok(())
    }

    // ---------- Builtin calls ----------

    fn builtin(&mut self, b: Builtin, args: Vec<Operand>, dest: Place) -> R {
        use Builtin as B;
        let dest_ty = self.place_ty(&dest)?;
        let mut args = args.into_iter();
        let mut arg = || args.next().ok_or_else(|| "iterator expansion: missing argument".to_string());
        match b {
            B::ConvInto => {
                let x = arg()?;
                return self.conv(x, dest, dest_ty);
            }
            B::SliceJoinBorrow | B::SliceConcatBorrow => {
                let r = arg()?;
                let sep = if b == B::SliceJoinBorrow { Some(arg()?) } else { None };
                let f = arg()?;
                return self.join_borrow(r, sep, f, dest);
            }
            B::SliceCloneFromWritten => {
                let (d, s, f) = (arg()?, arg()?, arg()?);
                return self.clone_from_written(d, s, f, dest);
            }
            // `slice.windows(size)` (W-STD-B): std's `NonZero::new(size).expect(..)`
            // panic first, then (the whole slice, size).
            B::IterWindows => {
                let (r, n) = (arg()?, arg()?);
                let nl = self.local(USIZE);
                self.assign(Place::local(nl), Rvalue::Use(n));
                let c = self.cmp(crate::ast::BinOp::Eq, Operand::Copy(Place::local(nl)), Self::usize_c(0));
                let (zero, go) = self.branch(c);
                self.cur = zero;
                self.term(Terminator::Panic(vec![FmtPart::Lit("window size must be non-zero".into())]));
                self.cur = go;
                let rt = self.op_ty(&r)?;
                let rp = self.op_place(r, rt);
                let fields = it::field_tys(&mut self.body.tys, dest_ty).ok_or("iterator expansion: bad windows iterator")?;
                let s = self.local(fields[0]);
                self.assign(Place::local(s), Rvalue::SliceOf(rp.deref()));
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(s)), Operand::Copy(Place::local(nl))]));
            }
            // `slice.chunks(size)` and kin (tf-slice): std's
            // `assert_ne!(size, 0)`-through-`NonZero` panic first,
            // then the stored fields. The exact forms split the
            // remainder off at creation, as std does.
            // A slice split: (v, pred, finished, count) as core's
            // constructors set them (`SplitInclusive` starts finished on
            // an empty slice; the N forms take the count first).
            B::IterSliceSplit => {
                use crate::ty::iter::SliceSplitMode as M;
                let r = arg()?;
                let (_, a) = self.kind_args(dest_ty).ok_or("iterator expansion: bad slice split")?;
                let mode = it::slice_split_mode(&self.body.tys, a[2]).ok_or("iterator expansion: bad slice split mode")?;
                let count = if matches!(mode, M::SplitN | M::RSplitN) { arg()? } else { Self::usize_c(0) };
                let pred = arg()?;
                let rt = self.op_ty(&r)?;
                let rp = self.op_place(r, rt);
                let fields = it::field_tys(&mut self.body.tys, dest_ty).ok_or("iterator expansion: bad slice split")?;
                let s = self.local(fields[0]);
                self.assign(Place::local(s), Rvalue::SliceOf(rp.deref()));
                let finished = if mode == M::SplitInclusive {
                    let len = self.local(USIZE);
                    self.assign(Place::local(len), Rvalue::LenOf(Place::local(s).deref()));
                    self.cmp(crate::ast::BinOp::Eq, Operand::Copy(Place::local(len)), Self::usize_c(0))
                } else {
                    Operand::Const(Const::Bool(false))
                };
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(s)), pred, finished, count]));
            }
            B::IterChunkBy => {
                let (r, pred) = (arg()?, arg()?);
                let rt = self.op_ty(&r)?;
                let rp = self.op_place(r, rt);
                let fields = it::field_tys(&mut self.body.tys, dest_ty).ok_or("iterator expansion: bad chunk_by")?;
                let s = self.local(fields[0]);
                self.assign(Place::local(s), Rvalue::SliceOf(rp.deref()));
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(s)), pred]));
            }
            B::IterChunks => {
                let (r, n) = (arg()?, arg()?);
                let nl = self.local(USIZE);
                self.assign(Place::local(nl), Rvalue::Use(n));
                let c = self.cmp(crate::ast::BinOp::Eq, Operand::Copy(Place::local(nl)), Self::usize_c(0));
                let (zero, go) = self.branch(c);
                self.cur = zero;
                self.term(Terminator::Panic(vec![FmtPart::Lit("chunk size must be non-zero".into())]));
                self.cur = go;
                let (k, _) = self.kind_args(dest_ty).ok_or("iterator expansion: bad chunks iterator")?;
                let m = matches!(k, IterKind::ChunksMut | IterKind::ChunksExactMut);
                let rt = self.op_ty(&r)?;
                let rp = self.op_place(r, rt);
                let fields = it::field_tys(&mut self.body.tys, dest_ty).ok_or("iterator expansion: bad chunks iterator")?;
                let s = self.local(fields[0]);
                self.assign(Place::local(s), Rvalue::SliceOf(rp.deref()));
                if matches!(k, IterKind::ChunksExact | IterKind::ChunksExactMut) {
                    let sd = Place::local(s).deref();
                    let len = self.local(USIZE);
                    self.assign(Place::local(len), Rvalue::LenOf(sd.clone()));
                    let rem = self.local(USIZE);
                    self.assign(
                        Place::local(rem),
                        Rvalue::Bin(crate::ast::BinOp::Rem, Operand::Copy(Place::local(len)), Operand::Copy(Place::local(nl))),
                    );
                    let fst_len = self.local(USIZE);
                    self.assign(
                        Place::local(fst_len),
                        Rvalue::Bin(crate::ast::BinOp::Sub, Operand::Copy(Place::local(len)), Operand::Copy(Place::local(rem))),
                    );
                    let (fst, snd) = (self.local(fields[0]), self.local(fields[1]));
                    self.assign(
                        Place::local(fst),
                        Rvalue::Subslice {
                            base: sd.clone(),
                            lo: Self::usize_c(0),
                            hi: Some(Operand::Copy(Place::local(fst_len))),
                            inclusive: false,
                            mutable: m,
                        },
                    );
                    self.assign(
                        Place::local(snd),
                        Rvalue::Subslice {
                            base: sd,
                            lo: Operand::Copy(Place::local(fst_len)),
                            hi: None,
                            inclusive: false,
                            mutable: m,
                        },
                    );
                    self.assign(
                        dest,
                        Rvalue::TupleAgg(
                            dest_ty,
                            vec![Operand::Move(Place::local(fst)), Operand::Move(Place::local(snd)), Operand::Copy(Place::local(nl))],
                        ),
                    );
                } else {
                    self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(s)), Operand::Copy(Place::local(nl))]));
                }
            }
            // `[u8]::utf8_chunks` (tf-slice): the source bytes, whole.
            B::IterUtf8Chunks => {
                let r = arg()?;
                let rt = self.op_ty(&r)?;
                let rp = self.op_place(r, rt);
                let fields = it::field_tys(&mut self.body.tys, dest_ty).ok_or("iterator expansion: bad utf8_chunks iterator")?;
                let s = self.local(fields[0]);
                self.assign(Place::local(s), Rvalue::SliceOf(rp.deref()));
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(s))]));
            }
            // `ChunksExact::remainder` and
            // `ChunksExactMut::into_remainder` (tf-slice): field 1,
            // through the reference or by value.
            B::IterRemainder => {
                let r = arg()?;
                let rt = self.op_ty(&r)?;
                let rp = self.op_place(r, rt);
                let base = match self.body.tys.kind(rt) {
                    TyKind::Ref(..) => rp.deref(),
                    _ => rp,
                };
                self.assign(dest, Rvalue::Use(Operand::Copy(base.project(Proj::Field(1)))));
            }
            B::IterIter | B::IterIterMut => {
                let r = arg()?;
                let rt = self.op_ty(&r)?;
                let rp = self.op_place(r, rt);
                let fields = it::field_tys(&mut self.body.tys, dest_ty).ok_or("iterator expansion: bad slice iterator")?;
                let s = self.local(fields[0]);
                self.assign(Place::local(s), Rvalue::SliceOf(rp.deref()));
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(s))]));
            }
            B::IterMap | B::IterFilter | B::IterFilterMap | B::IterMapWhile | B::IterInspect => {
                let (i, f) = (self.unwrap_op(arg()?)?, arg()?);
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i, f]));
            }
            B::IterEnumerate => {
                let i = self.unwrap_op(arg()?)?;
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i, Self::usize_c(0)]));
            }
            B::IterRev | B::IterCopied | B::IterCloned => {
                let i = self.unwrap_op(arg()?)?;
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i]));
            }
            B::IterTake | B::IterSkip => {
                let (i, n) = (self.unwrap_op(arg()?)?, arg()?);
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i, n]));
            }
            B::IterTakeWhile | B::IterSkipWhile => {
                let (i, p) = (self.unwrap_op(arg()?)?, arg()?);
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i, Operand::Const(Const::Bool(false)), p]));
            }
            B::IterPeekable => {
                let i = self.unwrap_op(arg()?)?;
                let fields = it::field_tys(&mut self.body.tys, dest_ty).ok_or("iterator expansion: bad Peekable")?;
                let slot = self.local(fields[1]);
                self.none(&Place::local(slot), fields[1]);
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i, Operand::Move(Place::local(slot))]));
            }
            B::IterStepBy => {
                let (i, n) = (self.unwrap_op(arg()?)?, arg()?);
                // `assert!(step != 0)`, then `step_minus_one`.
                let ok = self.cmp(crate::ast::BinOp::Ne, n.clone(), Self::usize_c(0));
                let (good, bad) = self.branch(ok);
                self.cur = bad;
                self.term(Terminator::Panic(vec![FmtPart::Lit("assertion failed: step != 0".into())]));
                // `StepBy::new` asserts in core, not at the caller.
                self.body.blocks[self.cur.0 as usize].term_span = crate::diag::Span::std_site(5, 36, 9);
                self.cur = good;
                let m = self.local(USIZE);
                self.assign(Place::local(m), Rvalue::Bin(crate::ast::BinOp::Sub, n, Self::usize_c(1)));
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![i, Operand::Copy(Place::local(m)), Operand::Const(Const::Bool(true))]));
            }
            B::IterChain => {
                let (a, other) = (self.unwrap_op(arg()?)?, arg()?);
                let fields = it::field_tys(&mut self.body.tys, dest_ty).ok_or("iterator expansion: bad Chain")?;
                let (_, targs) = self.kind_args(dest_ty).ok_or("iterator expansion: bad Chain")?;
                let bv = self.into_iter(other, targs[1])?;
                let (oa, ob) = (self.local(fields[0]), self.local(fields[1]));
                self.some(&Place::local(oa), fields[0], a);
                self.some(&Place::local(ob), fields[1], bv);
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(oa)), Operand::Move(Place::local(ob))]));
            }
            B::IterZip => {
                let (a, other) = (self.unwrap_op(arg()?)?, arg()?);
                let (_, targs) = self.kind_args(dest_ty).ok_or("iterator expansion: bad Zip")?;
                let bv = self.into_iter(other, targs[1])?;
                let (al, bl) = (self.local(targs[0]), self.local(targs[1]));
                self.assign(Place::local(al), Rvalue::Use(a));
                self.assign(Place::local(bl), Rvalue::Use(bv));
                // Both sides random access: the length is fixed now
                // (Rust's `ZipImpl::new` for `TrustedRandomAccess`).
                let len = self.local(USIZE);
                if self.tra(targs[0]) && self.tra(targs[1]) {
                    let x = self.size(Place::local(al), targs[0])?;
                    let y = self.size(Place::local(bl), targs[1])?;
                    self.call_builtin(B::Min, vec![x, y], Place::local(len));
                } else {
                    self.assign(Place::local(len), Rvalue::Use(Self::usize_c(0)));
                }
                self.assign(
                    dest,
                    Rvalue::TupleAgg(
                        dest_ty,
                        vec![Operand::Move(Place::local(al)), Operand::Move(Place::local(bl)), Self::usize_c(0), Operand::Copy(Place::local(len))],
                    ),
                );
            }
            B::IterSizeHint => {
                let r = arg()?;
                let (itp, ty) = self.deref_arg(r)?;
                let (itp, ty) = self.user_iter(itp, ty)?;
                let (lo, hi) = self.hint(itp, ty)?;
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Copy(Place::local(lo)), Operand::Move(Place::local(hi))]));
            }
            // `iter`, `iter_mut`, and `into_iter` on `Option` and
            // `Result` (fx-option-rest): the dest kind drives the
            // conversion (`make_opt_res`).
            B::IterOptRes => {
                let r = arg()?;
                self.make_opt_res(r, dest_ty, dest)?;
            }
            B::IterNext | B::IterNextBack => {
                let r = arg()?;
                let (itp, ty) = self.deref_arg(r)?;
                self.next(itp, ty, dest, b == B::IterNextBack)?;
            }
            B::IterLen => {
                let r = arg()?;
                let (itp, ty) = self.deref_arg(r)?;
                let (itp, ty) = self.user_iter(itp, ty)?;
                let (lo, hi) = self.hint(itp, ty)?;
                // std's default `ExactSizeIterator::len` asserts the
                // hint is exact. The builtin kinds are exact by
                // construction; a user iterator's `size_hint` need
                // not be, so a `ByNext` at the core gets the assert.
                if self.len_asserts(ty) {
                    let ou = self.body.tys.mk_option(USIZE);
                    let right = self.local(ou);
                    self.some(&Place::local(right), ou, Operand::Copy(Place::local(lo)));
                    let (some_b, none_b) = self.switch_opt(&Place::local(hi));
                    let join = self.block();
                    self.cur = none_b;
                    self.exact_len_panic(hi, right, ou);
                    self.cur = some_b;
                    let eq = self.cmp(crate::ast::BinOp::Eq, Operand::Copy(Self::payload(&Place::local(hi))), Operand::Copy(Place::local(lo)));
                    let (good, bad) = self.branch(eq);
                    self.cur = bad;
                    self.exact_len_panic(hi, right, ou);
                    self.cur = good;
                    self.goto(join);
                    self.cur = join;
                }
                self.assign(dest, Rvalue::Use(Operand::Copy(Place::local(lo))));
            }
            // `array::IntoIter::as_slice` and `as_mut_slice`
            // (fx-array-iter): the stored array's remaining range.
            B::ArrayIterAsSlice => {
                let r = arg()?;
                let (itp, _ty) = self.deref_arg(r)?;
                let m = matches!(self.body.tys.kind(dest_ty), TyKind::Ref(_, Mut::Mut, _));
                let f = |i: u32| itp.project(Proj::Field(i));
                self.assign(
                    dest,
                    Rvalue::Subslice { base: f(0), lo: Operand::Copy(f(1)), hi: Some(Operand::Copy(f(2))), inclusive: false, mutable: m },
                );
            }
            B::RangeStartBound | B::RangeEndBound => {
                let r = arg()?;
                let (itp, ty) = self.deref_arg(r)?;
                self.range_bound(itp, ty, dest, dest_ty, b == B::RangeStartBound)?;
            }
            // The Entry closure forms (W-STD-B): the closure runs only on
            // the branch std runs it on (vacant for the `or_insert_with`
            // forms, occupied for `and_modify`).
            B::EntryOrInsertWith | B::EntryOrInsertWithKey | B::EntryAndModify => {
                let (en, f) = (arg()?, arg()?);
                let ety = self.op_ty(&en)?;
                let el = self.local(ety);
                self.assign(Place::local(el), Rvalue::Use(en));
                let fty = self.op_ty(&f)?;
                let fl = self.local(fty);
                self.assign(Place::local(fl), Rvalue::Use(f));
                let r = self.ref_to(false, Place::local(el), ety);
                let occ = self.local(BOOL);
                self.call_builtin(Builtin::EntryOccupied, vec![Operand::Move(Place::local(r))], Place::local(occ));
                let (yes, no) = self.branch(Operand::Copy(Place::local(occ)));
                let join = self.block();
                let vr_ty = if b == B::EntryAndModify { None } else { Some(dest_ty) };
                let (_, kv) = crate::ty::hash::hash_parts(&self.body.tys, ety).ok_or("entry expansion: not an Entry")?;
                self.cur = yes;
                match vr_ty {
                    Some(_) => self.call_builtin(Builtin::EntryIntoMut, vec![Operand::Move(Place::local(el))], dest.clone()),
                    None => {
                        let rv_ty = self.body.tys.mk_ref(true, kv[1]);
                        let rm = self.ref_to(true, Place::local(el), ety);
                        let rv = self.local(rv_ty);
                        self.call_builtin(Builtin::EntryGetMut, vec![Operand::Move(Place::local(rm))], Place::local(rv));
                        let u = self.local(UNIT);
                        self.call_fn_once(fty, fl, vec![Operand::Move(Place::local(rv))], Place::local(u))?;
                        self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(el))));
                    }
                }
                if vr_ty.is_some() {
                    self.drop_local(fl);
                }
                self.goto(join);
                self.cur = no;
                match vr_ty {
                    Some(_) => {
                        let v = self.local(kv[1]);
                        let fargs = if b == B::EntryOrInsertWithKey {
                            let kr_ty = self.body.tys.mk_ref(false, kv[0]);
                            let rk = self.ref_to(false, Place::local(el), ety);
                            let k = self.local(kr_ty);
                            self.call_builtin(Builtin::EntryKey, vec![Operand::Move(Place::local(rk))], Place::local(k));
                            vec![Operand::Copy(Place::local(k))]
                        } else {
                            Vec::new()
                        };
                        self.call_fn_once(fty, fl, fargs, Place::local(v))?;
                        self.call_builtin(Builtin::EntryInsert, vec![Operand::Move(Place::local(el)), Operand::Move(Place::local(v))], dest);
                    }
                    None => {
                        self.assign(dest, Rvalue::Use(Operand::Move(Place::local(el))));
                        self.drop_local(fl);
                    }
                }
                self.goto(join);
                self.cur = join;
                return Ok(());
            }
            // A str split iterator (W-STD-B, check/split.rs): the runtime's
            // state over the receiver's `&str` (runtime/core.c
            // `lust_split`), then the pattern; the whitespace and line
            // modes have none (a placeholder char).
            B::StrSplit => {
                use it::SplitMode as M;
                let s = arg()?;
                let st = self.op_ty(&s)?;
                let hay = match self.body.tys.kind(st) {
                    TyKind::Ref(_, _, i) if self.body.tys.is_string_ty(i) => {
                        let v = self.local(REF_STR);
                        self.call_builtin(Builtin::StringAsStr, vec![s], Place::local(v));
                        Operand::Copy(Place::local(v))
                    }
                    _ => s,
                };
                let (_, a) = self.kind_args(dest_ty).ok_or("iterator expansion: bad split iterator")?;
                let mode = it::split_mode(&self.body.tys, a[1]).ok_or("iterator expansion: bad split mode")?;
                let (count, pat) = match mode {
                    M::SplitN | M::RSplitN => (arg()?, arg()?),
                    M::SplitWhitespace | M::SplitAsciiWhitespace | M::Lines => (Self::usize_c(0), Operand::Const(Const::Char('\n'))),
                    _ => (Self::usize_c(0), arg()?),
                };
                let hl = self.local(REF_STR);
                self.assign(Place::local(hl), Rvalue::Use(hay));
                let len = self.local(USIZE);
                self.call_builtin(Builtin::StrLen, vec![Operand::Copy(Place::local(hl))], Place::local(len));
                // MATCH_FW 4 and MATCH_BW 8 (the empty needle's first step
                // matches), and TRAILING 2 for the splits that keep a
                // trailing empty piece.
                let trailing = matches!(mode, M::Split | M::RSplit | M::SplitN | M::RSplitN | M::SplitWhitespace | M::SplitAsciiWhitespace);
                let flags = 12 + if trailing { 2 } else { 0 };
                let fields = vec![
                    Operand::Copy(Place::local(hl)),
                    Self::usize_c(0),
                    Operand::Copy(Place::local(len)),
                    Self::usize_c(0),
                    Operand::Copy(Place::local(len)),
                    Self::usize_c(flags),
                    count,
                    pat,
                ];
                self.assign(dest, Rvalue::TupleAgg(dest_ty, fields));
            }
            // `entries(iter)` on a Debug builder (W-STD-B): an `entry`
            // per item, each formatted and then dropped, as std loops.
            B::DlEntries | B::DmEntries => {
                let (r, src) = (arg()?, arg()?);
                let st = self.op_ty(&src)?;
                let want = it::as_iter_ty(&mut self.body.tys, st).ok_or("iterator expansion: bad entries argument")?;
                let iv = self.into_iter(src, want)?;
                let (owned, ty) = self.own(iv)?;
                let rt = self.op_ty(&r)?;
                let rl = self.local(rt);
                self.assign(Place::local(rl), Rvalue::Use(r));
                let map = b == B::DmEntries;
                self.each(&Place::local(owned), ty, &mut |this, x, item| {
                    let mut args = vec![Operand::Copy(Place::local(rl))];
                    if map {
                        let parts: Vec<Ty> = match this.body.tys.kind(item) {
                            TyKind::Tuple(ts) => this.body.tys.tys_of(ts).to_vec(),
                            _ => return Err("iterator expansion: map entries of a non-pair".into()),
                        };
                        for (i, t) in parts.into_iter().enumerate() {
                            let r = this.ref_to(false, Place::local(x).project(Proj::Field(i as u32)), t);
                            args.push(Operand::Move(Place::local(r)));
                        }
                    } else {
                        let r = this.ref_to(false, Place::local(x), item);
                        args.push(Operand::Move(Place::local(r)));
                    }
                    let u = this.local(rt);
                    this.call_builtin(if map { B::DmEntry } else { B::DlEntry }, args, Place::local(u));
                    this.drop_local(x);
                    Ok(())
                })?;
                self.drop_local(owned);
                self.assign(dest, Rvalue::Use(Operand::Copy(Place::local(rl))));
            }
            // `HashMap::from(array)` (W-STD-B): `from_iter`, so
            // `with_hasher(Default::default())` and `extend` from the
            // array's `array::IntoIter`.
            B::HashFromArray => {
                let x = arg()?;
                let at = self.op_ty(&x)?;
                let TyKind::Array(el, _) = self.body.tys.kind(at) else { return Err("hash expansion: from of a non-array".into()) };
                let it_ty = it::mk_iter(&mut self.body.tys, IterKind::ArrayIntoIter, &[el, at]);
                let io = self.into_iter(x, it_ty)?;
                let il = self.local(it_ty);
                self.assign(Place::local(il), Rvalue::Use(io));
                let m = self.local(dest_ty);
                self.call_builtin(Builtin::HashDefault, vec![], Place::local(m));
                let rt = self.body.tys.mk_ref(true, dest_ty);
                let rm = self.local(rt);
                self.assign(Place::local(rm), Rvalue::Ref(true, Place::local(m)));
                self.hash_extend(Place::local(il), it_ty, rm)?;
                self.assign(dest, Rvalue::Use(Operand::Move(Place::local(m))));
            }
            // `flatten()` and `flat_map(f)` (W-STD-B): (Some(iter), None,
            // None); flat_map's iter is `Map<I, F>`.
            B::IterFlatten | B::IterFlatMap | B::IterFlattenInto => {
                let i = self.unwrap_op(arg()?)?;
                let (_, fa) = self.kind_args(dest_ty).ok_or("iterator expansion: bad flatten iterator")?;
                let inner = if b == B::IterFlatten {
                    i
                } else {
                    // `IterFlattenInto`'s `into_iter` fn item is zero-sized.
                    let f = if b == B::IterFlatMap { arg()? } else { Operand::Const(Const::Unit) };
                    let m = self.local(fa[0]);
                    self.assign(Place::local(m), Rvalue::TupleAgg(fa[0], vec![i, f]));
                    Operand::Move(Place::local(m))
                };
                let fields = it::field_tys(&mut self.body.tys, dest_ty).ok_or("iterator expansion: bad flatten iterator")?;
                let (o, s) = (self.local(fields[0]), self.local(fields[1]));
                self.some(&Place::local(o), fields[0], inner);
                self.none(&Place::local(s), fields[1]);
                let s2 = self.local(fields[2]);
                self.none(&Place::local(s2), fields[2]);
                self.assign(
                    dest,
                    Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(o)), Operand::Move(Place::local(s)), Operand::Move(Place::local(s2))]),
                );
            }
            // A str matches iterator (tf-str, check/split.rs): the
            // split family's runtime state over the receiver's `&str`
            // with no trailing piece, then the pattern.
            B::StrMatches => {
                let s = arg()?;
                let st = self.op_ty(&s)?;
                let hay = match self.body.tys.kind(st) {
                    TyKind::Ref(_, _, i) if self.body.tys.is_string_ty(i) => {
                        let v = self.local(REF_STR);
                        self.call_builtin(Builtin::StringAsStr, vec![s], Place::local(v));
                        Operand::Copy(Place::local(v))
                    }
                    _ => s,
                };
                let pat = arg()?;
                let hl = self.local(REF_STR);
                self.assign(Place::local(hl), Rvalue::Use(hay));
                let len = self.local(USIZE);
                self.call_builtin(Builtin::StrLen, vec![Operand::Copy(Place::local(hl))], Place::local(len));
                let fields = vec![
                    Operand::Copy(Place::local(hl)),
                    Self::usize_c(0),
                    Operand::Copy(Place::local(len)),
                    Self::usize_c(0),
                    Operand::Copy(Place::local(len)),
                    Self::usize_c(12),
                    Self::usize_c(0),
                    pat,
                ];
                self.assign(dest, Rvalue::TupleAgg(dest_ty, fields));
            }
            // `s.encode_utf16()` (tf-str): (s.chars(), 0), with the
            // second field the buffered low surrogate (0 for none).
            B::StrEncodeUtf16 => {
                let s = arg()?;
                let c = self.local(CHARS);
                self.call_builtin(Builtin::StrChars, vec![s], Place::local(c));
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(c)), Self::usize_c(0)]));
            }
            // `s.parse::<T>()` (tf-str): by the target type, the
            // primitive runtime parsers or the written `FromStr`
            // impl's `from_str` (check/iter.rs `from_str_fn`).
            B::StrParse => {
                let s = arg()?;
                let st = self.op_ty(&s)?;
                let hay = match self.body.tys.kind(st) {
                    TyKind::Ref(_, _, i) if self.body.tys.is_string_ty(i) => {
                        let v = self.local(REF_STR);
                        self.call_builtin(Builtin::StringAsStr, vec![s], Place::local(v));
                        Operand::Copy(Place::local(v))
                    }
                    _ => s,
                };
                let (tgt, _) = self.body.tys.result_args(dest_ty).ok_or("parse expansion: not a Result")?;
                match self.body.tys.kind(tgt) {
                    TyKind::Int(it) => self.call_builtin(Builtin::ParseInt(it), vec![hay], dest),
                    TyKind::Float(f) => self.call_builtin(Builtin::ParseFloat(f), vec![hay], dest),
                    TyKind::Bool => self.call_builtin(Builtin::ParseBool, vec![hay], dest),
                    TyKind::Char => self.call_builtin(Builtin::ParseChar, vec![hay], dest),
                    _ if self.body.tys.is_string_ty(tgt) => {
                        let v = self.local(STRING);
                        self.call_builtin(Builtin::StringFrom, vec![hay], Place::local(v));
                        self.assign(dest, Rvalue::Res(dest_ty, true, Operand::Move(Place::local(v))));
                    }
                    _ => {
                        let f = crate::check::iter::from_str_fn(self.p, &self.body.tys, tgt)?;
                        self.call(CallTarget::Fn(f), vec![hay], dest);
                    }
                }
            }
            // `s.char_indices()` (W-STD-B): (s.chars(), 0), as std builds it.
            B::StrCharIndices => {
                let s = arg()?;
                let c = self.local(CHARS);
                self.call_builtin(Builtin::StrChars, vec![s], Place::local(c));
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(c)), Self::usize_c(0)]));
            }
            // `s.bytes()`: std's `Bytes` is `Copied<slice::Iter<u8>>` over
            // `s.as_bytes()`.
            B::StrBytes => {
                let s = arg()?;
                // A String receiver (`String::bytes` through Deref) gives
                // its `&str` first.
                let st = self.op_ty(&s)?;
                let s = match self.body.tys.kind(st) {
                    TyKind::Ref(_, _, i) if self.body.tys.is_string_ty(i) => {
                        let v = self.local(REF_STR);
                        self.call_builtin(Builtin::StringAsStr, vec![s], Place::local(v));
                        Operand::Copy(Place::local(v))
                    }
                    _ => s,
                };
                let (_, inner) = self.kind_args(dest_ty).ok_or("iterator expansion: bad bytes iterator")?;
                let fields = it::field_tys(&mut self.body.tys, inner[0]).ok_or("iterator expansion: bad bytes iterator")?;
                let v = self.local(fields[0]);
                self.call_builtin(Builtin::ConvStrBytes, vec![s], Place::local(v));
                let si = self.local(inner[0]);
                self.assign(Place::local(si), Rvalue::TupleAgg(inner[0], vec![Operand::Move(Place::local(v))]));
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(si))]));
            }
            B::BoundAsRef | B::BoundCloned => {
                let r = arg()?;
                let (itp, ty) = if b == B::BoundAsRef {
                    self.deref_arg(r)?
                } else {
                    let (l, ty) = self.own(r)?;
                    (Place::local(l), ty)
                };
                self.bound_map_like(b, itp, ty, None, dest, dest_ty)?;
            }
            // `Vec::resize_with(n, f)` (tf-small-a, R4): alloc's
            // `extend_trusted(repeat_with(f).take(n - len))` (one
            // `reserve`, then `f()` per element) or `truncate(n)`; `f`
            // drops last. Any callable: closure, fn item, fn pointer.
            B::VecResizeWith => {
                use crate::ast::BinOp::{Gt, Lt, Sub};
                let (v, n, f) = (arg()?, arg()?, arg()?);
                let vt = self.op_ty(&v)?;
                let elem = match self.body.tys.kind(vt) {
                    TyKind::Ref(_, _, vv) => self.body.tys.vec_elem(vv),
                    _ => None,
                }
                .ok_or("resize_with expansion: receiver is not a Vec reference")?;
                let vl = self.copy_local(v, vt);
                let nl = self.copy_local(n, USIZE);
                let fty = self.op_ty(&f)?;
                let fl = self.copy_local(f, fty);
                let rv = || Operand::Copy(Place::local(vl));
                let len = self.local(USIZE);
                self.call_builtin(Builtin::VecLen, vec![rv()], Place::local(len));
                let grow = self.cmp(Gt, Operand::Copy(Place::local(nl)), Operand::Copy(Place::local(len)));
                let (g, shrink) = self.branch(grow);
                let join = self.block();
                self.cur = shrink;
                let u = self.local(UNIT);
                self.call_builtin(Builtin::VecTruncate, vec![rv(), Operand::Copy(Place::local(nl))], Place::local(u));
                self.goto(join);
                self.cur = g;
                let add = self.local(USIZE);
                self.assign(Place::local(add), Rvalue::Bin(Sub, Operand::Copy(Place::local(nl)), Operand::Copy(Place::local(len))));
                self.call_builtin(Builtin::VecReserve, vec![rv(), Operand::Copy(Place::local(add))], Place::local(u));
                let lp = self.block();
                self.goto(lp);
                self.cur = lp;
                let now = self.local(USIZE);
                self.call_builtin(Builtin::VecLen, vec![rv()], Place::local(now));
                let more = self.cmp(Lt, Operand::Copy(Place::local(now)), Operand::Copy(Place::local(nl)));
                let (body, done) = self.branch(more);
                self.cur = done;
                self.goto(join);
                self.cur = body;
                let x = self.local(elem);
                self.call_fn(fty, Place::local(fl), Vec::new(), Place::local(x))?;
                self.call_builtin(Builtin::VecPush, vec![rv(), Operand::Move(Place::local(x))], Place::local(u));
                self.goto(lp);
                self.cur = join;
                self.drop_local(fl);
                self.assign(dest, Rvalue::Use(Operand::Const(Const::Unit)));
            }
            B::VecSplice => {
                let (v, st, sv, et, ev, rw) = (arg()?, arg()?, arg()?, arg()?, arg()?, arg()?);
                self.splice(v, [st, sv, et, ev], rw)?;
                self.assign(dest, Rvalue::Use(Operand::Const(Const::Unit)));
            }
            B::RangeIsEmpty | B::RangeInclStart | B::RangeInclEnd => {
                let r = arg()?;
                let (itp, ty) = self.deref_arg(r)?;
                self.range_query(b, itp, ty, None, dest)?;
            }
            B::RangeContains => {
                let (r, x) = (arg()?, arg()?);
                let (itp, ty) = self.deref_arg(r)?;
                let xt = self.op_ty(&x)?;
                let xp = self.op_place(x, xt);
                self.range_query(b, itp, ty, Some(xp.deref()), dest)?;
            }
            B::BoundMap => {
                let (r, f) = (arg()?, arg()?);
                let (l, ty) = self.own(r)?;
                let fty = self.op_ty(&f)?;
                let fl = self.local(fty);
                self.assign(Place::local(fl), Rvalue::Use(f));
                self.bound_map_like(b, Place::local(l), ty, Some((Place::local(fl), fty)), dest, dest_ty)?;
                self.drop_local(fl);
            }
            B::IterPeek => {
                let r = arg()?;
                let (itp, ty) = self.deref_arg(r)?;
                self.peek(itp, ty, dest, dest_ty)?;
            }
            B::IterNextIf | B::IterNextIfEq => {
                let (r, f) = (arg()?, arg()?);
                let (itp, ty) = self.deref_arg(r)?;
                self.next_if(b == B::IterNextIfEq, itp, ty, f, dest, dest_ty)?;
            }
            B::IterNth => {
                let (r, n) = (arg()?, arg()?);
                let (itp, ty) = self.deref_arg(r)?;
                let (itp, ty) = self.user_iter(itp, ty)?;
                let nl = self.local(USIZE);
                self.assign(Place::local(nl), Rvalue::Use(n));
                self.nth(itp, ty, nl, dest)?;
            }
            B::IterAny | B::IterAll | B::IterFind | B::IterFindMap | B::IterPosition | B::IterRposition => {
                let (r, f) = (arg()?, arg()?);
                let (itp, ty) = self.deref_arg(r)?;
                let (itp, ty) = self.user_iter(itp, ty)?;
                let fty = self.op_ty(&f)?;
                let fl = self.local(fty);
                self.assign(Place::local(fl), Rvalue::Use(f));
                if b == B::IterRposition {
                    self.rposition(itp, ty, Place::local(fl), fty, dest, dest_ty)?;
                } else {
                    self.search(b, itp, ty, Place::local(fl), fty, dest, dest_ty)?;
                }
                self.drop_local(fl);
            }
            // `Type::from_iter(src)` (fx-fromiter): `src` through
            // `IntoIterator`, then the `collect` expansion, as
            // `Iterator::collect` is `FromIterator::from_iter`.
            B::FromIter => {
                let src = arg()?;
                let st = self.op_ty(&src)?;
                let want = self
                    .wrapper_inner(st)
                    .or_else(|| it::as_iter_ty(&mut self.body.tys, st))
                    .ok_or("iterator expansion: bad `from_iter` argument")?;
                let iv = self.into_iter(src, want)?;
                let (owned, ty) = self.own(iv)?;
                self.collect(Place::local(owned), ty, dest, dest_ty)?;
                self.drop_local(owned);
            }
            B::IterEq | B::IterNe => {
                let (a, other) = (arg()?, arg()?);
                let (al, at) = self.own(a)?;
                let ot = self.op_ty(&other)?;
                let want = if it::is_iter(&self.body.tys, ot) {
                    ot
                } else {
                    self.wrapper_inner(ot).or_else(|| it::as_iter_ty(&mut self.body.tys, ot)).ok_or("iterator expansion: bad `eq` argument")?
                };
                let bv = self.into_iter(other, want)?;
                let bl = self.local(want);
                self.assign(Place::local(bl), Rvalue::Use(bv));
                self.iter_eq(Place::local(al), at, Place::local(bl), want, dest, b == B::IterNe)?;
                // `iter_compare(a, b, f)` drops its params in reverse.
                self.drop_local(bl);
                self.drop_local(al);
            }
            B::IterCount | B::IterLast | B::IterMin | B::IterMax | B::IterCollect | B::IterSum | B::IterProduct => {
                let i = arg()?;
                let (owned, ty) = self.own(i)?;
                match b {
                    B::IterCount => self.count(Place::local(owned), ty, dest)?,
                    B::IterLast => self.last(Place::local(owned), ty, dest, dest_ty)?,
                    B::IterMin | B::IterMax => self.min_max(b == B::IterMax, Place::local(owned), ty, None, dest, dest_ty)?,
                    B::IterCollect => self.collect(Place::local(owned), ty, dest, dest_ty)?,
                    _ => self.sum(b == B::IterProduct, Place::local(owned), ty, dest, dest_ty)?,
                }
                self.drop_local(owned);
            }
            B::IterMinByKey | B::IterMaxByKey | B::IterForEach => {
                let (i, f) = (arg()?, arg()?);
                let (owned, ty) = self.own(i)?;
                let fty = self.op_ty(&f)?;
                let fl = self.local(fty);
                self.assign(Place::local(fl), Rvalue::Use(f));
                if b == B::IterForEach {
                    self.for_each(Place::local(owned), ty, Place::local(fl), fty)?;
                    self.assign(dest, Rvalue::Use(Operand::Const(Const::Unit)));
                } else {
                    self.min_max(b == B::IterMaxByKey, Place::local(owned), ty, Some((Place::local(fl), fty)), dest, dest_ty)?;
                }
                self.drop_local(owned);
                self.drop_local(fl);
            }
            B::IterPartition | B::IterUnzip => {
                let i = arg()?;
                let f = if b == B::IterPartition { Some(arg()?) } else { None };
                let (owned, ty) = self.own(i)?;
                let fl = match f {
                    Some(f) => {
                        let fty = self.op_ty(&f)?;
                        let fl = self.local(fty);
                        self.assign(Place::local(fl), Rvalue::Use(f));
                        Some((fl, fty))
                    }
                    None => None,
                };
                self.partition_unzip(Place::local(owned), ty, fl, dest, dest_ty)?;
                self.drop_local(owned);
                if let Some((fl, _)) = fl {
                    self.drop_local(fl);
                }
            }
            B::IterFold => {
                let (i, init, f) = (arg()?, arg()?, arg()?);
                let (owned, ty) = self.own(i)?;
                let fty = self.op_ty(&f)?;
                let fl = self.local(fty);
                self.assign(Place::local(fl), Rvalue::Use(f));
                self.fold(Place::local(owned), ty, init, Place::local(fl), fty, dest, dest_ty)?;
                self.drop_local(owned);
                self.drop_local(fl);
            }
            B::IterTryFold => {
                let (r, init, f) = (arg()?, arg()?, arg()?);
                let (itp, ty) = self.deref_arg(r)?;
                let (itp, ty) = self.user_iter(itp, ty)?;
                let fty = self.op_ty(&f)?;
                let fl = self.local(fty);
                self.assign(Place::local(fl), Rvalue::Use(f));
                self.try_fold(itp, ty, init, Place::local(fl), fty, dest, dest_ty)?;
                self.drop_local(fl);
            }
            B::IterArrayIntoIter => {
                // (array, 0, N) (W-STD-B).
                let a = arg()?;
                let at = self.op_ty(&a)?;
                let n = match self.body.tys.kind(at) {
                    TyKind::Array(_, c) => match self.body.tys.const_kind(c) {
                        ConstKind::Int(n) => n as u64,
                        _ => return Err("iterator expansion: array length is not known".into()),
                    },
                    _ => return Err("iterator expansion: into_iter of a non-array".into()),
                };
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![a, Self::usize_c(0), Self::usize_c(n)]));
            }
            // core's `repeat_n`: `(Some(x), n)`, or `(None, 0)` with `x`
            // dropped at once for a zero count.
            B::IterRepeatN => {
                let (x, n) = (arg()?, arg()?);
                let xt = self.op_ty(&x)?;
                let ot = self.body.tys.mk_option(xt);
                let xl = self.local(xt);
                self.assign(Place::local(xl), Rvalue::Use(x));
                let nl = self.copy_local(n, USIZE);
                let o = self.local(ot);
                let join = self.block();
                let z = self.cmp(crate::ast::BinOp::Eq, Operand::Copy(Place::local(nl)), Self::usize_c(0));
                let (zero, some) = self.branch(z);
                self.cur = zero;
                self.drop_local(xl);
                self.none(&Place::local(o), ot);
                self.goto(join);
                self.cur = some;
                let ax = self.take(Place::local(xl), xt);
                self.some(&Place::local(o), ot, ax);
                self.goto(join);
                self.cur = join;
                let ao = self.take(Place::local(o), ot);
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![ao, Operand::Copy(Place::local(nl))]));
            }
            // `std::array::from_fn(f)`: push each `f(i)` into a
            // `Vec` in order, then pop them back out into the array
            // aggregate. A panic in one call drops the `Vec`'s
            // built prefix front to back, as core's buffer guard
            // does, then `f`; call temps of a plain array aggregate
            // would drop back to front. The pops cannot panic (the
            // length is known), and the emptied `Vec` then drops
            // only its buffer. An element with no drop glue has no
            // drop order to keep: each `f(i)` goes to a temp and the
            // temps form the aggregate (no `Vec`, as core writes in
            // place).
            B::ArrayFromFn => {
                let f = arg()?;
                let f_ty = self.op_ty(&f)?;
                let fl = self.local(f_ty);
                self.assign(Place::local(fl), Rvalue::Use(f));
                let f_place = Place::local(fl);
                let (elem, n) = match self.body.tys.kind(dest_ty) {
                    TyKind::Array(e, c) => match self.body.tys.const_kind(c) {
                        ConstKind::Int(n) => (e, n as u64),
                        _ => return Err("iterator expansion: `from_fn` with an unknown array length".into()),
                    },
                    _ => return Err("iterator expansion: `from_fn` into a non-array".into()),
                };
                if n == 0 {
                    self.assign(dest.clone(), Rvalue::ArrayAgg(dest_ty, Vec::new()));
                } else if !crate::check::collect::needs_drop(self.p, &self.body.tys, elem) {
                    let mut ops = Vec::with_capacity(n as usize);
                    for i in 0..n {
                        let t = self.local(elem);
                        self.call_fn(f_ty, f_place.clone(), vec![Self::usize_c(i)], Place::local(t))?;
                        ops.push(self.take(Place::local(t), elem));
                    }
                    self.assign(dest.clone(), Rvalue::ArrayAgg(dest_ty, ops));
                } else {
                    let vec_ty = self.body.tys.mk_vec(elem);
                    let v = self.local(vec_ty);
                    self.assign(Place::local(v), Rvalue::VecLit(elem, Vec::new()));
                    for i in 0..n {
                        let t = self.local(elem);
                        self.call_fn(f_ty, f_place.clone(), vec![Self::usize_c(i)], Place::local(t))?;
                        let rv = self.ref_to(true, Place::local(v), vec_ty);
                        let u = self.local(UNIT);
                        let at = self.take(Place::local(t), elem);
                        self.call_builtin(Builtin::VecPush, vec![Operand::Move(Place::local(rv)), at], Place::local(u));
                    }
                    let opt_ty = self.body.tys.mk_option(elem);
                    let mut ops = Vec::new();
                    for _ in 0..n {
                        let o = self.local(opt_ty);
                        let rv = self.ref_to(true, Place::local(v), vec_ty);
                        self.call_builtin(Builtin::VecPop, vec![Operand::Move(Place::local(rv))], Place::local(o));
                        ops.push(Operand::Move(Self::payload(&Place::local(o))));
                    }
                    ops.reverse();
                    self.assign(dest.clone(), Rvalue::ArrayAgg(dest_ty, ops));
                    self.drop_local(v);
                }
                self.drop_local(fl);
            }
            // `[T; N]::map(f)` (core's `try_map` over a draining
            // iterator): the array moves into an `array::IntoIter`, each
            // element goes to `f` front to back, and the outputs collect
            // in a `Vec`, as for `from_fn`. Locals are made in core's
            // unwind drop order, reversed: on a panic in `f` the outputs
            // so far drop first, then the inputs not yet taken, then
            // `f`.
            B::ArrayMap => {
                let (arr, f) = (arg()?, arg()?);
                let f_ty = self.op_ty(&f)?;
                let fl = self.local(f_ty);
                self.assign(Place::local(fl), Rvalue::Use(f));
                let arr_ty = self.op_ty(&arr)?;
                let (elem, n) = match self.body.tys.kind(arr_ty) {
                    TyKind::Array(e, c) => match self.body.tys.const_kind(c) {
                        ConstKind::Int(n) => (e, n as u64),
                        _ => return Err("iterator expansion: `map` on an array of unknown length".into()),
                    },
                    _ => return Err("iterator expansion: `map` on a non-array".into()),
                };
                let out = match self.body.tys.kind(dest_ty) {
                    TyKind::Array(u, _) => u,
                    _ => return Err("iterator expansion: `map` into a non-array".into()),
                };
                let it_ty = it::mk_iter(&mut self.body.tys, IterKind::ArrayIntoIter, &[elem, arr_ty]);
                let itl = self.local(it_ty);
                self.assign(Place::local(itl), Rvalue::TupleAgg(it_ty, vec![arr, Self::usize_c(0), Self::usize_c(n)]));
                let vec_ty = self.body.tys.mk_vec(out);
                let v = self.local(vec_ty);
                self.assign(Place::local(v), Rvalue::VecLit(out, Vec::new()));
                let opt_in = self.body.tys.mk_option(elem);
                for _ in 0..n {
                    let t = self.local(opt_in);
                    self.next(Place::local(itl), it_ty, Place::local(t), false)?;
                    let x = self.take(Self::payload(&Place::local(t)), elem);
                    let y = self.local(out);
                    self.call_fn(f_ty, Place::local(fl), vec![x], Place::local(y))?;
                    let rv = self.ref_to(true, Place::local(v), vec_ty);
                    let u = self.local(UNIT);
                    let ay = self.take(Place::local(y), out);
                    self.call_builtin(Builtin::VecPush, vec![Operand::Move(Place::local(rv)), ay], Place::local(u));
                }
                let opt_out = self.body.tys.mk_option(out);
                let mut ops = Vec::new();
                for _ in 0..n {
                    let o = self.local(opt_out);
                    let rv = self.ref_to(true, Place::local(v), vec_ty);
                    self.call_builtin(Builtin::VecPop, vec![Operand::Move(Place::local(rv))], Place::local(o));
                    ops.push(Operand::Move(Self::payload(&Place::local(o))));
                }
                ops.reverse();
                self.assign(dest.clone(), Rvalue::ArrayAgg(dest_ty, ops));
                self.drop_local(v);
                self.drop_local(itl);
                self.drop_local(fl);
            }
            B::VecExtend | B::StringExtend => {
                // `v.extend(src)` (W-STD-B): `src` through `IntoIterator`.
                let (r, src) = (arg()?, arg()?);
                let st = self.op_ty(&src)?;
                let want = self
                    .wrapper_inner(st)
                    .or_else(|| it::as_iter_ty(&mut self.body.tys, st))
                    .ok_or("iterator expansion: bad extend argument")?;
                let iv = self.into_iter(src, want)?;
                let (owned, ty) = self.own(iv)?;
                let rt = self.op_ty(&r)?;
                let rl = self.local(rt);
                self.assign(Place::local(rl), Rvalue::Use(r));
                if b == B::VecExtend {
                    self.vec_extend(Place::local(owned), ty, rl)?;
                } else {
                    self.string_extend(Place::local(owned), ty, rl)?;
                }
                self.drop_local(owned);
                self.assign(dest, Rvalue::Use(Operand::Const(Const::Unit)));
            }
            B::HashExtend => {
                // `map.extend(src)` (W-STD-B): `src` through `IntoIterator`.
                let (r, src) = (arg()?, arg()?);
                let st = self.op_ty(&src)?;
                let want = self
                    .wrapper_inner(st)
                    .or_else(|| it::as_iter_ty(&mut self.body.tys, st))
                    .ok_or("iterator expansion: bad extend argument")?;
                let iv = self.into_iter(src, want)?;
                let (owned, ty) = self.own(iv)?;
                let rt = self.op_ty(&r)?;
                let rl = self.local(rt);
                self.assign(Place::local(rl), Rvalue::Use(r));
                self.hash_extend(Place::local(owned), ty, rl)?;
                self.drop_local(owned);
                self.assign(dest, Rvalue::Use(Operand::Const(Const::Unit)));
            }
            _ => return Err(format!("iterator expansion: unexpected builtin {b:?}")),
        }
        Ok(())
    }

    /// `Vec::extend` into the Vec behind `v` (a `&mut` local), as std's
    /// `SpecExtend` picks: a `vec::IntoIter`, a slice iterator of `&T`
    /// (`T: Copy`), or any `TrustedLen` iterator reserves the exact
    /// count once (`append_elements`, `extend_trusted`); every other
    /// iterator pushes and reserves `lower + 1` whenever full
    /// (`extend_desugared`). `&T` items copy out.
    /// `dest = x.into()` through one of std's `From` impls between
    /// builtin types (W-STD-B, check/convert.rs `std_from`): the
    /// conversion's builtin calls, or the `Some` and Cow variants.
    fn conv(&mut self, x: Operand, dest: Place, dst: Ty) -> R {
        use crate::check::convert::FromConv as F;
        let src = self.op_ty(&x)?;
        let how = crate::check::convert::std_from(self.p, &self.body.tys, dst, src).ok_or("conversion: no std From impl")?;
        let one = |ex: &mut Self, b: Builtin, x: Operand, dest: Place| ex.call_builtin(b, vec![x], dest);
        match how {
            F::Same => self.assign(dest, Rvalue::Use(x)),
            F::StringFromStr | F::StringFromChar => one(self, Builtin::StringFrom, x, dest),
            F::StringFromRefString => {
                let s = self.local(REF_STR);
                one(self, Builtin::StringAsStr, x, Place::local(s));
                one(self, Builtin::StringFrom, Operand::Copy(Place::local(s)), dest);
            }
            F::CowIntoOwned => one(self, Builtin::CowIntoOwned, x, dest),
            F::BytesFromString => one(self, Builtin::StringIntoBytes, x, dest),
            F::BytesFromStr => {
                let s = self.local(STRING);
                one(self, Builtin::StringFrom, x, Place::local(s));
                one(self, Builtin::StringIntoBytes, Operand::Move(Place::local(s)), dest);
            }
            F::VecFromSlice => one(self, Builtin::SliceToVec, x, dest),
            F::VecFromArray => one(self, Builtin::VecFrom, x, dest),
            F::VecFromBoxSlice => one(self, Builtin::BoxSliceIntoVec, x, dest),
            F::BoxSliceFromVec => one(self, Builtin::VecIntoBoxedSlice, x, dest),
            F::Own(k) => one(self, Builtin::OwnFrom(k), x, dest),
            F::OwnFromBox(k) => {
                // The box moves through a `Box` of the target's pointee
                // first: a `dyn` one may differ in its object lifetime
                // only, which this move gives the borrow checker.
                let e = self.body.tys.rc_elem(dst).ok_or("conversion: no Rc or Arc pointee")?;
                let bt = self.body.tys.mk_boxed(e);
                let b = self.local(bt);
                self.assign(Place::local(b), Rvalue::Use(x));
                one(self, Builtin::OwnFrom(k), Operand::Move(Place::local(b)), dest);
            }
            F::StringFromBoxStr => one(self, Builtin::OwnIntoString, x, dest),
            F::NonZeroGet => one(self, Builtin::NonZeroGet, x, dest),
            F::Some => self.some(&dest, dst, x),
            F::BoxNew => one(self, Builtin::BoxNew, x, dest),
            F::RcNew => one(self, Builtin::RcNew, x, dest),
            F::CowBorrowed | F::CowBorrowedView | F::CowOwned => {
                // The Cow instance's own Adt (mono gives each one its id).
                let a = self.body.tys.local_adt(dst).ok_or("conversion: no Cow Adt")?;
                let v = if how == F::CowOwned { 1 } else { 0 };
                let x = if how == F::CowBorrowedView {
                    let b = crate::check::collect::cow_arg(&self.body.tys, dst).ok_or("conversion: bad Cow")?;
                    let view = self.body.tys.mk_ref(false, b);
                    let s = self.local(view);
                    let inner = match self.body.tys.kind(src) {
                        TyKind::Ref(_, _, i) => i,
                        _ => src,
                    };
                    let b = if self.body.tys.is_string_ty(inner) { Builtin::StringAsStr } else { Builtin::VecAsSlice };
                    one(self, b, x, Place::local(s));
                    Operand::Copy(Place::local(s))
                } else {
                    x
                };
                self.assign(dest, Rvalue::Aggregate(a, v, vec![x]));
            }
        }
        Ok(())
    }

    fn vec_extend(&mut self, itp: Place, ty: Ty, v: Local) -> R {
        use crate::ast::BinOp::*;
        let vt = self.body.locals[v as usize].ty;
        let TyKind::Ref(_, _, vec_ty) = self.body.tys.kind(vt) else { return Err("iterator expansion: extend of a non-reference".into()) };
        let elem = self.body.tys.vec_elem(vec_ty).ok_or("iterator expansion: extend of a non-Vec")?;
        let item = self.item(ty)?;
        // Not `item != elem`: a fn pointer keeps `'static` in its type, so
        // `fn(&u8) -> &'static u8` items into a `Vec<fn(&u8) -> &'b u8>` differ.
        let by_ref = ref_depth(&self.body.tys, item) > ref_depth(&self.body.tys, elem);
        let push = |this: &mut Self, x: Local| {
            let ax = if by_ref { Operand::Copy(Place::local(x).deref()) } else { this.take(Place::local(x), elem) };
            let u = this.local(UNIT);
            this.call_builtin(Builtin::VecPush, vec![Operand::Copy(Place::local(v)), ax], Place::local(u));
        };
        let exact = self.trusted_len(ty) || matches!(self.kind_args(ty), Some((IterKind::VecIntoIter | IterKind::SliceIter, _)));
        if exact {
            let (_, hi) = self.hint(itp.clone(), ty)?;
            let (s, n) = self.switch_opt(&Place::local(hi));
            self.cur = n;
            self.term(Terminator::Panic(vec![FmtPart::Lit("capacity overflow".into())]));
            self.cur = s;
            let u = self.local(UNIT);
            self.call_builtin(Builtin::VecReserve, vec![Operand::Copy(Place::local(v)), Operand::Copy(Self::payload(&Place::local(hi)))], Place::local(u));
            return self.each(&itp, ty, &mut |this, x, _| {
                push(this, x);
                Ok(())
            });
        }
        let join = self.block();
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        let (_, n, x, _) = self.pull(&itp, ty)?;
        let rvt = self.body.tys.mk_ref(false, vec_ty);
        let rv = self.local(rvt);
        self.assign(Place::local(rv), Rvalue::Ref(false, Place::local(v).deref()));
        let (len, cap) = (self.local(USIZE), self.local(USIZE));
        self.call_builtin(Builtin::VecLen, vec![Operand::Copy(Place::local(rv))], Place::local(len));
        self.call_builtin(Builtin::VecCapacity, vec![Operand::Copy(Place::local(rv))], Place::local(cap));
        let full = self.cmp(Eq, Operand::Copy(Place::local(len)), Operand::Copy(Place::local(cap)));
        let (grow, ok) = self.branch(full);
        self.cur = grow;
        let (lo, _) = self.hint(itp.clone(), ty)?;
        let add = self.local(USIZE);
        self.call_builtin(Builtin::SaturatingAdd, vec![Operand::Copy(Place::local(lo)), Self::usize_c(1)], Place::local(add));
        let u = self.local(UNIT);
        self.call_builtin(Builtin::VecReserve, vec![Operand::Copy(Place::local(v)), Operand::Copy(Place::local(add))], Place::local(u));
        self.goto(ok);
        self.cur = ok;
        push(self, x);
        self.goto(lp);
        self.cur = n;
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// `String::extend` into the String behind `s` (a `&mut` local):
    /// chars reserve the size hint's lower bound, then push; str-like
    /// items (`&str`, `String`, `Box<str>`, `Cow<str>`) push_str each.
    fn string_extend(&mut self, itp: Place, ty: Ty, s: Local) -> R {
        let item = self.item(ty)?;
        let chars = item == CHAR || matches!(self.body.tys.kind(item), TyKind::Ref(_, _, c) if c == CHAR);
        if chars {
            let (lo, _) = self.hint(itp.clone(), ty)?;
            let u = self.local(UNIT);
            self.call_builtin(Builtin::StringReserve, vec![Operand::Copy(Place::local(s)), Operand::Copy(Place::local(lo))], Place::local(u));
        }
        self.each(&itp, ty, &mut |this, x, item| {
            let u = this.local(UNIT);
            if item == CHAR {
                this.call_builtin(Builtin::StringPush, vec![Operand::Copy(Place::local(s)), Operand::Copy(Place::local(x))], Place::local(u));
            } else if chars {
                this.call_builtin(Builtin::StringPush, vec![Operand::Copy(Place::local(s)), Operand::Copy(Place::local(x).deref())], Place::local(u));
            } else if item == REF_STR {
                this.call_builtin(Builtin::StringPushStr, vec![Operand::Copy(Place::local(s)), Operand::Copy(Place::local(x))], Place::local(u));
            } else {
                // An owned or smart str: push its `&str` view, then drop it.
                let rx = this.ref_to(false, Place::local(x), item);
                let sx = this.local(REF_STR);
                let view = if this.body.tys.is_string_ty(item) {
                    Builtin::StringAsStr
                } else if crate::check::collect::cow_arg(&this.body.tys, item).is_some() {
                    Builtin::CowDeref
                } else {
                    Builtin::ConvDeref
                };
                this.call_builtin(view, vec![Operand::Copy(Place::local(rx))], Place::local(sx));
                this.call_builtin(Builtin::StringPushStr, vec![Operand::Copy(Place::local(s)), Operand::Copy(Place::local(sx))], Place::local(u));
                this.drop_local(x);
            }
            Ok(())
        })
    }

    /// hashbrown's `extend` into the map or set behind `table` (a `&mut`
    /// local): reserve the size hint's lower bound when the table is
    /// empty, else half of it rounded up, then insert every item in
    /// order (a map's `(K, V)` items; an old value drops at once).
    fn hash_extend(&mut self, itp: Place, ty: Ty, table: Local) -> R {
        let tt = self.body.locals[table as usize].ty;
        let TyKind::Ref(_, _, t) = self.body.tys.kind(tt) else { return Err("iterator expansion: extend of a non-reference".into()) };
        let (kind, targs) = crate::ty::hash::hash_parts(&self.body.tys, t).ok_or("iterator expansion: extend of a non-table")?;
        let (lo, _) = self.hint(itp.clone(), ty)?;
        let u = self.local(UNIT);
        self.call_builtin(
            Builtin::HashExtendReserve,
            vec![Operand::Copy(Place::local(table)), Operand::Copy(Place::local(lo))],
            Place::local(u),
        );
        let map = kind == crate::ty::hash::HashTy::HashMap;
        let old_ty = if map { self.body.tys.mk_option(targs[1]) } else { BOOL };
        // `Extend<&T>` and `Extend<(&K, &V)>` (Copy parts): copy them in.
        // The item is `T` or `&T` (check/hashmap.rs), so one more
        // reference than the key type means by reference.
        let item = self.item(ty)?;
        let key_item = match self.body.tys.kind(item) {
            TyKind::Tuple(ts) if map => self.body.tys.tys_of(ts)[0],
            _ => item,
        };
        let by_ref = ref_depth(&self.body.tys, key_item) > ref_depth(&self.body.tys, targs[0]);
        self.each(&itp, ty, &mut |this, x, _| {
            let res = this.local(old_ty);
            let mut args = vec![Operand::Copy(Place::local(table))];
            if map && by_ref {
                args.push(Operand::Copy(Place::local(x).project(Proj::Field(0)).deref()));
                args.push(Operand::Copy(Place::local(x).project(Proj::Field(1)).deref()));
            } else if map {
                args.push(Operand::Move(Place::local(x).project(Proj::Field(0))));
                args.push(Operand::Move(Place::local(x).project(Proj::Field(1))));
            } else if by_ref {
                args.push(Operand::Copy(Place::local(x).deref()));
            } else {
                args.push(Operand::Move(Place::local(x)));
            }
            this.call_builtin(if map { Builtin::MapInsert } else { Builtin::SetInsert }, args, Place::local(res));
            if map {
                this.drop_local(res);
            }
            Ok(())
        })
    }

    /// A user iterator (or other non-builtin one) that a borrowing
    /// consumer reaches through its `&mut` (check/iter.rs passes it as
    /// is): a `ByNext` wrapper over a reborrow of it, so the expansion
    /// steps it through its own `next` and `size_hint` and it stays put.
    /// Builtin iterators come back unchanged.
    fn user_iter(&mut self, itp: Place, ty: Ty) -> Result<(Place, Ty), String> {
        if self.kind_args(ty).is_some() || self.body.tys.is_chars_ty(ty) {
            return Ok((itp, ty));
        }
        let fns = crate::check::iter::by_next_fns(self.p, &self.body.tys, ty)?;
        let item = fns.item.ok_or("iterator expansion: no `Item` in the impl")?;
        let held = self.body.tys.mk_ref(true, ty);
        let w = it::mk_iter(&mut self.body.tys, IterKind::ByNext, &[held, item]);
        let r = self.ref_to(true, itp, ty);
        let v = self.local(w);
        self.assign(Place::local(v), Rvalue::TupleAgg(w, vec![Operand::Move(Place::local(r))]));
        Ok((Place::local(v), w))
    }

    /// The iterator a `ByNext` wrapper holds (its first type argument
    /// `held`, at place `at`): itself, or what the reference it holds
    /// for a borrowing consumer (`user_iter`) points to.
    fn by_next_held(&self, held: Ty, at: Place) -> (Ty, Place) {
        match self.body.tys.kind(held) {
            TyKind::Ref(_, _, inner) => (inner, at.deref()),
            _ => (held, at),
        }
    }

    /// The builtin iterator a `ByNext` wrapper reaches through the
    /// `&mut I` it holds (core's `impl Iterator for &mut I`): it steps,
    /// hints, and fuses as `I` itself, in place.
    /// A std collection iterator struct behind the `&mut` counts as its
    /// inner builtin iterator (field 0, `by_mut_place`).
    fn by_mut_builtin(&mut self, held: Ty) -> Option<Ty> {
        match self.body.tys.kind(held) {
            TyKind::Ref(_, Mut::Mut, inner) if self.kind_args(inner).is_some() || self.body.tys.is_chars_ty(inner) => Some(inner),
            TyKind::Ref(_, Mut::Mut, inner) => self.wrapper_inner(inner),
            _ => None,
        }
    }

    /// The place of the builtin iterator `by_mut_builtin` found, for the
    /// `&mut` held at `at`: `*at`, or field 0 of the collection iterator
    /// struct it points to.
    fn by_mut_place(&mut self, held: Ty, at: Place) -> Place {
        match self.body.tys.kind(held) {
            TyKind::Ref(_, _, inner) if self.wrapper_inner(inner).is_some() => at.deref().project(Proj::Field(0)),
            _ => at.deref(),
        }
    }

    /// The inner iterator type when `ty` is a std source collection
    /// iterator struct (collect.rs `collection_iter_inner`): check
    /// typed its methods as the inner type's, so every expansion
    /// entry below unwraps field 0 and continues with the inner type.
    fn wrapper_inner(&mut self, ty: Ty) -> Option<Ty> {
        self.p.collection_iter_inner(&mut self.body.tys, ty)
    }

    /// A by-value iterator operand as its inner iterator when it is
    /// a collection iterator struct (moves field 0 into a fresh
    /// local); other operands pass through.
    fn unwrap_op(&mut self, i: Operand) -> Result<Operand, String> {
        let ty = self.op_ty(&i)?;
        let Some(inner) = self.wrapper_inner(ty) else { return Ok(i) };
        let pl = self.op_place(i, ty);
        let l = self.local(inner);
        self.assign(Place::local(l), Rvalue::Use(self.take(pl.project(Proj::Field(0)), inner)));
        Ok(Operand::Move(Place::local(l)))
    }

    /// The iterator place and type behind a `&mut I` argument.
    fn deref_arg(&mut self, r: Operand) -> Result<(Place, Ty), String> {
        let rt = self.op_ty(&r)?;
        let TyKind::Ref(_, _, ty) = self.body.tys.kind(rt) else {
            return Err("iterator expansion: `&mut self` argument is not a reference".into());
        };
        let pl = self.op_place(r, rt);
        if let Some(inner) = self.wrapper_inner(ty) {
            return Ok((pl.deref().project(Proj::Field(0)), inner));
        }
        Ok((pl.deref(), ty))
    }

    /// Moves a by-value iterator argument into a fresh local the
    /// consumer owns (dropped when the consumer returns, as in Rust).
    fn own(&mut self, i: Operand) -> Result<(Local, Ty), String> {
        let i = self.unwrap_op(i)?;
        let ty = self.op_ty(&i)?;
        let l = self.local(ty);
        self.assign(Place::local(l), Rvalue::Use(i));
        Ok((l, ty))
    }

    /// Makes an `option` or `result` iterator (`dest_ty`) from its
    /// source operand (fx-option-rest): a reference to the enum for
    /// `Iter` and `IterMut` (the field borrows the payload), the enum
    /// by value for `IntoIter`. A `Result`'s `Err` payload drops
    /// here, at conversion, as core's `self.ok()` does.
    fn make_opt_res(&mut self, o: Operand, dest_ty: Ty, dest: Place) -> R {
        use IterKind as K;
        let (k, a) = self.kind_args(dest_ty).ok_or("iterator expansion: bad option/result iterator")?;
        let fields = it::field_tys(&mut self.body.tys, dest_ty).ok_or("iterator expansion: bad option/result iterator")?;
        let ft = fields[0];
        match k {
            K::OptionIntoIter => self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![o])),
            K::ResultIntoIter => {
                let ot = self.op_ty(&o)?;
                let l = self.local(ot);
                self.assign(Place::local(l), Rvalue::Use(o));
                let fl = self.local(ft);
                let d = self.local(int(IntTy::U32));
                self.assign(Place::local(d), Rvalue::Discriminant(Place::local(l)));
                let (ok, err) = (self.block(), self.block());
                self.term(Terminator::Switch(Operand::Copy(Place::local(d)), vec![(0, ok)], err));
                let join = self.block();
                self.cur = ok;
                let pl = Place::local(l).project(Proj::Downcast(0)).project(Proj::Field(0));
                let v = self.take(pl, a[0]);
                self.some(&Place::local(fl), ft, v);
                self.goto(join);
                self.cur = err;
                self.none(&Place::local(fl), ft);
                self.drop_local(l);
                self.goto(join);
                self.cur = join;
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(fl))]));
            }
            K::OptionIter | K::OptionIterMut | K::ResultIter | K::ResultIterMut => {
                let mutable = matches!(k, K::OptionIterMut | K::ResultIterMut);
                let variant = if matches!(k, K::OptionIter | K::OptionIterMut) { 1 } else { 0 };
                let ot = self.op_ty(&o)?;
                let rp = self.op_place(o, ot);
                let base = rp.deref();
                let fl = self.local(ft);
                let d = self.local(int(IntTy::U32));
                self.assign(Place::local(d), Rvalue::Discriminant(base.clone()));
                let (some_b, none_b) = (self.block(), self.block());
                self.term(Terminator::Switch(Operand::Copy(Place::local(d)), vec![(variant, some_b)], none_b));
                let join = self.block();
                self.cur = some_b;
                let pl = base.project(Proj::Downcast(variant)).project(Proj::Field(0));
                let r = self.ref_to(mutable, pl, a[0]);
                self.some(&Place::local(fl), ft, Operand::Move(Place::local(r)));
                self.goto(join);
                self.cur = none_b;
                self.none(&Place::local(fl), ft);
                self.goto(join);
                self.cur = join;
                self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![Operand::Move(Place::local(fl))]));
            }
            _ => return Err("iterator expansion: bad option/result iterator".into()),
        }
        Ok(())
    }

    /// An `IntoIterator` argument of `chain` or `zip` as the iterator
    /// type `want` (check/iter.rs `into_iter_ty`).
    fn into_iter(&mut self, o: Operand, want: Ty) -> Result<Operand, String> {
        let ot = self.op_ty(&o)?;
        if ot == want {
            return Ok(o);
        }
        // A collection iterator struct chains as its inner iterator.
        if self.wrapper_inner(ot) == Some(want) {
            return self.unwrap_op(o);
        }
        let Some((k, _)) = self.kind_args(want) else { return Err("iterator expansion: bad IntoIterator argument".into()) };
        let l = self.local(want);
        match k {
            IterKind::VecIntoIter => self.call_builtin(Builtin::IterVecIntoIter, vec![o], Place::local(l)),
            // A map or set (or a reference to one) makes its hash iterator.
            k if k.is_hash() => self.call_builtin(Builtin::HashIterNew, vec![o], Place::local(l)),
            // An array by value: (array, 0, N).
            IterKind::ArrayIntoIter => {
                let n = match self.body.tys.kind(ot) {
                    TyKind::Array(_, c) => match self.body.tys.const_kind(c) {
                        ConstKind::Int(n) => n as u64,
                        _ => return Err("iterator expansion: array length is not known".into()),
                    },
                    _ => return Err("iterator expansion: bad IntoIterator argument".into()),
                };
                self.assign(Place::local(l), Rvalue::TupleAgg(want, vec![o, Self::usize_c(0), Self::usize_c(n)]));
            }
            IterKind::SliceIter | IterKind::SliceIterMut => {
                let fields = it::field_tys(&mut self.body.tys, want).ok_or("iterator expansion: bad slice iterator")?;
                let pl = self.op_place(o, ot);
                let s = self.local(fields[0]);
                self.assign(Place::local(s), Rvalue::SliceOf(pl.deref()));
                self.assign(Place::local(l), Rvalue::TupleAgg(want, vec![Operand::Move(Place::local(s))]));
            }
            // Another iterator (W-STD-B): moved into its `next` wrapper.
            IterKind::ByNext => self.assign(Place::local(l), Rvalue::TupleAgg(want, vec![o])),
            // An Option or Result (or a reference to one) into its
            // one-item iterator (fx-option-rest).
            k if it::is_opt_res(k) => self.make_opt_res(o, want, Place::local(l))?,
            _ => return Err("iterator expansion: bad IntoIterator argument".into()),
        }
        Ok(Operand::Move(Place::local(l)))
    }

    // ---------- next and next_back ----------

    /// `dest = itp.next()` (`next_back` when `back`). Under `fold`, Zip
    /// and StepBy still pull their inner iterators with `next` and
    /// `nth`, as std's `try_fold` of both does.
    fn next(&mut self, itp: Place, ty: Ty, dest: Place, back: bool) -> R {
        let saved = self.fold;
        if matches!(self.kind_args(ty), Some((IterKind::Zip | IterKind::StepBy, _))) {
            self.fold = false;
        }
        let r = self.next_in(itp, ty, dest, back);
        self.fold = saved;
        r
    }

    fn next_in(&mut self, itp: Place, ty: Ty, dest: Place, back: bool) -> R {
        use crate::ast::BinOp::*;
        use IterKind as K;
        let item = self.item(ty)?;
        let opt = self.body.tys.mk_option(item);
        let join = self.block();
        if self.is_char_range(ty) {
            self.char_range_next(itp, ty, dest, back)?;
            self.goto(join);
            self.cur = join;
            return Ok(());
        }
        if self.body.tys.is_chars_ty(ty) {
            let r = self.ref_to(true, itp, ty);
            let b = if back { Builtin::CharsNextBack } else { Builtin::CharsNext };
            self.call_builtin(b, vec![Operand::Move(Place::local(r))], dest);
            self.goto(join);
            self.cur = join;
            return Ok(());
        }
        let (k, a) = self.kind_args(ty).ok_or("iterator expansion: not an iterator")?;
        let f = |i: u32| itp.project(Proj::Field(i));
        match k {
            // The mpsc iterators (W-THREADS): `recv` (or `try_recv` for
            // `TryIter`) through the receiver, `None` once it fails.
            K::RecvIter | K::RecvTryIter | K::RecvIntoIter => {
                let rt = crate::ty::sync::sync_ty(&mut self.body.tys, crate::ty::sync::SyncTy::Receiver, &[a[0]]);
                let r = if k == K::RecvIntoIter {
                    Operand::Move(Place::local(self.ref_to(false, f(0), rt)))
                } else {
                    Operand::Copy(f(0))
                };
                let b = Builtin::Sync(crate::check::sync::SyncOp::RecvNext(k != K::RecvTryIter));
                self.call_builtin(b, vec![r], dest);
                self.goto(join);
            }
            K::SliceIter | K::SliceIterMut => {
                let m = k == K::SliceIterMut;
                let sd = f(0).deref();
                let len = self.local(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(sd.clone()));
                let c = self.cmp(Lt, Self::usize_c(0), Operand::Copy(Place::local(len)));
                let (s, n) = self.branch(c);
                self.cur = s;
                let idx = self.local(USIZE);
                if back {
                    self.assign(Place::local(idx), Rvalue::Bin(Sub, Operand::Copy(Place::local(len)), Self::usize_c(1)));
                } else {
                    self.assign(Place::local(idx), Rvalue::Use(Self::usize_c(0)));
                }
                let r = self.ref_to(m, sd.project(Proj::Index(idx)), a[0]);
                let rest_ty = self.place_ty(&f(0))?;
                let rest = self.local(rest_ty);
                let (lo, hi) = if back { (Self::usize_c(0), Some(Operand::Copy(Place::local(idx)))) } else { (Self::usize_c(1), None) };
                self.assign(Place::local(rest), Rvalue::Subslice { base: sd, lo, hi, inclusive: false, mutable: m });
                self.assign(f(0), Rvalue::Use(Operand::Move(Place::local(rest))));
                self.some(&dest, opt, Operand::Move(Place::local(r)));
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::VecIntoIter => {
                let r = self.ref_to(true, itp, ty);
                let b = if back { Builtin::VecIterNextBack } else { Builtin::VecIterNext };
                self.call_builtin(b, vec![Operand::Move(Place::local(r))], dest);
                self.goto(join);
            }
            // `array::IntoIter` (fx-array-iter): the element at the
            // front (or back) index. The read is a `Copy` operand on
            // purpose: a move out of a dynamic index has no move path
            // for drop elaboration. Ownership moves by the index
            // change alone, and the iterator's C drop glue drops only
            // the range the indexes still span.
            K::ArrayIntoIter => {
                let c = self.cmp(Lt, Operand::Copy(f(1)), Operand::Copy(f(2)));
                let (s, n) = self.branch(c);
                self.cur = s;
                let idx = self.local(USIZE);
                if back {
                    self.assign(f(2), Rvalue::Bin(Sub, Operand::Copy(f(2)), Self::usize_c(1)));
                    self.assign(Place::local(idx), Rvalue::Use(Operand::Copy(f(2))));
                } else {
                    self.assign(Place::local(idx), Rvalue::Use(Operand::Copy(f(1))));
                    self.assign(f(1), Rvalue::Bin(Add, Operand::Copy(f(1)), Self::usize_c(1)));
                }
                self.some(&dest, opt, Operand::Copy(f(0).project(Proj::Index(idx))));
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            // The slice splits (core slice/iter.rs): see `slice_split_next`.
            K::SliceSplit | K::SliceSplitMut => self.slice_split_next(&itp, k, &a, back, &dest, opt, join)?,
            K::ChunkBy | K::ChunkByMut => self.chunk_by_next(&itp, k, &a, back, &dest, opt, join)?,
            // `env::Args`: the argument at the front (or back) index while
            // the indexes differ, taken first, then checked as UTF-8 as
            // std's `into_string().unwrap()` does (runtime `lust_env_arg`).
            K::Args => {
                let c = self.cmp(Lt, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (s, n) = self.branch(c);
                self.cur = s;
                let idx = self.local(USIZE);
                if back {
                    self.assign(f(1), Rvalue::Bin(Sub, Operand::Copy(f(1)), Self::usize_c(1)));
                    self.assign(Place::local(idx), Rvalue::Use(Operand::Copy(f(1))));
                } else {
                    self.assign(Place::local(idx), Rvalue::Use(Operand::Copy(f(0))));
                    self.assign(f(0), Rvalue::Bin(Add, Operand::Copy(f(0)), Self::usize_c(1)));
                }
                let st = self.local(STRING);
                self.call_builtin(Builtin::EnvArg, vec![Operand::Copy(Place::local(idx)), Operand::Const(Const::Bool(back))], Place::local(st));
                self.some(&dest, opt, Operand::Move(Place::local(st)));
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            // `iter::RepeatN` (W-STD-B), as core's `next` (and `next_back`,
            // the same): a clone of the element while more than one is
            // left (the clone first, then the count), then the element
            // itself, then `None`.
            K::RepeatN => {
                let c = self.cmp(Lt, Self::usize_c(1), Operand::Copy(f(1)));
                let (many, last) = self.branch(c);
                self.cur = many;
                let r = self.ref_to(false, Self::payload(&f(0)), a[0]);
                let y = self.local(a[0]);
                self.call_builtin(Builtin::Clone, vec![Operand::Move(Place::local(r))], Place::local(y));
                self.assign(f(1), Rvalue::Bin(Sub, Operand::Copy(f(1)), Self::usize_c(1)));
                let ay = self.take(Place::local(y), a[0]);
                self.some(&dest, opt, ay);
                self.goto(join);
                self.cur = last;
                self.assign(f(1), Rvalue::Use(Self::usize_c(0)));
                self.take_none(f(0), opt, dest.clone());
                self.goto(join);
            }
            // `Windows` (W-STD-B): the first (or last) `size` elements
            // while that many remain, then the slice loses one element
            // at that end, as std's `next` and `next_back` do.
            K::Windows => {
                let sd = f(0).deref();
                let len = self.local(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(sd.clone()));
                let c = self.cmp(Lt, Operand::Copy(Place::local(len)), Operand::Copy(f(1)));
                let (short, s) = self.branch(c);
                self.cur = s;
                let st = self.place_ty(&f(0))?;
                let (w, rest) = (self.local(st), self.local(st));
                if back {
                    let lo = self.local(USIZE);
                    self.assign(Place::local(lo), Rvalue::Bin(Sub, Operand::Copy(Place::local(len)), Operand::Copy(f(1))));
                    let hi = self.local(USIZE);
                    self.assign(Place::local(hi), Rvalue::Bin(Sub, Operand::Copy(Place::local(len)), Self::usize_c(1)));
                    self.assign(Place::local(w), Rvalue::Subslice { base: sd.clone(), lo: Operand::Copy(Place::local(lo)), hi: None, inclusive: false, mutable: false });
                    self.assign(Place::local(rest), Rvalue::Subslice { base: sd, lo: Self::usize_c(0), hi: Some(Operand::Copy(Place::local(hi))), inclusive: false, mutable: false });
                } else {
                    self.assign(Place::local(w), Rvalue::Subslice { base: sd.clone(), lo: Self::usize_c(0), hi: Some(Operand::Copy(f(1))), inclusive: false, mutable: false });
                    self.assign(Place::local(rest), Rvalue::Subslice { base: sd, lo: Self::usize_c(1), hi: None, inclusive: false, mutable: false });
                }
                self.assign(f(0), Rvalue::Use(Operand::Move(Place::local(rest))));
                self.some(&dest, opt, Operand::Move(Place::local(w)));
                self.goto(join);
                self.cur = short;
                self.none(&dest, opt);
                self.goto(join);
            }
            // `Chunks` and `ChunksMut` (tf-slice): the first (or
            // last) at most `size` elements while any remain; the
            // back chunk is the remainder when the length does not
            // divide evenly, as std computes it.
            K::Chunks | K::ChunksMut => {
                let m = k == K::ChunksMut;
                let sd = f(0).deref();
                let len = self.local(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(sd.clone()));
                let c = self.cmp(Eq, Operand::Copy(Place::local(len)), Self::usize_c(0));
                let (empty, s) = self.branch(c);
                self.cur = s;
                let st = self.place_ty(&f(0))?;
                let (w, rest) = (self.local(st), self.local(st));
                if back {
                    let rem = self.local(USIZE);
                    self.assign(Place::local(rem), Rvalue::Bin(Rem, Operand::Copy(Place::local(len)), Operand::Copy(f(1))));
                    let csz = self.local(USIZE);
                    let c2 = self.cmp(Eq, Operand::Copy(Place::local(rem)), Self::usize_c(0));
                    let (even, uneven) = self.branch(c2);
                    let go = self.block();
                    self.cur = even;
                    self.assign(Place::local(csz), Rvalue::Use(Operand::Copy(f(1))));
                    self.goto(go);
                    self.cur = uneven;
                    self.assign(Place::local(csz), Rvalue::Use(Operand::Copy(Place::local(rem))));
                    self.goto(go);
                    self.cur = go;
                    let lo = self.local(USIZE);
                    self.assign(Place::local(lo), Rvalue::Bin(Sub, Operand::Copy(Place::local(len)), Operand::Copy(Place::local(csz))));
                    self.assign(
                        Place::local(w),
                        Rvalue::Subslice { base: sd.clone(), lo: Operand::Copy(Place::local(lo)), hi: None, inclusive: false, mutable: m },
                    );
                    self.assign(
                        Place::local(rest),
                        Rvalue::Subslice {
                            base: sd,
                            lo: Self::usize_c(0),
                            hi: Some(Operand::Copy(Place::local(lo))),
                            inclusive: false,
                            mutable: m,
                        },
                    );
                } else {
                    let csz = self.local(USIZE);
                    let c2 = self.cmp(Lt, Operand::Copy(Place::local(len)), Operand::Copy(f(1)));
                    let (short, full) = self.branch(c2);
                    let go = self.block();
                    self.cur = short;
                    self.assign(Place::local(csz), Rvalue::Use(Operand::Copy(Place::local(len))));
                    self.goto(go);
                    self.cur = full;
                    self.assign(Place::local(csz), Rvalue::Use(Operand::Copy(f(1))));
                    self.goto(go);
                    self.cur = go;
                    self.assign(
                        Place::local(w),
                        Rvalue::Subslice {
                            base: sd.clone(),
                            lo: Self::usize_c(0),
                            hi: Some(Operand::Copy(Place::local(csz))),
                            inclusive: false,
                            mutable: m,
                        },
                    );
                    self.assign(
                        Place::local(rest),
                        Rvalue::Subslice { base: sd, lo: Operand::Copy(Place::local(csz)), hi: None, inclusive: false, mutable: m },
                    );
                }
                self.assign(f(0), Rvalue::Use(Operand::Move(Place::local(rest))));
                self.some(&dest, opt, Operand::Move(Place::local(w)));
                self.goto(join);
                self.cur = empty;
                self.none(&dest, opt);
                self.goto(join);
            }
            // `ChunksExact` and `ChunksExactMut` (tf-slice): one
            // full chunk from either end while one remains; the
            // remainder (field 1) never yields.
            K::ChunksExact | K::ChunksExactMut => {
                let m = k == K::ChunksExactMut;
                let size_field = f(2);
                let sd = f(0).deref();
                let len = self.local(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(sd.clone()));
                let c = self.cmp(Lt, Operand::Copy(Place::local(len)), Operand::Copy(size_field.clone()));
                let (short, s) = self.branch(c);
                self.cur = s;
                let st = self.place_ty(&f(0))?;
                let (w, rest) = (self.local(st), self.local(st));
                if back {
                    let lo = self.local(USIZE);
                    self.assign(Place::local(lo), Rvalue::Bin(Sub, Operand::Copy(Place::local(len)), Operand::Copy(size_field)));
                    self.assign(
                        Place::local(w),
                        Rvalue::Subslice { base: sd.clone(), lo: Operand::Copy(Place::local(lo)), hi: None, inclusive: false, mutable: m },
                    );
                    self.assign(
                        Place::local(rest),
                        Rvalue::Subslice {
                            base: sd,
                            lo: Self::usize_c(0),
                            hi: Some(Operand::Copy(Place::local(lo))),
                            inclusive: false,
                            mutable: m,
                        },
                    );
                } else {
                    self.assign(
                        Place::local(w),
                        Rvalue::Subslice {
                            base: sd.clone(),
                            lo: Self::usize_c(0),
                            hi: Some(Operand::Copy(size_field.clone())),
                            inclusive: false,
                            mutable: m,
                        },
                    );
                    self.assign(
                        Place::local(rest),
                        Rvalue::Subslice { base: sd, lo: Operand::Copy(size_field), hi: None, inclusive: false, mutable: m },
                    );
                }
                self.assign(f(0), Rvalue::Use(Operand::Move(Place::local(rest))));
                self.some(&dest, opt, Operand::Move(Place::local(w)));
                self.goto(join);
                self.cur = short;
                self.none(&dest, opt);
                self.goto(join);
            }
            // `Utf8Chunks` (tf-slice): one runtime step over the
            // bytes left (forward only).
            K::Utf8Chunks => {
                if back {
                    return Err("iterator expansion: Utf8Chunks is forward-only here".into());
                }
                let r = self.ref_to(true, itp, ty);
                self.call_builtin(Builtin::Utf8ChunksNext, vec![Operand::Move(Place::local(r))], dest);
                self.goto(join);
            }
            K::Utf8Chunk => return Err("iterator expansion: Utf8Chunk is not an iterator".into()),
            // `Flatten` (W-STD-B), as std's FlattenCompat::next: the front
            // inner iterator's items, then the next inner value from the
            // outer iterator, then the back inner iterator's. The outer is a
            // `Fuse<I>`: one that is not a FusedIterator (a user iterator)
            // drops once it ends; a fused one stays (std's specialization).
            K::Flatten => {
                if back {
                    return Err("iterator expansion: Flatten is forward-only here".into());
                }
                let u = a[1];
                let (ot, ut) = (self.place_ty(&f(0))?, self.place_ty(&f(1))?);
                let lp = self.block();
                self.goto(lp);
                self.cur = lp;
                let pull = self.block();
                let (fs, fnone) = self.switch_opt(&f(1));
                self.cur = fnone;
                self.goto(pull);
                self.cur = fs;
                let t = self.local(opt);
                self.next(Self::payload(&f(1)), u, Place::local(t), false)?;
                let (hit, done) = self.switch_opt(&Place::local(t));
                self.cur = hit;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(t))));
                self.goto(join);
                self.cur = done;
                self.none(&f(1), ut);
                self.goto(pull);
                self.cur = pull;
                let back_side = self.block();
                let (os, onone) = self.switch_opt(&f(0));
                self.cur = onone;
                self.goto(back_side);
                self.cur = os;
                let ii = self.item(a[0])?;
                let oi = self.body.tys.mk_option(ii);
                let x = self.local(oi);
                self.next(Self::payload(&f(0)), a[0], Place::local(x), false)?;
                let (xs, xn) = self.switch_opt(&Place::local(x));
                self.cur = xs;
                let xv = self.take(Self::payload(&Place::local(x)), ii);
                let uo = self.into_iter(xv, u)?;
                self.some(&f(1), ut, uo);
                self.goto(lp);
                self.cur = xn;
                if !self.fused(a[0]) {
                    self.none(&f(0), ot);
                }
                self.goto(back_side);
                self.cur = back_side;
                let (bs, bnone) = self.switch_opt(&f(2));
                self.cur = bs;
                self.next(Self::payload(&f(2)), u, dest.clone(), false)?;
                let (bh, bd) = self.switch_opt(&dest);
                self.cur = bd;
                self.none(&f(2), ut);
                self.goto(join);
                self.cur = bh;
                self.goto(join);
                self.cur = bnone;
                self.none(&dest, opt);
                self.goto(join);
            }
            // The str splits (W-STD-B): one runtime step (cgen/split.rs).
            K::StrSplit => {
                let r = self.ref_to(true, itp, ty);
                let b = if back { Builtin::StrSplitNextBack } else { Builtin::StrSplitNext };
                self.call_builtin(b, vec![Operand::Move(Place::local(r))], dest);
                self.goto(join);
            }
            // The str matches forms (tf-str): one runtime step yields
            // the `(usize, &str)` pair; the plain forms keep its text.
            K::StrMatches => {
                let pair = self.tuple_ty(&[USIZE, REF_STR]);
                let opair = self.body.tys.mk_option(pair);
                let x = self.local(opair);
                let r = self.ref_to(true, itp, ty);
                let b = if back { Builtin::StrMatchesNextBack } else { Builtin::StrMatchesNext };
                self.call_builtin(b, vec![Operand::Move(Place::local(r))], Place::local(x));
                let indexed = it::matches_mode(&self.body.tys, a[1]).is_some_and(|m| m.indexed());
                if indexed {
                    self.assign(dest, Rvalue::Use(Operand::Move(Place::local(x))));
                } else {
                    let (s, n) = self.switch_opt(&Place::local(x));
                    self.cur = s;
                    let text = Self::payload(&Place::local(x)).project(Proj::Field(1));
                    self.some(&dest, opt, Operand::Copy(text));
                    self.goto(join);
                    self.cur = n;
                    self.none(&dest, opt);
                }
                self.goto(join);
            }
            // `EncodeUtf16` (tf-str): a buffered low surrogate first,
            // else the next char's units (the high surrogate first,
            // its low half buffered in field 1). Forward only, as std.
            K::EncodeUtf16 => {
                let u16t = int(IntTy::U16);
                let u32t = int(IntTy::U32);
                let has = self.cmp(Ne, Operand::Copy(f(1)), Self::usize_c(0));
                let (buf_b, chr_b) = self.branch(has);
                self.cur = buf_b;
                let v = self.local(u16t);
                self.assign(Place::local(v), Rvalue::Cast(Operand::Copy(f(1)), u16t));
                self.assign(f(1), Rvalue::Use(Self::usize_c(0)));
                self.some(&dest, opt, Operand::Copy(Place::local(v)));
                self.goto(join);
                self.cur = chr_b;
                let oc = self.body.tys.mk_option(CHAR);
                let x = self.local(oc);
                let rm = self.ref_to(true, f(0), CHARS);
                self.call_builtin(Builtin::CharsNext, vec![Operand::Move(Place::local(rm))], Place::local(x));
                let (s, n) = self.switch_opt(&Place::local(x));
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
                self.cur = s;
                let cp = self.local(u32t);
                self.assign(Place::local(cp), Rvalue::Cast(Operand::Copy(Self::payload(&Place::local(x))), u32t));
                let small = self.cmp(Lt, Operand::Copy(Place::local(cp)), Self::u32_c(0x10000));
                let (one, two) = self.branch(small);
                self.cur = one;
                let v1 = self.local(u16t);
                self.assign(Place::local(v1), Rvalue::Cast(Operand::Copy(Place::local(cp)), u16t));
                self.some(&dest, opt, Operand::Copy(Place::local(v1)));
                self.goto(join);
                self.cur = two;
                let d = self.local(u32t);
                self.assign(Place::local(d), Rvalue::Bin(Sub, Operand::Copy(Place::local(cp)), Self::u32_c(0x10000)));
                let hi = self.local(u32t);
                let hi_shift = self.local(u32t);
                self.assign(Place::local(hi_shift), Rvalue::Bin(Shr, Operand::Copy(Place::local(d)), Self::u32_c(10)));
                self.assign(Place::local(hi), Rvalue::Bin(Add, Operand::Copy(Place::local(hi_shift)), Self::u32_c(0xD800)));
                let lo = self.local(u32t);
                let lo_mask = self.local(u32t);
                self.assign(Place::local(lo_mask), Rvalue::Bin(BitAnd, Operand::Copy(Place::local(d)), Self::u32_c(0x3FF)));
                self.assign(Place::local(lo), Rvalue::Bin(Add, Operand::Copy(Place::local(lo_mask)), Self::u32_c(0xDC00)));
                self.assign(f(1), Rvalue::Cast(Operand::Copy(Place::local(lo)), USIZE));
                let v2 = self.local(u16t);
                self.assign(Place::local(v2), Rvalue::Cast(Operand::Copy(Place::local(hi)), u16t));
                self.some(&dest, opt, Operand::Copy(Place::local(v2)));
                self.goto(join);
            }
            // The `option` and `result` iterators (W-STD-B,
            // fx-option-rest): `self.inner.take()`, from either end.
            K::OptionIntoIter | K::OptionIter | K::OptionIterMut | K::ResultIter | K::ResultIterMut | K::ResultIntoIter => {
                let ot = self.place_ty(&f(0))?;
                let r = self.ref_to(true, f(0), ot);
                let nl = self.local(ot);
                self.none(&Place::local(nl), ot);
                self.call_builtin(Builtin::MemReplace, vec![Operand::Move(Place::local(r)), Operand::Move(Place::local(nl))], dest);
                self.goto(join);
            }
            // `CharIndices` (W-STD-B), as std's: the front offset grows by
            // the bytes `next` consumed; `next_back` gives the offset of
            // the char it removed (front offset + bytes left).
            K::CharIndices => {
                let oc = self.body.tys.mk_option(CHAR);
                let x = self.local(oc);
                let pre = self.local(USIZE);
                if !back {
                    let r = self.ref_to(false, f(0), CHARS);
                    self.call_builtin(Builtin::CharsBytesLeft, vec![Operand::Move(Place::local(r))], Place::local(pre));
                }
                let rm = self.ref_to(true, f(0), CHARS);
                let b = if back { Builtin::CharsNextBack } else { Builtin::CharsNext };
                self.call_builtin(b, vec![Operand::Move(Place::local(rm))], Place::local(x));
                let (s, n) = self.switch_opt(&Place::local(x));
                self.cur = s;
                let left = self.local(USIZE);
                let r2 = self.ref_to(false, f(0), CHARS);
                self.call_builtin(Builtin::CharsBytesLeft, vec![Operand::Move(Place::local(r2))], Place::local(left));
                let idx = self.local(USIZE);
                if back {
                    self.assign(Place::local(idx), Rvalue::Bin(Add, Operand::Copy(f(1)), Operand::Copy(Place::local(left))));
                } else {
                    self.assign(Place::local(idx), Rvalue::Use(Operand::Copy(f(1))));
                    let used = self.local(USIZE);
                    self.assign(Place::local(used), Rvalue::Bin(Sub, Operand::Copy(Place::local(pre)), Operand::Copy(Place::local(left))));
                    self.assign(f(1), Rvalue::Bin(Add, Operand::Copy(f(1)), Operand::Copy(Place::local(used))));
                }
                let pair = self.tuple_ty(&[USIZE, CHAR]);
                let t = self.local(pair);
                self.assign(Place::local(t), Rvalue::TupleAgg(pair, vec![Operand::Copy(Place::local(idx)), Operand::Copy(Self::payload(&Place::local(x)))]));
                self.some(&dest, opt, Operand::Move(Place::local(t)));
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            // The wrapped iterator's own `next` (W-STD-B): forward only.
            K::ByNext if let Some(inner) = self.by_mut_builtin(a[0]) => {
                let at = self.by_mut_place(a[0], f(0));
                self.next(at, inner, dest, back)?;
                self.goto(join);
            }
            K::ByNext => {
                let (inner, at) = self.by_next_held(a[0], f(0));
                let fns = crate::check::iter::by_next_fns(self.p, &self.body.tys, inner)?;
                let step = if back { fns.next_back.ok_or("iterator expansion: no `next_back`")? } else { fns.next };
                let r = self.ref_to(true, at, inner);
                self.call(CallTarget::Fn(step), vec![Operand::Move(Place::local(r))], dest);
                self.goto(join);
            }
            // The hash iterators step in the core (cgen/hash.rs, W-STD-B);
            // none is double-ended.
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
            | K::SetDrain => {
                let r = self.ref_to(true, itp, ty);
                self.call_builtin(Builtin::HashIterNext, vec![Operand::Move(Place::local(r))], dest);
                self.goto(join);
            }
            K::VecDrain | K::StringDrain => {
                let r = self.ref_to(true, itp, ty);
                let b = match (k, back) {
                    (K::VecDrain, false) => Builtin::VecDrainNext,
                    (K::VecDrain, true) => Builtin::VecDrainNextBack,
                    (_, false) => Builtin::StrDrainNext,
                    _ => Builtin::StrDrainNextBack,
                };
                self.call_builtin(b, vec![Operand::Move(Place::local(r))], dest);
                self.goto(join);
            }
            K::RangeFrom if !back => {
                self.range_from_next(itp, a[0], dest)?;
                self.goto(join);
            }
            K::RangeFrom | K::RangeTo | K::RangeFull | K::RangeToInclusive => {
                return Err("iterator expansion: next on an open-ended range kind".into());
            }
            K::Range => {
                let c = self.cmp(Lt, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (s, n) = self.branch(c);
                self.cur = s;
                let one = Self::one(a[0], &self.body.tys)?;
                let v = self.local(a[0]);
                if back {
                    self.assign(f(1), Rvalue::Bin(Sub, Operand::Copy(f(1)), one));
                    self.assign(Place::local(v), Rvalue::Use(Operand::Copy(f(1))));
                } else {
                    self.assign(Place::local(v), Rvalue::Use(Operand::Copy(f(0))));
                    self.assign(f(0), Rvalue::Bin(Add, Operand::Copy(f(0)), one));
                }
                self.some(&dest, opt, Operand::Copy(Place::local(v)));
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::RangeInclusive => {
                let none_b = self.block();
                let (ex, live) = self.branch(Operand::Copy(f(2)));
                self.cur = ex;
                self.goto(none_b);
                self.cur = live;
                let c = self.cmp(Le, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (go, empty) = self.branch(c);
                self.cur = empty;
                self.goto(none_b);
                self.cur = go;
                let lt = self.cmp(Lt, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (step, last) = self.branch(lt);
                let one = Self::one(a[0], &self.body.tys)?;
                let v = self.local(a[0]);
                self.cur = step;
                if back {
                    self.assign(Place::local(v), Rvalue::Use(Operand::Copy(f(1))));
                    self.assign(f(1), Rvalue::Bin(Sub, Operand::Copy(f(1)), one));
                } else {
                    self.assign(Place::local(v), Rvalue::Use(Operand::Copy(f(0))));
                    self.assign(f(0), Rvalue::Bin(Add, Operand::Copy(f(0)), one));
                }
                self.some(&dest, opt, Operand::Copy(Place::local(v)));
                self.goto(join);
                self.cur = last;
                self.some(&dest, opt, Operand::Copy(if back { f(1) } else { f(0) }));
                if self.fold {
                    // core's `spec_try_fold` (`try_rfold`): the last
                    // item sets `exhausted` and leaves the cursor.
                    self.assign(f(2), Rvalue::Use(Operand::Const(Const::Bool(true))));
                } else {
                    // `next`: the cursor steps past the end it came
                    // from, wrapping, and `exhausted` is the overflow
                    // (`Step::forward_overflowing`), as std's fields do
                    // (observable through `start()`, `end()`,
                    // `end_bound`, and `contains`).
                    let (cur, b, wrapped) = if back { (f(1), Builtin::WrappingSub, Gt) } else { (f(0), Builtin::WrappingAdd, Lt) };
                    let t = self.local(a[0]);
                    let one = Self::one(a[0], &self.body.tys)?;
                    self.call_builtin(b, vec![Operand::Copy(cur.clone()), one], Place::local(t));
                    let o = self.cmp(wrapped, Operand::Copy(Place::local(t)), Operand::Copy(cur.clone()));
                    self.assign(f(2), Rvalue::Use(o));
                    self.assign(cur, Rvalue::Use(Operand::Copy(Place::local(t))));
                }
                self.goto(join);
                self.cur = none_b;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Map | K::Inspect | K::Copied | K::Cloned => {
                let inner_item = self.item(a[0])?;
                let iopt = self.body.tys.mk_option(inner_item);
                let t = self.local(iopt);
                self.next(f(0), a[0], Place::local(t), back)?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = s;
                let x = self.local(inner_item);
                let px = self.take(Self::payload(&Place::local(t)), inner_item);
                self.assign(Place::local(x), Rvalue::Use(px));
                match k {
                    K::Map => {
                        let fty = a[1];
                        let y = self.local(item);
                        let ax = self.take(Place::local(x), inner_item);
                        self.call_fn(fty, f(1), vec![ax], Place::local(y))?;
                        let ay = self.take(Place::local(y), item);
                        self.some(&dest, opt, ay);
                    }
                    K::Inspect => {
                        let rx = self.ref_to(false, Place::local(x), inner_item);
                        let u = self.local(UNIT);
                        self.call_fn(a[1], f(1), vec![Operand::Move(Place::local(rx))], Place::local(u))?;
                        let ax = self.take(Place::local(x), item);
                        self.some(&dest, opt, ax);
                    }
                    K::Copied => self.some(&dest, opt, Operand::Copy(Place::local(x).deref())),
                    _ => {
                        let y = self.local(item);
                        self.call_builtin(Builtin::Clone, vec![Operand::Copy(Place::local(x))], Place::local(y));
                        let ay = self.take(Place::local(y), item);
                        self.some(&dest, opt, ay);
                    }
                }
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Filter | K::SkipWhile => {
                // Pull until the predicate keeps an item; rejected items
                // drop right away. std's `next` here is `self.iter.find(..)`
                // (`rfind` back), so the pulls are `try_fold` steps.
                let lp = self.block();
                self.goto(lp);
                self.cur = lp;
                let t = self.local(opt);
                let saved = std::mem::replace(&mut self.fold, true);
                let pulled = self.next(f(0), a[0], Place::local(t), back);
                self.fold = saved;
                pulled?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
                self.cur = s;
                let x = self.local(item);
                let px = self.take(Self::payload(&Place::local(t)), item);
                self.assign(Place::local(x), Rvalue::Use(px));
                let (keep, skip) = if k == K::Filter {
                    let rx = self.ref_to(false, Place::local(x), item);
                    let b = self.local(BOOL);
                    self.call_fn(a[1], f(1), vec![Operand::Move(Place::local(rx))], Place::local(b))?;
                    self.branch(Operand::Copy(Place::local(b)))
                } else {
                    // `*flag || !pred(x)` keeps the item and sets the flag.
                    let keep = self.block();
                    let (flagged, open) = self.branch(Operand::Copy(f(1)));
                    self.cur = flagged;
                    self.goto(keep);
                    self.cur = open;
                    let rx = self.ref_to(false, Place::local(x), item);
                    let b = self.local(BOOL);
                    self.call_fn(a[1], f(2), vec![Operand::Move(Place::local(rx))], Place::local(b))?;
                    let (skip, k2) = self.branch(Operand::Copy(Place::local(b)));
                    self.cur = k2;
                    self.assign(f(1), Rvalue::Use(Operand::Const(Const::Bool(true))));
                    self.goto(keep);
                    (keep, skip)
                };
                self.cur = keep;
                let ax = self.take(Place::local(x), item);
                self.some(&dest, opt, ax);
                self.goto(join);
                self.cur = skip;
                self.drop_local(x);
                self.goto(lp);
            }
            K::FilterMap => {
                // std: `self.iter.find_map(..)`, `try_fold` steps as Filter.
                let inner_item = self.item(a[0])?;
                let iopt = self.body.tys.mk_option(inner_item);
                let lp = self.block();
                self.goto(lp);
                self.cur = lp;
                let t = self.local(iopt);
                let saved = std::mem::replace(&mut self.fold, true);
                let pulled = self.next(f(0), a[0], Place::local(t), back);
                self.fold = saved;
                pulled?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
                self.cur = s;
                let px = self.take(Self::payload(&Place::local(t)), inner_item);
                let o = self.local(opt);
                self.call_fn(a[1], f(1), vec![px], Place::local(o))?;
                let (hit, miss) = self.switch_opt(&Place::local(o));
                self.cur = hit;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(o))));
                self.goto(join);
                self.cur = miss;
                self.goto(lp);
            }
            // The try-collect wrapper (F3; core's `ProcessResults`):
            // yield the value inside each `Ok` or `Some`; at the
            // first `Err` or `None`, store it in field 1 and end.
            // Once failed, later pulls end at once without pulling
            // the source, as std's `next` checks the stored error.
            K::TryCollect => {
                if back {
                    return Err("iterator expansion: TryCollect is forward-only here".into());
                }
                let inner_item = self.item(a[0])?;
                let (failed, go) = self.switch_opt(&f(1));
                self.cur = failed;
                self.none(&dest, opt);
                self.goto(join);
                self.cur = go;
                let iopt = self.body.tys.mk_option(inner_item);
                let t = self.local(iopt);
                self.next(f(0), a[0], Place::local(t), false)?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
                self.cur = s;
                let x = self.local(inner_item);
                let px = self.take(Self::payload(&Place::local(t)), inner_item);
                self.assign(Place::local(x), Rvalue::Use(px));
                let err_ty = a[1];
                let opt_err = self.body.tys.mk_option(err_ty);
                if self.body.tys.result_args(inner_item).is_some() {
                    // `Ok` is discriminant 0, `Err` 1 (place_ty).
                    let d = self.local(int(IntTy::U32));
                    self.assign(Place::local(d), Rvalue::Discriminant(Place::local(x)));
                    let (ok, bad) = (self.block(), self.block());
                    self.term(Terminator::Switch(Operand::Copy(Place::local(d)), vec![(0, ok)], bad));
                    self.cur = ok;
                    let v = self.take(Place::local(x).project(Proj::Downcast(0)).project(Proj::Field(0)), item);
                    self.some(&dest, opt, v);
                    self.goto(join);
                    self.cur = bad;
                    let ev = self.take(Place::local(x).project(Proj::Downcast(1)).project(Proj::Field(0)), err_ty);
                    self.some(&f(1), opt_err, ev);
                    self.none(&dest, opt);
                    self.goto(join);
                } else {
                    let (some, none) = self.switch_opt(&Place::local(x));
                    self.cur = some;
                    let v = self.take(Self::payload(&Place::local(x)), item);
                    self.some(&dest, opt, v);
                    self.goto(join);
                    self.cur = none;
                    self.some(&f(1), opt_err, Operand::Const(Const::Unit));
                    self.none(&dest, opt);
                    self.goto(join);
                }
            }
            // `next_back` (`I: DoubleEndedIterator + ExactSizeIterator`):
            // the inner's back item at index `count + inner.len()`, the
            // length read after the pull, as core does.
            K::Enumerate if back => {
                let inner_item = self.item(a[0])?;
                let iopt = self.body.tys.mk_option(inner_item);
                let t = self.local(iopt);
                self.next(f(0), a[0], Place::local(t), true)?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = s;
                let (len, _) = self.hint(f(0), a[0])?;
                let i = self.local(USIZE);
                self.assign(Place::local(i), Rvalue::Bin(Add, Operand::Copy(f(1)), Operand::Copy(Place::local(len))));
                let px = self.take(Self::payload(&Place::local(t)), inner_item);
                let tup = self.local(item);
                self.assign(Place::local(tup), Rvalue::TupleAgg(item, vec![Operand::Copy(Place::local(i)), px]));
                let at = self.take(Place::local(tup), item);
                self.some(&dest, opt, at);
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Enumerate => {
                let inner_item = self.item(a[0])?;
                let iopt = self.body.tys.mk_option(inner_item);
                let t = self.local(iopt);
                self.next(f(0), a[0], Place::local(t), false)?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = s;
                let i = self.local(USIZE);
                self.assign(Place::local(i), Rvalue::Use(Operand::Copy(f(1))));
                self.assign(f(1), Rvalue::Bin(Add, Operand::Copy(f(1)), Self::usize_c(1)));
                let px = self.take(Self::payload(&Place::local(t)), inner_item);
                let tup = self.local(item);
                self.assign(Place::local(tup), Rvalue::TupleAgg(item, vec![Operand::Copy(Place::local(i)), px]));
                let at = self.take(Place::local(tup), item);
                self.some(&dest, opt, at);
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Rev => {
                self.next(f(0), a[0], dest, !back)?;
                self.goto(join);
            }
            K::Take => {
                if back {
                    return Err("iterator expansion: Take is forward-only here".into());
                }
                let c = self.cmp(Ne, Operand::Copy(f(1)), Self::usize_c(0));
                let (s, n) = self.branch(c);
                self.cur = s;
                if self.fold {
                    // `try_fold`: the count drops per item the inner yields.
                    self.next(f(0), a[0], dest.clone(), false)?;
                    let (got, end) = self.switch_opt(&dest);
                    self.cur = got;
                    self.assign(f(1), Rvalue::Bin(Sub, Operand::Copy(f(1)), Self::usize_c(1)));
                    self.goto(join);
                    self.cur = end;
                } else {
                    self.assign(f(1), Rvalue::Bin(Sub, Operand::Copy(f(1)), Self::usize_c(1)));
                    self.next(f(0), a[0], dest.clone(), false)?;
                }
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            // `next_back` (`I: DoubleEndedIterator + ExactSizeIterator`):
            // the inner's back item while `len() > 0`, with `len` the
            // inner's minus the items still to skip (saturating).
            K::Skip if back => {
                let (len, _) = self.hint(itp.clone(), ty)?;
                let c = self.cmp(Lt, Self::usize_c(0), Operand::Copy(Place::local(len)));
                let (s, n) = self.branch(c);
                self.cur = s;
                self.next(f(0), a[0], dest.clone(), true)?;
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Skip => {
                let c = self.cmp(Lt, Self::usize_c(0), Operand::Copy(f(1)));
                let (s, n) = self.branch(c);
                // Each inner op has one expansion, so the code grows
                // linearly with nested `Skip`s (fx-cgen-ice).
                let pull = self.block();
                self.cur = s;
                let cnt = self.local(USIZE);
                if self.fold {
                    // `try_fold`: `nth(n - 1)` drops the skipped items, an
                    // end there ends the fold, then the inner's own items.
                    self.assign(Place::local(cnt), Rvalue::Bin(Sub, Operand::Copy(f(1)), Self::usize_c(1)));
                    self.assign(f(1), Rvalue::Use(Self::usize_c(0)));
                    let t = self.local(opt);
                    self.nth(f(0), a[0], cnt, Place::local(t))?;
                    let (got, end) = self.switch_opt(&Place::local(t));
                    self.cur = end;
                    self.none(&dest, opt);
                    self.goto(join);
                    self.cur = got;
                    self.drop_local(t);
                    self.goto(pull);
                } else {
                    self.assign(Place::local(cnt), Rvalue::Use(Operand::Copy(f(1))));
                    self.assign(f(1), Rvalue::Use(Self::usize_c(0)));
                    self.nth(f(0), a[0], cnt, dest.clone())?;
                    self.goto(join);
                }
                self.cur = n;
                self.goto(pull);
                self.cur = pull;
                self.next(f(0), a[0], dest, false)?;
                self.goto(join);
            }
            K::StepBy => {
                if back {
                    return Err("iterator expansion: StepBy is forward-only here".into());
                }
                // `nth(if first_take { 0 } else { step_minus_one })`.
                let step = self.local(USIZE);
                let (first, later) = self.branch(Operand::Copy(f(2)));
                let go = self.block();
                self.cur = first;
                self.assign(Place::local(step), Rvalue::Use(Self::usize_c(0)));
                self.goto(go);
                self.cur = later;
                self.assign(Place::local(step), Rvalue::Use(Operand::Copy(f(1))));
                self.goto(go);
                self.cur = go;
                self.assign(f(2), Rvalue::Use(Operand::Const(Const::Bool(false))));
                self.nth(f(0), a[0], step, dest)?;
                self.goto(join);
            }
            K::Chain => {
                let (first, second) = if back { (1u32, 0u32) } else { (0, 1) };
                let other = self.block();
                let (fs, fnone) = self.switch_opt(&f(first));
                self.cur = fnone;
                self.goto(other);
                self.cur = fs;
                let t = self.local(opt);
                self.next(Self::payload(&f(first)), a[first as usize], Place::local(t), back)?;
                let (hit, done) = self.switch_opt(&Place::local(t));
                self.cur = hit;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(t))));
                self.goto(join);
                self.cur = done;
                // `and_then_or_clear`: the spent side drops now.
                let fty = self.place_ty(&f(first))?;
                self.none(&f(first), fty);
                self.goto(other);
                self.cur = other;
                let (ss, snone) = self.switch_opt(&f(second));
                self.cur = ss;
                self.next(Self::payload(&f(second)), a[second as usize], dest.clone(), back)?;
                self.goto(join);
                self.cur = snone;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Zip if back => self.zip_next_back(&itp, &a, &dest, opt, join)?,
            K::Zip => {
                let (ia, ib) = (self.item(a[0])?, self.item(a[1])?);
                if self.tra_coerce(a[0]) && self.tra_coerce(a[1]) {
                    // Both sides random access (Rust's `Zip` over two
                    // `TrustedRandomAccess` sides; with only the
                    // `NoCoerce` form, `next` is the general one and
                    // `fold` reads by index, see `fold_differs`): the length fixed at
                    // `zip` creation bounds the pulls, so each side is
                    // pulled exactly `len` times. Pulling with `next`
                    // gives the same items and side effects as std's
                    // indexed reads, and it advances each side, so a
                    // side that owns its items (an `array::IntoIter`
                    // of non-`Copy` elements) drops only what it has
                    // not yielded when the zip drops.
                    let c = self.cmp(Lt, Operand::Copy(f(2)), Operand::Copy(f(3)));
                    let (s, n) = self.branch(c);
                    self.cur = s;
                    self.assign(f(2), Rvalue::Bin(Add, Operand::Copy(f(2)), Self::usize_c(1)));
                    let (oa, ob) = (self.body.tys.mk_option(ia), self.body.tys.mk_option(ib));
                    let (ta, tb) = (self.local(oa), self.local(ob));
                    self.next(f(0), a[0], Place::local(ta), false)?;
                    self.next(f(1), a[1], Place::local(tb), false)?;
                    let ax = self.take(Self::payload(&Place::local(ta)), ia);
                    let ay = self.take(Self::payload(&Place::local(tb)), ib);
                    let tup = self.local(item);
                    self.assign(Place::local(tup), Rvalue::TupleAgg(item, vec![ax, ay]));
                    let at = self.take(Place::local(tup), item);
                    self.some(&dest, opt, at);
                    self.goto(join);
                    self.cur = n;
                    self.none(&dest, opt);
                    self.goto(join);
                } else {
                    let none_b = self.block();
                    let (oa, ob) = (self.body.tys.mk_option(ia), self.body.tys.mk_option(ib));
                    let ta = self.local(oa);
                    self.next(f(0), a[0], Place::local(ta), false)?;
                    let (s, n) = self.switch_opt(&Place::local(ta));
                    self.cur = n;
                    self.goto(none_b);
                    self.cur = s;
                    let x = self.local(ia);
                    let px = self.take(Self::payload(&Place::local(ta)), ia);
                    self.assign(Place::local(x), Rvalue::Use(px));
                    let tb = self.local(ob);
                    self.next(f(1), a[1], Place::local(tb), false)?;
                    let (s2, n2) = self.switch_opt(&Place::local(tb));
                    self.cur = n2;
                    self.drop_local(x);
                    self.goto(none_b);
                    self.cur = s2;
                    let py = self.take(Self::payload(&Place::local(tb)), ib);
                    let ax = self.take(Place::local(x), ia);
                    let tup = self.local(item);
                    self.assign(Place::local(tup), Rvalue::TupleAgg(item, vec![ax, py]));
                    let at = self.take(Place::local(tup), item);
                    self.some(&dest, opt, at);
                    self.goto(join);
                    self.cur = none_b;
                    self.none(&dest, opt);
                    self.goto(join);
                }
            }
            // core's `let x = self.iter.next()?; (self.predicate)(x)`:
            // not fused, so a pull after a `None` from the predicate
            // pulls the inner iterator again.
            K::MapWhile => {
                if back {
                    return Err("iterator expansion: MapWhile is forward-only".into());
                }
                let inner_item = self.item(a[0])?;
                let iopt = self.body.tys.mk_option(inner_item);
                let t = self.local(iopt);
                self.next(f(0), a[0], Place::local(t), false)?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = s;
                let px = self.take(Self::payload(&Place::local(t)), inner_item);
                self.call_fn(a[1], f(1), vec![px], dest.clone())?;
                self.goto(join);
                self.cur = n;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::TakeWhile => {
                if back {
                    return Err("iterator expansion: TakeWhile is forward-only".into());
                }
                let none_b = self.block();
                let (done, open) = self.branch(Operand::Copy(f(1)));
                self.cur = done;
                self.goto(none_b);
                self.cur = open;
                let t = self.local(opt);
                self.next(f(0), a[0], Place::local(t), false)?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = n;
                self.goto(none_b);
                self.cur = s;
                let x = self.local(item);
                let px = self.take(Self::payload(&Place::local(t)), item);
                self.assign(Place::local(x), Rvalue::Use(px));
                let rx = self.ref_to(false, Place::local(x), item);
                let b = self.local(BOOL);
                self.call_fn(a[1], f(2), vec![Operand::Move(Place::local(rx))], Place::local(b))?;
                let (keep, stop) = self.branch(Operand::Copy(Place::local(b)));
                self.cur = keep;
                let ax = self.take(Place::local(x), item);
                self.some(&dest, opt, ax);
                self.goto(join);
                self.cur = stop;
                self.assign(f(1), Rvalue::Use(Operand::Const(Const::Bool(true))));
                self.drop_local(x);
                self.goto(none_b);
                self.cur = none_b;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Peekable if back => {
                // `match self.peeked.as_mut() { Some(v @ Some(_)) => self.iter.next_back().or_else(|| v.take()),
                //  Some(None) => None, None => self.iter.next_back() }`
                let slot = f(1);
                let (s, n) = self.switch_opt(&slot);
                self.cur = n;
                self.next(f(0), a[0], dest.clone(), true)?;
                self.goto(join);
                self.cur = s;
                let inner = Self::payload(&slot);
                let (full, spent) = self.switch_opt(&inner);
                self.cur = spent;
                self.none(&dest, opt);
                self.goto(join);
                self.cur = full;
                let t = self.local(opt);
                self.next(f(0), a[0], Place::local(t), true)?;
                let (hit, miss) = self.switch_opt(&Place::local(t));
                self.cur = hit;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(t))));
                self.goto(join);
                self.cur = miss;
                self.take_none(inner.clone(), opt, dest.clone());
                self.goto(join);
            }
            K::Peekable => {
                // `match self.peeked.take() { Some(v) => v, None => self.iter.next() }`
                let slot = f(1);
                let (s, n) = self.switch_opt(&slot);
                self.cur = s;
                let pty = self.place_ty(&slot)?;
                let o = self.local(pty);
                self.take_none(slot.clone(), pty, Place::local(o));
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Self::payload(&Place::local(o)))));
                self.goto(join);
                self.cur = n;
                self.next(f(0), a[0], dest, false)?;
                self.goto(join);
            }
        }
        self.cur = join;
        Ok(())
    }

    /// `Zip::next_back` (core 1.99 zip.rs, R22). Both sides are
    /// double-ended and exact size (check/iter.rs `double_ended`).
    ///
    /// Two `TrustedRandomAccess` sides: core reads index `len - 1` of
    /// each side after one trim of the longer side's back to `len`
    /// (only a side that may have side effects is trimmed). lust's
    /// sides are pulled from the front on each `next` (see the forward
    /// arm), so a side holds `size + index` of core's elements: each
    /// side is trimmed back to `len` with `next_back` (on a side without
    /// side effects this is not observable), then one `next_back` of
    /// each side is core's indexed read.
    ///
    /// Otherwise core's general `next_back`: trim the longer side by the
    /// `len` difference, then `next_back` both.
    fn zip_next_back(&mut self, itp: &Place, a: &[Ty], dest: &Place, opt: Ty, join: Bb) -> R {
        use crate::ast::BinOp::*;
        let f = |i: u32| itp.project(Proj::Field(i));
        let (ia, ib) = (self.item(a[0])?, self.item(a[1])?);
        if self.tra_coerce(a[0]) && self.tra_coerce(a[1]) {
            let c = self.cmp(Lt, Operand::Copy(f(2)), Operand::Copy(f(3)));
            let (go, spent) = self.branch(c);
            self.cur = spent;
            self.none(dest, opt);
            self.goto(join);
            self.cur = go;
            let want = self.local(USIZE);
            self.assign(Place::local(want), Rvalue::Bin(Sub, Operand::Copy(f(3)), Operand::Copy(f(2))));
            self.assign(f(3), Rvalue::Bin(Sub, Operand::Copy(f(3)), Self::usize_c(1)));
            // Two slice sides: core's indexed read of each at `len - 1`, in place. A slice side
            // has no side effects and owns nothing, and its front is at the zip's index (the
            // forward arm pulls it once a step), so that element is its `want - 1`; the trim
            // and the pull of the general form only move its back.
            if [a[0], a[1]].iter().all(|&t| matches!(self.kind_args(t), Some((IterKind::SliceIter | IterKind::SliceIterMut, _)))) {
                let k = self.local(USIZE);
                self.assign(Place::local(k), Rvalue::Bin(Sub, Operand::Copy(Place::local(want)), Self::usize_c(1)));
                let mut xs = Vec::new();
                for i in 0..2 {
                    let (sk, sa) = self.kind_args(a[i]).ok_or("iterator expansion: bad Zip side")?;
                    // A slice iterator's field 0 is its slice (`next`).
                    let r = self.ref_to(sk == IterKind::SliceIterMut, f(i as u32).project(Proj::Field(0)).deref().project(Proj::Index(k)), sa[0]);
                    xs.push(Operand::Move(Place::local(r)));
                }
                let ts = self.body.tys.intern_tys(&[ia, ib]);
                let item = self.body.tys.intern(TyKind::Tuple(ts));
                let tup = self.local(item);
                self.assign(Place::local(tup), Rvalue::TupleAgg(item, xs));
                let at = self.take(Place::local(tup), item);
                self.some(dest, opt, at);
                self.goto(join);
                return Ok(());
            }
            for i in 0..2 {
                let sz = self.size(f(i), a[i as usize])?;
                let n = self.local(USIZE);
                self.assign(Place::local(n), Rvalue::Bin(Sub, sz, Operand::Copy(Place::local(want))));
                self.drop_back_n(f(i), a[i as usize], n)?;
            }
        } else {
            let (al, _) = self.hint(f(0), a[0])?;
            let (bl, _) = self.hint(f(1), a[1])?;
            let (na, nb) = (self.local(USIZE), self.local(USIZE));
            self.call_builtin(Builtin::SaturatingSub, vec![Operand::Copy(Place::local(al)), Operand::Copy(Place::local(bl))], Place::local(na));
            self.call_builtin(Builtin::SaturatingSub, vec![Operand::Copy(Place::local(bl)), Operand::Copy(Place::local(al))], Place::local(nb));
            self.drop_back_n(f(0), a[0], na)?;
            self.drop_back_n(f(1), a[1], nb)?;
        }
        let (oa, ob) = (self.body.tys.mk_option(ia), self.body.tys.mk_option(ib));
        let (ta, tb) = (self.local(oa), self.local(ob));
        self.next(f(0), a[0], Place::local(ta), true)?;
        self.next(f(1), a[1], Place::local(tb), true)?;
        let (sa, na) = self.switch_opt(&Place::local(ta));
        self.cur = sa;
        let (sb, nb) = self.switch_opt(&Place::local(tb));
        self.cur = sb;
        let ts = self.body.tys.intern_tys(&[ia, ib]);
        let item = self.body.tys.intern(TyKind::Tuple(ts));
        let ax = self.take(Self::payload(&Place::local(ta)), ia);
        let ay = self.take(Self::payload(&Place::local(tb)), ib);
        let tup = self.local(item);
        self.assign(Place::local(tup), Rvalue::TupleAgg(item, vec![ax, ay]));
        let at = self.take(Place::local(tup), item);
        self.some(dest, opt, at);
        self.goto(join);
        // Equal lengths make both sides end together; the mixed case
        // (core's `unreachable!`) cannot happen over exact sides.
        self.cur = nb;
        self.drop_local(ta);
        self.none(dest, opt);
        self.goto(join);
        self.cur = na;
        self.drop_local(tb);
        self.none(dest, opt);
        self.goto(join);
        Ok(())
    }

    /// core's `for _ in 0..n { s.next_back(); }`: each item drops at once.
    fn drop_back_n(&mut self, s: Place, st: Ty, n: Local) -> R {
        use crate::ast::BinOp::*;
        let item = self.item(st)?;
        let opt = self.body.tys.mk_option(item);
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        let c = self.cmp(Gt, Operand::Copy(Place::local(n)), Self::usize_c(0));
        let (go, end) = self.branch(c);
        self.cur = go;
        self.assign(Place::local(n), Rvalue::Bin(Sub, Operand::Copy(Place::local(n)), Self::usize_c(1)));
        let t = self.local(opt);
        self.next(s.clone(), st, Place::local(t), true)?;
        self.drop_local(t);
        self.goto(lp);
        self.cur = end;
        Ok(())
    }

    /// The integer 1 of a range element type.
    /// One `next` (or `next_back`) of a slice split into `dest`, ending
    /// in `join`: core's `Split`, `RSplit` (`Split` from the other
    /// end), `SplitInclusive`, and `GenericSplitN` over `Split` or
    /// `RSplit`, with their `_mut` twins. Fields (v, pred, finished,
    /// count). The predicate sees `&v[i]` in core's search order
    /// (`position` front to back, `rposition` back to front).
    #[allow(clippy::too_many_arguments)]
    fn slice_split_next(&mut self, itp: &Place, k: IterKind, a: &[Ty], back: bool, dest: &Place, opt: Ty, join: Bb) -> R {
        use crate::ast::BinOp::*;
        use crate::ty::iter::SliceSplitMode as M;
        let mode = it::slice_split_mode(&self.body.tys, a[2]).ok_or("iterator expansion: bad slice split mode")?;
        let f = |i: u32| itp.project(Proj::Field(i));
        if matches!(mode, M::SplitN | M::RSplitN) {
            // `GenericSplitN::next`: no item once the count is 0; the
            // last counted item is the inner iterator's `finish`.
            let c = self.cmp(Eq, Operand::Copy(f(3)), Self::usize_c(0));
            let (spent, go) = self.branch(c);
            self.cur = spent;
            self.none(dest, opt);
            self.goto(join);
            self.cur = go;
            self.assign(f(3), Rvalue::Bin(Sub, Operand::Copy(f(3)), Self::usize_c(1)));
            let c = self.cmp(Eq, Operand::Copy(f(3)), Self::usize_c(0));
            let (last, more) = self.branch(c);
            self.cur = last;
            self.slice_split_finish(itp, dest, opt, join);
            self.cur = more;
            return self.slice_split_step(itp, k, a, mode == M::RSplitN, false, dest, opt, join);
        }
        self.slice_split_step(itp, k, a, back != (mode == M::RSplit), mode == M::SplitInclusive, dest, opt, join)
    }

    /// One `next` (or `next_back`) of `ChunkBy` or `ChunkByMut`, as core
    /// writes it: the run grows while the predicate holds for the pair
    /// at its edge (`windows(2)` from the front or the back), then the
    /// run splits off. Fields (slice, predicate).
    #[allow(clippy::too_many_arguments)]
    fn chunk_by_next(&mut self, itp: &Place, k: IterKind, a: &[Ty], back: bool, dest: &Place, opt: Ty, join: Bb) -> R {
        use crate::ast::BinOp::*;
        let m = k == IterKind::ChunkByMut;
        let f = |i: u32| itp.project(Proj::Field(i));
        let sd = f(0).deref();
        let len = self.local(USIZE);
        self.assign(Place::local(len), Rvalue::LenOf(sd.clone()));
        let c = self.cmp(Eq, Operand::Copy(Place::local(len)), Self::usize_c(0));
        let (empty, go) = self.branch(c);
        self.cur = empty;
        self.none(dest, opt);
        self.goto(join);
        self.cur = go;
        // `n` is the run length; the pair checked next is (n - 1, n)
        // from the front, or (len - n - 1, len - n) from the back.
        let n = self.local(USIZE);
        self.assign(Place::local(n), Rvalue::Use(Self::usize_c(1)));
        let (head, body, done) = (self.block(), self.block(), self.block());
        self.goto(head);
        self.cur = head;
        let c = self.cmp(Lt, Operand::Copy(Place::local(n)), Operand::Copy(Place::local(len)));
        self.term(Terminator::If(c, body, done));
        self.cur = body;
        let (li, ri) = (self.local(USIZE), self.local(USIZE));
        if back {
            self.assign(Place::local(ri), Rvalue::Bin(Sub, Operand::Copy(Place::local(len)), Operand::Copy(Place::local(n))));
            self.assign(Place::local(li), Rvalue::Bin(Sub, Operand::Copy(Place::local(ri)), Self::usize_c(1)));
        } else {
            self.assign(Place::local(li), Rvalue::Bin(Sub, Operand::Copy(Place::local(n)), Self::usize_c(1)));
            self.assign(Place::local(ri), Rvalue::Use(Operand::Copy(Place::local(n))));
        }
        let l = self.ref_to(false, sd.project(Proj::Index(li)), a[0]);
        let r = self.ref_to(false, sd.project(Proj::Index(ri)), a[0]);
        let b = self.local(BOOL);
        self.call_fn(a[1], f(1), vec![Operand::Move(Place::local(l)), Operand::Move(Place::local(r))], Place::local(b))?;
        let grow = self.block();
        self.term(Terminator::If(Operand::Copy(Place::local(b)), grow, done));
        self.cur = grow;
        self.assign(Place::local(n), Rvalue::Bin(Add, Operand::Copy(Place::local(n)), Self::usize_c(1)));
        self.goto(head);
        self.cur = done;
        let st = self.place_ty(&f(0))?;
        let sub = |lo: Operand, hi: Option<Operand>| Rvalue::Subslice { base: sd.clone(), lo, hi, inclusive: false, mutable: m };
        let (ret, rest) = (self.local(st), self.local(st));
        if back {
            let at = self.local(USIZE);
            self.assign(Place::local(at), Rvalue::Bin(Sub, Operand::Copy(Place::local(len)), Operand::Copy(Place::local(n))));
            self.assign(Place::local(ret), sub(Operand::Copy(Place::local(at)), None));
            self.assign(Place::local(rest), sub(Self::usize_c(0), Some(Operand::Copy(Place::local(at)))));
        } else {
            self.assign(Place::local(ret), sub(Self::usize_c(0), Some(Operand::Copy(Place::local(n)))));
            self.assign(Place::local(rest), sub(Operand::Copy(Place::local(n)), None));
        }
        self.assign(f(0), Rvalue::Use(Operand::Move(Place::local(rest))));
        self.some(dest, opt, Operand::Move(Place::local(ret)));
        self.goto(join);
        Ok(())
    }

    /// `SplitIter::finish`: `None` once finished, else the rest of the
    /// slice (and finished).
    fn slice_split_finish(&mut self, itp: &Place, dest: &Place, opt: Ty, join: Bb) {
        let f = |i: u32| itp.project(Proj::Field(i));
        let (done, go) = self.branch(Operand::Copy(f(2)));
        self.cur = done;
        self.none(dest, opt);
        self.goto(join);
        self.cur = go;
        self.assign(f(2), Rvalue::Use(Operand::Const(Const::Bool(true))));
        self.some(dest, opt, Operand::Copy(f(0)));
        self.goto(join);
    }

    /// One step of `Split::next` (`from_back`: `next_back`) or of
    /// `SplitInclusive` (`inclusive`), as core writes them.
    #[allow(clippy::too_many_arguments)]
    fn slice_split_step(&mut self, itp: &Place, k: IterKind, a: &[Ty], from_back: bool, inclusive: bool, dest: &Place, opt: Ty, join: Bb) -> R {
        use crate::ast::BinOp::*;
        let m = k == IterKind::SliceSplitMut;
        let f = |i: u32| itp.project(Proj::Field(i));
        let (done, go) = self.branch(Operand::Copy(f(2)));
        self.cur = done;
        self.none(dest, opt);
        self.goto(join);
        self.cur = go;
        let sd = f(0).deref();
        let len = self.local(USIZE);
        self.assign(Place::local(len), Rvalue::LenOf(sd.clone()));
        // The search: `i` is the matching index on `found`.
        let i = self.local(USIZE);
        let (head, found, miss) = (self.block(), self.block(), self.block());
        if from_back {
            // `rposition`; `SplitInclusive` skips the last element,
            // which the previous step already matched.
            if inclusive {
                let c = self.cmp(Eq, Operand::Copy(Place::local(len)), Self::usize_c(0));
                let (empty, some) = self.branch(c);
                let set = self.block();
                self.cur = empty;
                self.assign(Place::local(i), Rvalue::Use(Self::usize_c(0)));
                self.goto(set);
                self.cur = some;
                self.assign(Place::local(i), Rvalue::Bin(Sub, Operand::Copy(Place::local(len)), Self::usize_c(1)));
                self.goto(set);
                self.cur = set;
            } else {
                self.assign(Place::local(i), Rvalue::Use(Operand::Copy(Place::local(len))));
            }
            self.goto(head);
            self.cur = head;
            let c = self.cmp(Lt, Self::usize_c(0), Operand::Copy(Place::local(i)));
            let body = self.block();
            self.term(Terminator::If(c, body, miss));
            self.cur = body;
            self.assign(Place::local(i), Rvalue::Bin(Sub, Operand::Copy(Place::local(i)), Self::usize_c(1)));
            let r = self.ref_to(false, sd.project(Proj::Index(i)), a[0]);
            let b = self.local(BOOL);
            self.call_fn(a[1], f(1), vec![Operand::Move(Place::local(r))], Place::local(b))?;
            self.term(Terminator::If(Operand::Copy(Place::local(b)), found, head));
        } else {
            // `position`.
            self.assign(Place::local(i), Rvalue::Use(Self::usize_c(0)));
            self.goto(head);
            self.cur = head;
            let c = self.cmp(Lt, Operand::Copy(Place::local(i)), Operand::Copy(Place::local(len)));
            let body = self.block();
            self.term(Terminator::If(c, body, miss));
            self.cur = body;
            let r = self.ref_to(false, sd.project(Proj::Index(i)), a[0]);
            let b = self.local(BOOL);
            self.call_fn(a[1], f(1), vec![Operand::Move(Place::local(r))], Place::local(b))?;
            let next = self.block();
            self.term(Terminator::If(Operand::Copy(Place::local(b)), found, next));
            self.cur = next;
            self.assign(Place::local(i), Rvalue::Bin(Add, Operand::Copy(Place::local(i)), Self::usize_c(1)));
            self.goto(head);
        }
        let st = self.place_ty(&f(0))?;
        let sub = |lo: Operand, hi: Option<Operand>| Rvalue::Subslice { base: sd.clone(), lo, hi, inclusive: false, mutable: m };
        let (ret, rest) = (self.local(st), self.local(st));
        if inclusive {
            // The split point `idx`: one past the match, or the end
            // (front) or 0 (back) on a miss; the iterator finishes
            // when it reaches that end.
            let idx = self.local(USIZE);
            let set = self.block();
            self.cur = found;
            self.assign(Place::local(idx), Rvalue::Bin(Add, Operand::Copy(Place::local(i)), Self::usize_c(1)));
            self.goto(set);
            self.cur = miss;
            let end = if from_back { Self::usize_c(0) } else { Operand::Copy(Place::local(len)) };
            self.assign(Place::local(idx), Rvalue::Use(end.clone()));
            self.goto(set);
            self.cur = set;
            let c = self.cmp(Eq, Operand::Copy(Place::local(idx)), end);
            let (fin, keep) = self.branch(c);
            let cont = self.block();
            self.cur = fin;
            self.assign(f(2), Rvalue::Use(Operand::Const(Const::Bool(true))));
            self.goto(cont);
            self.cur = keep;
            self.goto(cont);
            self.cur = cont;
            let at = Operand::Copy(Place::local(idx));
            if from_back {
                self.assign(Place::local(ret), sub(at.clone(), None));
                self.assign(Place::local(rest), sub(Self::usize_c(0), Some(at)));
            } else {
                self.assign(Place::local(ret), sub(Self::usize_c(0), Some(at.clone())));
                self.assign(Place::local(rest), sub(at, None));
            }
            self.assign(f(0), Rvalue::Use(Operand::Move(Place::local(rest))));
            self.some(dest, opt, Operand::Move(Place::local(ret)));
            self.goto(join);
            return Ok(());
        }
        // `Split`: a miss is `finish`; a match splits around index `i`.
        self.cur = miss;
        self.assign(f(2), Rvalue::Use(Operand::Const(Const::Bool(true))));
        self.some(dest, opt, Operand::Copy(f(0)));
        self.goto(join);
        self.cur = found;
        let after = self.local(USIZE);
        self.assign(Place::local(after), Rvalue::Bin(Add, Operand::Copy(Place::local(i)), Self::usize_c(1)));
        let (left, right) = (sub(Self::usize_c(0), Some(Operand::Copy(Place::local(i)))), sub(Operand::Copy(Place::local(after)), None));
        if from_back {
            self.assign(Place::local(ret), right);
            self.assign(Place::local(rest), left);
        } else {
            self.assign(Place::local(ret), left);
            self.assign(Place::local(rest), right);
        }
        self.assign(f(0), Rvalue::Use(Operand::Move(Place::local(rest))));
        self.some(dest, opt, Operand::Move(Place::local(ret)));
        self.goto(join);
        Ok(())
    }

    fn one(t: Ty, tys: &Tys) -> Result<Operand, String> {
        match tys.kind(t) {
            TyKind::Int(i) => Ok(Operand::Const(Const::Int(1, i))),
            _ => Err("iterator expansion: range over a non-integer".into()),
        }
    }

    /// `Peekable::peek`: fill the slot from `next` when it is empty,
    /// then a reference to the peeked item.
    fn peek(&mut self, itp: Place, ty: Ty, dest: Place, dest_ty: Ty) -> R {
        let (_, a) = self.kind_args(ty).ok_or("iterator expansion: peek on a non-Peekable")?;
        let item = self.item(ty)?;
        let opt = self.body.tys.mk_option(item);
        let slot = itp.project(Proj::Field(1));
        let pty = self.place_ty(&slot)?;
        let (full, empty) = self.switch_opt(&slot);
        self.cur = empty;
        let t = self.local(opt);
        self.next(itp.project(Proj::Field(0)), a[0], Place::local(t), false)?;
        self.some(&slot, pty, Operand::Move(Place::local(t)));
        self.goto(full);
        self.cur = full;
        let inner = Self::payload(&slot);
        let (s, n) = self.switch_opt(&inner);
        let join = self.block();
        self.cur = s;
        let r = self.ref_to(false, Self::payload(&inner), item);
        self.some(&dest, dest_ty, Operand::Move(Place::local(r)));
        self.goto(join);
        self.cur = n;
        self.none(&dest, dest_ty);
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// `Peekable::next_if` (and `next_if_eq`, whose test is
    /// `next == expected`): core's `match self.next() { Some(matched) if
    /// func(&matched) => Some(matched), other => { self.peeked =
    /// Some(other); None } }`. `func` runs at most once and drops before
    /// the call returns.
    fn next_if(&mut self, eq: bool, itp: Place, ty: Ty, f: Operand, dest: Place, dest_ty: Ty) -> R {
        let item = self.item(ty)?;
        let fty = self.op_ty(&f)?;
        let fl = self.local(fty);
        self.assign(Place::local(fl), Rvalue::Use(f));
        let t = self.local(dest_ty);
        self.next(itp.clone(), ty, Place::local(t), false)?;
        let slot = itp.project(Proj::Field(1));
        let pty = self.place_ty(&slot)?;
        let (join, back) = (self.block(), self.block());
        let (s, n) = self.switch_opt(&Place::local(t));
        self.cur = s;
        let rx = self.ref_to(false, Self::payload(&Place::local(t)), item);
        let b = self.local(BOOL);
        if eq {
            // `&Item == &T` with `T = Item` (check took one type).
            let rt = self.body.tys.mk_ref(false, item);
            self.item_eq(rx, rt, fl, b);
        } else {
            self.call_fn(fty, Place::local(fl), vec![Operand::Move(Place::local(rx))], Place::local(b))?;
        }
        let (yes, no) = self.branch(Operand::Copy(Place::local(b)));
        self.cur = yes;
        self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(t))));
        self.goto(join);
        self.cur = no;
        self.goto(back);
        self.cur = n;
        self.goto(back);
        // `next` emptied the slot: no old value to drop.
        self.cur = back;
        self.some(&slot, pty, Operand::Move(Place::local(t)));
        self.none(&dest, dest_ty);
        self.goto(join);
        self.cur = join;
        self.drop_local(fl);
        Ok(())
    }

    /// A fresh local holding an operand's value.
    fn copy_local(&mut self, v: Operand, ty: Ty) -> Local {
        let l = self.local(ty);
        self.assign(Place::local(l), Rvalue::Use(v));
        l
    }

    /// A fresh local holding `v` cast to `ty` (Rust `as` semantics).
    fn cast_local(&mut self, v: Operand, ty: Ty) -> Local {
        let l = self.local(ty);
        self.assign(Place::local(l), Rvalue::Cast(v, ty));
        l
    }

    /// The wide type range step math runs in, with the element's int
    /// type: `i128` for elements up to 64 bits (every sum and
    /// difference of two elements and a `usize` fits), `u128` bit
    /// patterns for 128-bit elements (Rust's wrapping step math).
    fn wide_ty(&self, elem: Ty) -> Result<(Ty, IntTy), String> {
        let TyKind::Int(it) = self.body.tys.kind(elem) else {
            return Err("iterator expansion: range over a non-integer".into());
        };
        Ok((if it.bits() <= 64 { int(IntTy::I128) } else { int(IntTy::U128) }, it))
    }

    /// Wide `a + b` or `a - b`: plain in `i128` (cannot overflow, see
    /// `wide_ty`), wrapping in `u128`.
    fn wide_bin(&mut self, sub: bool, a: Local, b: Local, w: Ty) -> Local {
        let l = self.local(w);
        if w == int(IntTy::I128) {
            let op = if sub { crate::ast::BinOp::Sub } else { crate::ast::BinOp::Add };
            self.assign(Place::local(l), Rvalue::Bin(op, Operand::Copy(Place::local(a)), Operand::Copy(Place::local(b))));
        } else {
            let f = if sub { Builtin::WrappingSub } else { Builtin::WrappingAdd };
            self.call_builtin(f, vec![Operand::Copy(Place::local(a)), Operand::Copy(Place::local(b))], Place::local(l));
        }
        l
    }

    /// The element type's MAX or MIN as a wide local.
    fn wide_bound(&mut self, it: IntTy, w: Ty, max: bool) -> Local {
        let bits = it.bits();
        let max_v: u128 = if it.signed() { (1u128 << (bits - 1)) - 1 } else if bits == 128 { u128::MAX } else { (1u128 << bits) - 1 };
        let wit = if w == int(IntTy::I128) { IntTy::I128 } else { IntTy::U128 };
        let max_l = self.copy_local(Operand::Const(Const::Int(max_v, wit)), w);
        if max {
            return max_l;
        }
        if !it.signed() {
            return self.copy_local(Operand::Const(Const::Int(0, wit)), w);
        }
        // MIN: -MAX - 1 in signed wide math; MAX + 1 in `u128` patterns
        // (the sign bit for `i128`).
        let one = self.cast_local(Self::usize_c(1), w);
        if w == int(IntTy::I128) {
            let zero = self.copy_local(Operand::Const(Const::Int(0, IntTy::I128)), w);
            let neg = self.wide_bin(true, zero, max_l, w);
            self.wide_bin(true, neg, one, w)
        } else {
            self.wide_bin(false, max_l, one, w)
        }
    }

    /// The default `nth`: `advance_by(n)` then `next` (or the back
    /// forms), as in Rust's `Iterator` and `DoubleEndedIterator`.
    fn nth_via_advance(&mut self, itp: Place, ty: Ty, n: Local, dest: Place, back: bool) -> R {
        let item = self.item(ty)?;
        let opt = self.body.tys.mk_option(item);
        if self.advance_is_loop(ty, back) && self.fold_pull_same(ty) {
            return self.nth_loop(itp, ty, n, dest, back);
        }
        let join = self.block();
        let rem = if back { self.advance_back(itp.clone(), ty, n)? } else { self.advance(itp.clone(), ty, n)? };
        let z = self.cmp(crate::ast::BinOp::Eq, Operand::Copy(Place::local(rem)), Self::usize_c(0));
        let (go, no) = self.branch(z);
        self.cur = go;
        self.next(itp, ty, dest.clone(), back)?;
        self.goto(join);
        self.cur = no;
        self.none(&dest, opt);
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// `nth_via_advance` when `advance_by` is the default pull loop and
    /// a `try_fold` pull is the same code as a `next` pull
    /// (`fold_pull_same`): `n + 1` pulls through one `next` site, the
    /// last one's item the result, as `advance_by(n)` then `next` pulls.
    /// Two sites would expand the inner chain twice, which made nested
    /// `Map`s or `Filter`s over `Skip` exponential in depth (fx-cgen-ice).
    fn nth_loop(&mut self, itp: Place, ty: Ty, n: Local, dest: Place, back: bool) -> R {
        use crate::ast::BinOp::*;
        let item = self.item(ty)?;
        let opt = self.body.tys.mk_option(item);
        let k = self.copy_local(Operand::Copy(Place::local(n)), USIZE);
        let join = self.block();
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        let t = self.local(opt);
        self.next(itp.clone(), ty, Place::local(t), back)?;
        let (s, none) = self.switch_opt(&Place::local(t));
        self.cur = none;
        self.none(&dest, opt);
        self.goto(join);
        self.cur = s;
        let z = self.cmp(Eq, Operand::Copy(Place::local(k)), Self::usize_c(0));
        let (hit, more) = self.branch(z);
        self.cur = hit;
        self.assign(dest, Rvalue::Use(Operand::Move(Place::local(t))));
        self.goto(join);
        self.cur = more;
        self.drop_local(t);
        self.assign(Place::local(k), Rvalue::Bin(Sub, Operand::Copy(Place::local(k)), Self::usize_c(1)));
        self.goto(lp);
        self.cur = join;
        Ok(())
    }

    /// True when `advance_by` (`advance_back_by` when `back`) on this
    /// type is the default pull loop (`advance_loop`): the kinds
    /// `advance` and `advance_back` do not override.
    fn advance_is_loop(&self, ty: Ty, back: bool) -> bool {
        use IterKind as K;
        if self.is_char_range(ty) {
            return false;
        }
        match self.kind_args(ty) {
            None => true,
            Some((k, _)) if back => !matches!(k, K::Range | K::Rev | K::Copied | K::Chain | K::RepeatN),
            Some((k, _)) => !matches!(k, K::Range | K::Skip | K::Take | K::Enumerate | K::Rev | K::Copied | K::Chain | K::RepeatN),
        }
    }

    /// True when `next` on this type expands the same with `fold` set as
    /// without it, so a `try_fold` pull and a `next` pull are the same
    /// code (`nth_loop`). Take, Skip, and RangeInclusive step differently
    /// under `fold` (`next_in`); Filter, FilterMap, and SkipWhile pull
    /// their inner with `fold` set either way, Zip and StepBy with it
    /// clear (`next`); the other adapters here pass it on. Other kinds
    /// answer false, which keeps the two-site form.
    fn fold_pull_same(&self, ty: Ty) -> bool {
        use IterKind as K;
        if self.is_char_range(ty) {
            return false;
        }
        let Some((k, a)) = self.kind_args(ty) else { return self.body.tys.is_chars_ty(ty) };
        match k {
            K::Filter | K::FilterMap | K::SkipWhile | K::Zip | K::StepBy => true,
            K::Map | K::MapWhile | K::Inspect | K::Copied | K::Cloned | K::Enumerate | K::Peekable | K::Rev | K::TakeWhile => self.fold_pull_same(a[0]),
            K::Chain | K::Flatten => self.fold_pull_same(a[0]) && self.fold_pull_same(a[1]),
            K::SliceIter | K::SliceIterMut | K::VecIntoIter | K::Range | K::RangeFrom | K::ArrayIntoIter | K::ByNext => true,
            _ => false,
        }
    }

    /// `dest = itp.nth(n)`, with Rust 1.99's per-kind overrides: the
    /// adapters Rust delegates through (`Skip`, `Take`, `Enumerate`,
    /// `Rev`, `Peekable`, `Copied`, `Chain`, `StepBy`) and the O(1)
    /// range forms. Other kinds take the default via `advance`. Its
    /// pulls are `next` steps, not `try_fold` ones (see `Ex::fold`).
    fn nth(&mut self, itp: Place, ty: Ty, n: Local, dest: Place) -> R {
        let saved = std::mem::replace(&mut self.fold, false);
        let r = self.nth_in(itp, ty, n, dest);
        self.fold = saved;
        r
    }

    fn nth_in(&mut self, itp: Place, ty: Ty, n: Local, dest: Place) -> R {
        use crate::ast::BinOp::*;
        use IterKind as K;
        if self.is_char_range(ty) {
            return self.char_range_nth(itp, ty, n, dest, false);
        }
        let item = self.item(ty)?;
        let opt = self.body.tys.mk_option(item);
        let Some((k, a)) = self.kind_args(ty) else {
            return self.nth_via_advance(itp, ty, n, dest, false);
        };
        let join = self.block();
        let f = |i: u32| itp.project(Proj::Field(i));
        match k {
            K::RangeFrom => {
                self.range_from_nth(itp, a[0], n, dest)?;
                self.goto(join);
            }
            K::Range => {
                // `spec_nth`: `start + n` checked, else `start = end`.
                let (w, _) = self.wide_ty(a[0])?;
                let ws = self.cast_local(Operand::Copy(f(0)), w);
                let we = self.cast_local(Operand::Copy(f(1)), w);
                let fail = self.block();
                let c = self.cmp(Lt, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (go, no) = self.branch(c);
                self.cur = no;
                self.goto(fail);
                self.cur = go;
                let steps = self.wide_bin(true, we, ws, w);
                let wn = self.cast_local(Operand::Copy(Place::local(n)), w);
                let c2 = self.cmp(Lt, Operand::Copy(Place::local(wn)), Operand::Copy(Place::local(steps)));
                let (hit, miss) = self.branch(c2);
                self.cur = miss;
                self.goto(fail);
                self.cur = hit;
                let plus = self.wide_bin(false, ws, wn, w);
                let v = self.cast_local(Operand::Copy(Place::local(plus)), a[0]);
                let one_w = self.cast_local(Self::usize_c(1), w);
                let ns_w = self.wide_bin(false, plus, one_w, w);
                let ns = self.cast_local(Operand::Copy(Place::local(ns_w)), a[0]);
                self.assign(f(0), Rvalue::Use(Operand::Copy(Place::local(ns))));
                self.some(&dest, opt, Operand::Copy(Place::local(v)));
                self.goto(join);
                self.cur = fail;
                self.assign(f(0), Rvalue::Use(Operand::Copy(f(1))));
                self.none(&dest, opt);
                self.goto(join);
            }
            K::RangeInclusive => {
                // Rust's overflowing form: the state advances by
                // `n + 1` wrapping steps whether or not an item comes
                // out; the result needs `start + n <= end` exactly.
                let (w, it) = self.wide_ty(a[0])?;
                let none_b = self.block();
                let (ex, live) = self.branch(Operand::Copy(f(2)));
                self.cur = ex;
                self.goto(none_b);
                self.cur = live;
                let c = self.cmp(Le, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (go, empty) = self.branch(c);
                self.cur = empty;
                self.goto(none_b);
                self.cur = go;
                let ws = self.cast_local(Operand::Copy(f(0)), w);
                let we = self.cast_local(Operand::Copy(f(1)), w);
                let steps = self.wide_bin(true, we, ws, w);
                let wn = self.cast_local(Operand::Copy(Place::local(n)), w);
                let plus = self.wide_bin(false, ws, wn, w);
                let one_w = self.cast_local(Self::usize_c(1), w);
                let ns_w = self.wide_bin(false, plus, one_w, w);
                let ns = self.cast_local(Operand::Copy(Place::local(ns_w)), a[0]);
                let maxw = self.wide_bound(it, w, true);
                let to_max = self.wide_bin(true, maxw, ws, w);
                // The new start, both paths; exhausted is set on the
                // hit path when `plus` is MAX, on the miss path when
                // the step overflowed or `plus` is MAX.
                let le = self.cmp(Le, Operand::Copy(Place::local(wn)), Operand::Copy(Place::local(steps)));
                let (hit, miss) = self.branch(le);
                self.cur = hit;
                self.assign(f(0), Rvalue::Use(Operand::Copy(Place::local(ns))));
                let ismax = self.cmp(Eq, Operand::Copy(Place::local(plus)), Operand::Copy(Place::local(maxw)));
                let (atmax, below) = self.branch(ismax);
                let ret = self.block();
                self.cur = atmax;
                self.assign(f(2), Rvalue::Use(Operand::Const(Const::Bool(true))));
                self.goto(ret);
                self.cur = below;
                self.goto(ret);
                self.cur = ret;
                let v = self.cast_local(Operand::Copy(Place::local(plus)), a[0]);
                self.some(&dest, opt, Operand::Copy(Place::local(v)));
                self.goto(join);
                self.cur = miss;
                self.assign(f(0), Rvalue::Use(Operand::Copy(Place::local(ns))));
                let on = self.cmp(Gt, Operand::Copy(Place::local(wn)), Operand::Copy(Place::local(to_max)));
                let ismax = self.cmp(Eq, Operand::Copy(Place::local(plus)), Operand::Copy(Place::local(maxw)));
                let set_ex = self.block();
                let (onb, offb) = self.branch(on);
                self.cur = onb;
                self.goto(set_ex);
                self.cur = offb;
                let (maxb, plain) = self.branch(ismax);
                self.cur = maxb;
                self.goto(set_ex);
                self.cur = plain;
                self.goto(none_b);
                self.cur = set_ex;
                self.assign(f(2), Rvalue::Use(Operand::Const(Const::Bool(true))));
                self.goto(none_b);
                self.cur = none_b;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Skip => {
                // One inner `nth` site for every path, so the code grows
                // linearly with nested `Skip`s (fx-cgen-ice): `arg` is its
                // argument, and `pre` marks the overflow form's first pull
                // (`nth(skip - 1)`, dropped, must hit), after which the
                // site runs again with `n`.
                let arg = self.copy_local(Operand::Copy(Place::local(n)), USIZE);
                let pre = self.local(BOOL);
                self.assign(Place::local(pre), Rvalue::Use(Operand::Const(Const::Bool(false))));
                let site = self.block();
                let c = self.cmp(Gt, Operand::Copy(f(1)), Self::usize_c(0));
                let (skip_b, plain) = self.branch(c);
                self.cur = plain;
                self.goto(site);
                self.cur = skip_b;
                let skip = self.copy_local(Operand::Copy(f(1)), USIZE);
                self.assign(f(1), Rvalue::Use(Self::usize_c(0)));
                let ou = self.body.tys.mk_option(USIZE);
                let sum = self.local(ou);
                self.call_builtin(Builtin::CheckedAdd, vec![Operand::Copy(Place::local(skip)), Operand::Copy(Place::local(n))], Place::local(sum));
                let (fits, over) = self.switch_opt(&Place::local(sum));
                self.cur = fits;
                self.assign(Place::local(arg), Rvalue::Use(Operand::Copy(Self::payload(&Place::local(sum)))));
                self.goto(site);
                self.cur = over;
                self.assign(Place::local(arg), Rvalue::Bin(Sub, Operand::Copy(Place::local(skip)), Self::usize_c(1)));
                self.assign(Place::local(pre), Rvalue::Use(Operand::Const(Const::Bool(true))));
                self.goto(site);
                self.cur = site;
                let t = self.local(opt);
                self.nth(f(0), a[0], arg, Place::local(t))?;
                let (first, last) = self.branch(Operand::Copy(Place::local(pre)));
                self.cur = last;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(t))));
                self.goto(join);
                self.cur = first;
                let (s, no) = self.switch_opt(&Place::local(t));
                self.cur = no;
                self.none(&dest, opt);
                self.goto(join);
                self.cur = s;
                self.drop_local(t);
                self.assign(Place::local(pre), Rvalue::Use(Operand::Const(Const::Bool(false))));
                self.assign(Place::local(arg), Rvalue::Use(Operand::Copy(Place::local(n))));
                self.goto(site);
            }
            K::Take => {
                // One inner `nth` site for both paths (linear code in
                // nested `Take`s, fx-cgen-ice): at `arg`, and `drain`
                // marks the spent form, whose item drops.
                let arg = self.copy_local(Operand::Copy(Place::local(n)), USIZE);
                let drain_f = self.local(BOOL);
                self.assign(Place::local(drain_f), Rvalue::Use(Operand::Const(Const::Bool(false))));
                let site = self.block();
                let c = self.cmp(Gt, Operand::Copy(f(1)), Operand::Copy(Place::local(n)));
                let (go, stop) = self.branch(c);
                self.cur = go;
                let n1 = self.local(USIZE);
                self.assign(Place::local(n1), Rvalue::Bin(Add, Operand::Copy(Place::local(n)), Self::usize_c(1)));
                self.assign(f(1), Rvalue::Bin(Sub, Operand::Copy(f(1)), Operand::Copy(Place::local(n1))));
                self.goto(site);
                self.cur = stop;
                let c2 = self.cmp(Gt, Operand::Copy(f(1)), Self::usize_c(0));
                let (drain, done) = self.branch(c2);
                self.cur = drain;
                self.assign(Place::local(arg), Rvalue::Bin(Sub, Operand::Copy(f(1)), Self::usize_c(1)));
                self.assign(Place::local(drain_f), Rvalue::Use(Operand::Const(Const::Bool(true))));
                self.goto(site);
                self.cur = site;
                let t = self.local(opt);
                self.nth(f(0), a[0], arg, Place::local(t))?;
                let (spent, hit) = self.branch(Operand::Copy(Place::local(drain_f)));
                self.cur = hit;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(t))));
                self.goto(join);
                self.cur = spent;
                self.drop_local(t);
                self.assign(f(1), Rvalue::Use(Self::usize_c(0)));
                self.goto(done);
                self.cur = done;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Enumerate => {
                let ii = self.item(a[0])?;
                let iopt = self.body.tys.mk_option(ii);
                let t = self.local(iopt);
                self.nth(f(0), a[0], n, Place::local(t))?;
                let (s, no) = self.switch_opt(&Place::local(t));
                self.cur = no;
                self.none(&dest, opt);
                self.goto(join);
                self.cur = s;
                let i = self.local(USIZE);
                self.assign(Place::local(i), Rvalue::Bin(Add, Operand::Copy(f(1)), Operand::Copy(Place::local(n))));
                self.assign(f(1), Rvalue::Bin(Add, Operand::Copy(Place::local(i)), Self::usize_c(1)));
                let px = self.take(Self::payload(&Place::local(t)), ii);
                let tup = self.local(item);
                self.assign(Place::local(tup), Rvalue::TupleAgg(item, vec![Operand::Copy(Place::local(i)), px]));
                let at = self.take(Place::local(tup), item);
                self.some(&dest, opt, at);
                self.goto(join);
            }
            K::Rev => {
                self.nth_back(f(0), a[0], n, dest)?;
                self.goto(join);
            }
            K::Copied => {
                let ii = self.item(a[0])?;
                let iopt = self.body.tys.mk_option(ii);
                let t = self.local(iopt);
                self.nth(f(0), a[0], n, Place::local(t))?;
                let (s, no) = self.switch_opt(&Place::local(t));
                self.cur = s;
                self.some(&dest, opt, Operand::Copy(Self::payload(&Place::local(t)).deref()));
                self.goto(join);
                self.cur = no;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Peekable => {
                let slot = f(1);
                let pty = self.place_ty(&slot)?;
                // One inner `nth` site for both paths (linear code in
                // nested `Peekable`s, fx-cgen-ice), at `arg`.
                let arg = self.copy_local(Operand::Copy(Place::local(n)), USIZE);
                let held = self.local(opt);
                self.none(&Place::local(held), opt);
                let site = self.block();
                let (full, empty) = self.switch_opt(&slot);
                self.cur = empty;
                self.goto(site);
                self.cur = full;
                let inner = Self::payload(&slot);
                let (some, spent) = self.switch_opt(&inner);
                self.cur = spent;
                self.none(&slot, pty);
                self.none(&dest, opt);
                self.goto(join);
                self.cur = some;
                // The peeked item is taken out now; on the `n > 0`
                // path it drops after the inner `nth`, as in Rust.
                let o = self.local(pty);
                self.take_none(slot.clone(), pty, Place::local(o));
                let v = self.local(item);
                let pv = self.take(Self::payload(&Self::payload(&Place::local(o))), item);
                self.assign(Place::local(v), Rvalue::Use(pv));
                let z = self.cmp(Eq, Operand::Copy(Place::local(n)), Self::usize_c(0));
                let (zero, more) = self.branch(z);
                self.cur = zero;
                let av = self.take(Place::local(v), item);
                self.some(&dest, opt, av);
                self.goto(join);
                self.cur = more;
                self.assign(Place::local(arg), Rvalue::Bin(Sub, Operand::Copy(Place::local(n)), Self::usize_c(1)));
                let hv = self.take(Place::local(v), item);
                self.some(&Place::local(held), opt, hv);
                self.goto(site);
                self.cur = site;
                self.nth(f(0), a[0], arg, dest.clone())?;
                self.drop_local(held);
                self.goto(join);
            }
            K::Chain => {
                let aty = self.place_ty(&f(0))?;
                let n2 = self.local(USIZE);
                let bside = self.block();
                let (asome, anone) = self.switch_opt(&f(0));
                self.cur = anone;
                self.assign(Place::local(n2), Rvalue::Use(Operand::Copy(Place::local(n))));
                self.goto(bside);
                self.cur = asome;
                let rem = self.advance(Self::payload(&f(0)), a[0], n)?;
                let z = self.cmp(Eq, Operand::Copy(Place::local(rem)), Self::usize_c(0));
                let (adv_ok, adv_err) = self.branch(z);
                self.cur = adv_err;
                self.assign(Place::local(n2), Rvalue::Use(Operand::Copy(Place::local(rem))));
                self.none(&f(0), aty);
                self.goto(bside);
                self.cur = adv_ok;
                let t = self.local(opt);
                self.next(Self::payload(&f(0)), a[0], Place::local(t), false)?;
                let (hit, miss) = self.switch_opt(&Place::local(t));
                self.cur = hit;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(t))));
                self.goto(join);
                self.cur = miss;
                self.assign(Place::local(n2), Rvalue::Use(Self::usize_c(0)));
                self.none(&f(0), aty);
                self.goto(bside);
                self.cur = bside;
                let (bs, bn) = self.switch_opt(&f(1));
                self.cur = bn;
                self.none(&dest, opt);
                self.goto(join);
                self.cur = bs;
                self.nth(Self::payload(&f(1)), a[1], n2, dest.clone())?;
                self.goto(join);
            }
            K::StepBy if !self.stepby_range_spec(a[0]) => {
                // The general `spec_nth`: the first item, then one
                // inner `nth((n + 1) * step - 1)`, chunked on overflow.
                // An inner unsigned range takes Rust's other spec,
                // whose `nth` is the default loop (the `_` arm).
                //
                // Every inner pull goes through one `nth` site at `arg`,
                // so the code grows linearly with nested `StepBy`s
                // (fx-cgen-ice). `phase` says which pull it is:
                // 0 the first take (Rust's `self.iter.next()?`; the inner
                // `nth(0)` makes the same pulls as its `next` for every
                // iterator lust accepts: core's adapters reduce `nth(0)`
                // to `next` level by level, and a user iterator that
                // overrides `nth` is rejected, L0640), 1 the `n ==
                // usize::MAX` pre-pull, 2 the last pull (its item is the
                // result), 3 an overflow chunk. A pull other than the last
                // that ends returns None, as Rust's `?` does.
                let m = self.copy_local(Operand::Copy(Place::local(n)), USIZE);
                let step = self.local(USIZE);
                self.assign(Place::local(step), Rvalue::Bin(Add, Operand::Copy(f(1)), Self::usize_c(1)));
                let arg = self.local(USIZE);
                let phase = self.local(int(IntTy::U32));
                let site = self.block();
                let body = self.block();
                let after_max = self.block();
                let lp = self.block();
                let (first, later) = self.branch(Operand::Copy(f(2)));
                self.cur = later;
                self.goto(body);
                self.cur = first;
                self.assign(f(2), Rvalue::Use(Operand::Const(Const::Bool(false))));
                self.assign(Place::local(arg), Rvalue::Use(Self::usize_c(0)));
                self.assign(Place::local(phase), Rvalue::Use(Self::u32_c(0)));
                self.goto(site);
                self.cur = body;
                let mx = self.cmp(Eq, Operand::Copy(Place::local(m)), Self::usize_c(u64::MAX));
                let (is_max, not_max) = self.branch(mx);
                self.cur = not_max;
                self.assign(Place::local(m), Rvalue::Bin(Add, Operand::Copy(Place::local(m)), Self::usize_c(1)));
                self.goto(after_max);
                self.cur = is_max;
                self.assign(Place::local(arg), Rvalue::Use(Operand::Copy(f(1))));
                self.assign(Place::local(phase), Rvalue::Use(Self::u32_c(1)));
                self.goto(site);
                self.cur = after_max;
                self.goto(lp);
                self.cur = lp;
                let ou = self.body.tys.mk_option(USIZE);
                let mul = self.local(ou);
                self.call_builtin(Builtin::CheckedMul, vec![Operand::Copy(Place::local(m)), Operand::Copy(Place::local(step))], Place::local(mul));
                let (fits, over) = self.switch_opt(&Place::local(mul));
                self.cur = fits;
                self.assign(Place::local(arg), Rvalue::Bin(Sub, Operand::Copy(Self::payload(&Place::local(mul))), Self::usize_c(1)));
                self.assign(Place::local(phase), Rvalue::Use(Self::u32_c(2)));
                self.goto(site);
                self.cur = over;
                let (div_n, div_step) = (self.local(USIZE), self.local(USIZE));
                self.assign(Place::local(div_n), Rvalue::Bin(Div, Self::usize_c(u64::MAX), Operand::Copy(Place::local(m))));
                self.assign(Place::local(div_step), Rvalue::Bin(Div, Self::usize_c(u64::MAX), Operand::Copy(Place::local(step))));
                let (nth_n, nth_step) = (self.local(USIZE), self.local(USIZE));
                self.assign(Place::local(nth_n), Rvalue::Bin(Mul, Operand::Copy(Place::local(div_n)), Operand::Copy(Place::local(m))));
                self.assign(Place::local(nth_step), Rvalue::Bin(Mul, Operand::Copy(Place::local(div_step)), Operand::Copy(Place::local(step))));
                let chunk = self.local(USIZE);
                let pick = self.cmp(Gt, Operand::Copy(Place::local(nth_n)), Operand::Copy(Place::local(nth_step)));
                let (use_n, use_step) = self.branch(pick);
                let go = self.block();
                self.cur = use_n;
                self.assign(Place::local(step), Rvalue::Bin(Sub, Operand::Copy(Place::local(step)), Operand::Copy(Place::local(div_n))));
                self.assign(Place::local(chunk), Rvalue::Use(Operand::Copy(Place::local(nth_n))));
                self.goto(go);
                self.cur = use_step;
                self.assign(Place::local(m), Rvalue::Bin(Sub, Operand::Copy(Place::local(m)), Operand::Copy(Place::local(div_step))));
                self.assign(Place::local(chunk), Rvalue::Use(Operand::Copy(Place::local(nth_step))));
                self.goto(go);
                self.cur = go;
                self.assign(Place::local(arg), Rvalue::Bin(Sub, Operand::Copy(Place::local(chunk)), Self::usize_c(1)));
                self.assign(Place::local(phase), Rvalue::Use(Self::u32_c(3)));
                self.goto(site);
                // The one site, then each phase's way on.
                self.cur = site;
                let t = self.local(opt);
                self.nth(f(0), a[0], arg, Place::local(t))?;
                let (p_first, p_max, p_last, p_chunk) = (self.block(), self.block(), self.block(), self.block());
                self.term(Terminator::Switch(Operand::Copy(Place::local(phase)), vec![(0, p_first), (1, p_max), (2, p_last)], p_chunk));
                self.cur = p_last;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(t))));
                self.goto(join);
                for (b, ok) in [(p_first, None), (p_max, Some(after_max)), (p_chunk, Some(lp))] {
                    self.cur = b;
                    let (s2, no2) = self.switch_opt(&Place::local(t));
                    self.cur = no2;
                    self.none(&dest, opt);
                    self.goto(join);
                    self.cur = s2;
                    match ok {
                        Some(next_b) => {
                            self.drop_local(t);
                            self.goto(next_b);
                        }
                        None => {
                            let z = self.cmp(Eq, Operand::Copy(Place::local(m)), Self::usize_c(0));
                            let (zero, more) = self.branch(z);
                            self.cur = zero;
                            self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(t))));
                            self.goto(join);
                            self.cur = more;
                            self.drop_local(t);
                            self.assign(Place::local(m), Rvalue::Bin(Sub, Operand::Copy(Place::local(m)), Self::usize_c(1)));
                            self.goto(body);
                        }
                    }
                }
            }
            _ => {
                self.nth_via_advance(itp, ty, n, dest, false)?;
                self.goto(join);
            }
        }
        self.cur = join;
        Ok(())
    }

    /// True when Rust 1.99 specializes `StepBy` over this inner type
    /// (an unsigned `Range` up to `usize` wide): its `nth` then pulls
    /// item by item instead of delegating.
    fn stepby_range_spec(&self, ty: Ty) -> bool {
        use IterKind as K;
        let Some((K::Range, a)) = self.kind_args(ty) else { return false };
        matches!(self.body.tys.kind(a[0]), TyKind::Int(IntTy::U8 | IntTy::U16 | IntTy::U32 | IntTy::U64 | IntTy::Usize))
    }

    /// `dest = itp.nth_back(n)`: the back form of `nth`, used by
    /// `Rev::nth`. Only the kinds check marks double-ended reach
    /// here; of those, Rust delegates for `Rev` and `Chain` and the
    /// ranges are O(1). The rest take the default via `advance_back`.
    fn nth_back(&mut self, itp: Place, ty: Ty, n: Local, dest: Place) -> R {
        use crate::ast::BinOp::*;
        use IterKind as K;
        if self.is_char_range(ty) {
            return self.char_range_nth(itp, ty, n, dest, true);
        }
        let item = self.item(ty)?;
        let opt = self.body.tys.mk_option(item);
        let Some((k, a)) = self.kind_args(ty) else {
            return self.nth_via_advance(itp, ty, n, dest, true);
        };
        let join = self.block();
        let f = |i: u32| itp.project(Proj::Field(i));
        match k {
            K::Range => {
                // `spec_nth_back`: `end - n` checked against `start`,
                // else `end = start`.
                let (w, _) = self.wide_ty(a[0])?;
                let ws = self.cast_local(Operand::Copy(f(0)), w);
                let we = self.cast_local(Operand::Copy(f(1)), w);
                let fail = self.block();
                let c = self.cmp(Lt, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (go, no) = self.branch(c);
                self.cur = no;
                self.goto(fail);
                self.cur = go;
                let steps = self.wide_bin(true, we, ws, w);
                let wn = self.cast_local(Operand::Copy(Place::local(n)), w);
                let c2 = self.cmp(Lt, Operand::Copy(Place::local(wn)), Operand::Copy(Place::local(steps)));
                let (hit, miss) = self.branch(c2);
                self.cur = miss;
                self.goto(fail);
                self.cur = hit;
                let minus = self.wide_bin(true, we, wn, w);
                let one_w = self.cast_local(Self::usize_c(1), w);
                let ne_w = self.wide_bin(true, minus, one_w, w);
                let v = self.cast_local(Operand::Copy(Place::local(ne_w)), a[0]);
                self.assign(f(1), Rvalue::Use(Operand::Copy(Place::local(v))));
                self.some(&dest, opt, Operand::Copy(Place::local(v)));
                self.goto(join);
                self.cur = fail;
                self.assign(f(1), Rvalue::Use(Operand::Copy(f(0))));
                self.none(&dest, opt);
                self.goto(join);
            }
            K::RangeInclusive => {
                // The back form of the inclusive `nth` above.
                let (w, it) = self.wide_ty(a[0])?;
                let none_b = self.block();
                let (ex, live) = self.branch(Operand::Copy(f(2)));
                self.cur = ex;
                self.goto(none_b);
                self.cur = live;
                let c = self.cmp(Le, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (go, empty) = self.branch(c);
                self.cur = empty;
                self.goto(none_b);
                self.cur = go;
                let ws = self.cast_local(Operand::Copy(f(0)), w);
                let we = self.cast_local(Operand::Copy(f(1)), w);
                let steps = self.wide_bin(true, we, ws, w);
                let wn = self.cast_local(Operand::Copy(Place::local(n)), w);
                let minus = self.wide_bin(true, we, wn, w);
                let one_w = self.cast_local(Self::usize_c(1), w);
                let ne_w = self.wide_bin(true, minus, one_w, w);
                let ne = self.cast_local(Operand::Copy(Place::local(ne_w)), a[0]);
                let minw = self.wide_bound(it, w, false);
                let from_min = self.wide_bin(true, we, minw, w);
                let le = self.cmp(Le, Operand::Copy(Place::local(wn)), Operand::Copy(Place::local(steps)));
                let (hit, miss) = self.branch(le);
                self.cur = hit;
                self.assign(f(1), Rvalue::Use(Operand::Copy(Place::local(ne))));
                let ismin = self.cmp(Eq, Operand::Copy(Place::local(minus)), Operand::Copy(Place::local(minw)));
                let (atmin, above) = self.branch(ismin);
                let ret = self.block();
                self.cur = atmin;
                self.assign(f(2), Rvalue::Use(Operand::Const(Const::Bool(true))));
                self.goto(ret);
                self.cur = above;
                self.goto(ret);
                self.cur = ret;
                let v = self.cast_local(Operand::Copy(Place::local(minus)), a[0]);
                self.some(&dest, opt, Operand::Copy(Place::local(v)));
                self.goto(join);
                self.cur = miss;
                self.assign(f(1), Rvalue::Use(Operand::Copy(Place::local(ne))));
                let on = self.cmp(Gt, Operand::Copy(Place::local(wn)), Operand::Copy(Place::local(from_min)));
                let ismin = self.cmp(Eq, Operand::Copy(Place::local(minus)), Operand::Copy(Place::local(minw)));
                let set_ex = self.block();
                let (onb, offb) = self.branch(on);
                self.cur = onb;
                self.goto(set_ex);
                self.cur = offb;
                let (minb, plain) = self.branch(ismin);
                self.cur = minb;
                self.goto(set_ex);
                self.cur = plain;
                self.goto(none_b);
                self.cur = set_ex;
                self.assign(f(2), Rvalue::Use(Operand::Const(Const::Bool(true))));
                self.goto(none_b);
                self.cur = none_b;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Rev => {
                self.nth(f(0), a[0], n, dest)?;
                self.goto(join);
            }
            K::Copied => {
                let ii = self.item(a[0])?;
                let iopt = self.body.tys.mk_option(ii);
                let t = self.local(iopt);
                self.nth_back(f(0), a[0], n, Place::local(t))?;
                let (s, no) = self.switch_opt(&Place::local(t));
                self.cur = s;
                self.some(&dest, opt, Operand::Copy(Self::payload(&Place::local(t)).deref()));
                self.goto(join);
                self.cur = no;
                self.none(&dest, opt);
                self.goto(join);
            }
            K::Chain => {
                let bty = self.place_ty(&f(1))?;
                let n2 = self.local(USIZE);
                let aside = self.block();
                let (bsome, bnone) = self.switch_opt(&f(1));
                self.cur = bnone;
                self.assign(Place::local(n2), Rvalue::Use(Operand::Copy(Place::local(n))));
                self.goto(aside);
                self.cur = bsome;
                let rem = self.advance_back(Self::payload(&f(1)), a[1], n)?;
                let z = self.cmp(Eq, Operand::Copy(Place::local(rem)), Self::usize_c(0));
                let (adv_ok, adv_err) = self.branch(z);
                self.cur = adv_err;
                self.assign(Place::local(n2), Rvalue::Use(Operand::Copy(Place::local(rem))));
                self.none(&f(1), bty);
                self.goto(aside);
                self.cur = adv_ok;
                let t = self.local(opt);
                self.next(Self::payload(&f(1)), a[1], Place::local(t), true)?;
                let (hit, miss) = self.switch_opt(&Place::local(t));
                self.cur = hit;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(t))));
                self.goto(join);
                self.cur = miss;
                self.assign(Place::local(n2), Rvalue::Use(Self::usize_c(0)));
                self.none(&f(1), bty);
                self.goto(aside);
                self.cur = aside;
                let (asome, anone) = self.switch_opt(&f(0));
                self.cur = anone;
                self.none(&dest, opt);
                self.goto(join);
                self.cur = asome;
                self.nth_back(Self::payload(&f(0)), a[0], n2, dest.clone())?;
                self.goto(join);
            }
            _ => {
                self.nth_via_advance(itp, ty, n, dest, true)?;
                self.goto(join);
            }
        }
        self.cur = join;
        Ok(())
    }

    /// The pull-and-drop loop behind the default `advance_by` (the
    /// back form when `back`): the remainder local is 0 when all `n`
    /// items were pulled, else how many are missing.
    fn advance_loop(&mut self, itp: Place, ty: Ty, n: Local, back: bool) -> Result<Local, String> {
        use crate::ast::BinOp::*;
        let item = self.item(ty)?;
        let opt = self.body.tys.mk_option(item);
        let rem = self.local(USIZE);
        let i = self.local(USIZE);
        self.assign(Place::local(i), Rvalue::Use(Self::usize_c(0)));
        let join = self.block();
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        let c = self.cmp(Lt, Operand::Copy(Place::local(i)), Operand::Copy(Place::local(n)));
        let (pull, done) = self.branch(c);
        self.cur = done;
        self.assign(Place::local(rem), Rvalue::Use(Self::usize_c(0)));
        self.goto(join);
        self.cur = pull;
        let t = self.local(opt);
        // core's default `advance_by` is a `try_fold` (see `Ex::fold`).
        let saved = std::mem::replace(&mut self.fold, true);
        let pulled = self.next(itp.clone(), ty, Place::local(t), back);
        self.fold = saved;
        pulled?;
        let (s, none) = self.switch_opt(&Place::local(t));
        self.cur = none;
        self.assign(Place::local(rem), Rvalue::Bin(Sub, Operand::Copy(Place::local(n)), Operand::Copy(Place::local(i))));
        self.goto(join);
        self.cur = s;
        self.drop_local(t);
        self.assign(Place::local(i), Rvalue::Bin(Add, Operand::Copy(Place::local(i)), Self::usize_c(1)));
        self.goto(lp);
        self.cur = join;
        Ok(rem)
    }

    /// `itp.advance_by(n)` as the remainder local (0 when fully
    /// advanced), with Rust 1.99's per-kind overrides. The O(1) form
    /// is `Range` only: `RangeInclusive` advances item by item in
    /// Rust, like the default loop used for the other kinds.
    fn advance(&mut self, itp: Place, ty: Ty, n: Local) -> Result<Local, String> {
        use crate::ast::BinOp::*;
        use IterKind as K;
        if self.is_char_range(ty) {
            return self.char_range_advance(itp, ty, n, false);
        }
        let Some((k, a)) = self.kind_args(ty) else {
            return self.advance_loop(itp, ty, n, false);
        };
        let f = |i: u32| itp.project(Proj::Field(i));
        match k {
            K::Range => {
                let (w, _) = self.wide_ty(a[0])?;
                let rem = self.local(USIZE);
                let join = self.block();
                let c = self.cmp(Lt, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (go, no) = self.branch(c);
                self.cur = no;
                self.assign(Place::local(rem), Rvalue::Use(Operand::Copy(Place::local(n))));
                self.goto(join);
                self.cur = go;
                let ws = self.cast_local(Operand::Copy(f(0)), w);
                let we = self.cast_local(Operand::Copy(f(1)), w);
                let steps = self.wide_bin(true, we, ws, w);
                let wn = self.cast_local(Operand::Copy(Place::local(n)), w);
                let taken_w = self.local(w);
                let lt = self.cmp(Lt, Operand::Copy(Place::local(steps)), Operand::Copy(Place::local(wn)));
                let (fewer, enough) = self.branch(lt);
                let mid = self.block();
                self.cur = fewer;
                self.assign(Place::local(taken_w), Rvalue::Use(Operand::Copy(Place::local(steps))));
                self.goto(mid);
                self.cur = enough;
                self.assign(Place::local(taken_w), Rvalue::Use(Operand::Copy(Place::local(wn))));
                self.goto(mid);
                self.cur = mid;
                let ns_w = self.wide_bin(false, ws, taken_w, w);
                let ns = self.cast_local(Operand::Copy(Place::local(ns_w)), a[0]);
                self.assign(f(0), Rvalue::Use(Operand::Copy(Place::local(ns))));
                let taken = self.cast_local(Operand::Copy(Place::local(taken_w)), USIZE);
                self.assign(Place::local(rem), Rvalue::Bin(Sub, Operand::Copy(Place::local(n)), Operand::Copy(Place::local(taken))));
                self.goto(join);
                self.cur = join;
                Ok(rem)
            }
            K::Skip => {
                let skip_inner = self.copy_local(Operand::Copy(f(1)), USIZE);
                let saa = self.local(USIZE);
                self.call_builtin(
                    Builtin::SaturatingAdd,
                    vec![Operand::Copy(Place::local(skip_inner)), Operand::Copy(Place::local(n))],
                    Place::local(saa),
                );
                // One inner `advance` site (linear code in nested `Skip`s,
                // fx-cgen-ice): `again` marks its second run, for the rest
                // a saturated sum left.
                let arg = self.copy_local(Operand::Copy(Place::local(saa)), USIZE);
                let again = self.local(BOOL);
                self.assign(Place::local(again), Rvalue::Use(Operand::Const(Const::Bool(false))));
                let site = self.block();
                self.goto(site);
                self.cur = site;
                let rem = self.advance(f(0), a[0], arg)?;
                let nn = self.local(USIZE);
                let join = self.block();
                let (second, first) = self.branch(Operand::Copy(Place::local(again)));
                self.cur = second;
                self.assign(Place::local(nn), Rvalue::Use(Operand::Copy(Place::local(rem))));
                self.goto(join);
                self.cur = first;
                let rem1 = self.copy_local(Operand::Copy(Place::local(rem)), USIZE);
                let advanced = self.local(USIZE);
                self.assign(Place::local(advanced), Rvalue::Bin(Sub, Operand::Copy(Place::local(saa)), Operand::Copy(Place::local(rem1))));
                let subbed = self.local(USIZE);
                self.call_builtin(
                    Builtin::SaturatingSub,
                    vec![Operand::Copy(Place::local(advanced)), Operand::Copy(Place::local(skip_inner))],
                    Place::local(subbed),
                );
                self.assign(Place::local(nn), Rvalue::Bin(Sub, Operand::Copy(Place::local(n)), Operand::Copy(Place::local(subbed))));
                let newn = self.local(USIZE);
                self.call_builtin(
                    Builtin::SaturatingSub,
                    vec![Operand::Copy(f(1)), Operand::Copy(Place::local(advanced))],
                    Place::local(newn),
                );
                self.assign(f(1), Rvalue::Use(Operand::Copy(Place::local(newn))));
                // The saturated sum may leave a rest to advance.
                let z = self.cmp(Eq, Operand::Copy(Place::local(rem1)), Self::usize_c(0));
                let (full, short) = self.branch(z);
                self.cur = short;
                self.goto(join);
                self.cur = full;
                let pos = self.cmp(Gt, Operand::Copy(Place::local(nn)), Self::usize_c(0));
                let (rest, done) = self.branch(pos);
                self.cur = done;
                self.goto(join);
                self.cur = rest;
                self.assign(Place::local(arg), Rvalue::Use(Operand::Copy(Place::local(nn))));
                self.assign(Place::local(again), Rvalue::Use(Operand::Const(Const::Bool(true))));
                self.goto(site);
                self.cur = join;
                Ok(nn)
            }
            K::Take => {
                let minl = self.local(USIZE);
                self.call_builtin(Builtin::Min, vec![Operand::Copy(f(1)), Operand::Copy(Place::local(n))], Place::local(minl));
                let rem = self.advance(f(0), a[0], minl)?;
                let advanced = self.local(USIZE);
                self.assign(Place::local(advanced), Rvalue::Bin(Sub, Operand::Copy(Place::local(minl)), Operand::Copy(Place::local(rem))));
                self.assign(f(1), Rvalue::Bin(Sub, Operand::Copy(f(1)), Operand::Copy(Place::local(advanced))));
                let out = self.local(USIZE);
                self.assign(Place::local(out), Rvalue::Bin(Sub, Operand::Copy(Place::local(n)), Operand::Copy(Place::local(advanced))));
                Ok(out)
            }
            K::Enumerate => {
                let rem = self.advance(f(0), a[0], n)?;
                let advanced = self.local(USIZE);
                self.assign(Place::local(advanced), Rvalue::Bin(Sub, Operand::Copy(Place::local(n)), Operand::Copy(Place::local(rem))));
                self.assign(f(1), Rvalue::Bin(Add, Operand::Copy(f(1)), Operand::Copy(Place::local(advanced))));
                Ok(rem)
            }
            K::Rev => self.advance_back(f(0), a[0], n),
            K::Copied => self.advance(f(0), a[0], n),
            K::RepeatN => self.repeat_n_advance(itp, a[0], n),
            K::Chain => {
                let aty = self.place_ty(&f(0))?;
                let out = self.local(USIZE);
                let n2 = self.local(USIZE);
                let join = self.block();
                let bside = self.block();
                let (asome, anone) = self.switch_opt(&f(0));
                self.cur = anone;
                self.assign(Place::local(n2), Rvalue::Use(Operand::Copy(Place::local(n))));
                self.goto(bside);
                self.cur = asome;
                let rem = self.advance(Self::payload(&f(0)), a[0], n)?;
                let z = self.cmp(Eq, Operand::Copy(Place::local(rem)), Self::usize_c(0));
                let (full, short) = self.branch(z);
                self.cur = full;
                self.assign(Place::local(out), Rvalue::Use(Self::usize_c(0)));
                self.goto(join);
                self.cur = short;
                self.assign(Place::local(n2), Rvalue::Use(Operand::Copy(Place::local(rem))));
                self.none(&f(0), aty);
                self.goto(bside);
                self.cur = bside;
                let (bs, bn) = self.switch_opt(&f(1));
                self.cur = bn;
                self.assign(Place::local(out), Rvalue::Use(Operand::Copy(Place::local(n2))));
                self.goto(join);
                self.cur = bs;
                let rb = self.advance(Self::payload(&f(1)), a[1], n2)?;
                self.assign(Place::local(out), Rvalue::Use(Operand::Copy(Place::local(rb))));
                self.goto(join);
                self.cur = join;
                Ok(out)
            }
            _ => self.advance_loop(itp, ty, n, false),
        }
    }

    /// `dst.clone_from_slice(src)` for a Copy `T` with a written Clone,
    /// as core's non-`TrivialClone` form: the length assert, then
    /// `dst[i].clone_from(&src[i])` in order through `f`, the impl's
    /// `clone_from` (two params), or `dst[i] = src[i].clone()` when the
    /// impl has only `clone` (core's default `clone_from`).
    fn clone_from_written(&mut self, d: Operand, s: Operand, f: Operand, dest: Place) -> R {
        use crate::ast::BinOp::*;
        let slice_of = |this: &mut Self, o: Operand, m: bool| -> Result<(Local, Ty), String> {
            let ot = this.op_ty(&o)?;
            let el = match this.body.tys.kind(ot) {
                TyKind::Ref(_, _, inner) => match this.body.tys.kind(inner) {
                    TyKind::Slice(e) | TyKind::Array(e, _) => e,
                    _ => this.body.tys.vec_elem(inner).ok_or("clone_from_slice expansion: not a slice")?,
                },
                _ => return Err("clone_from_slice expansion: not a reference".into()),
            };
            let op = this.op_place(o, ot);
            let sl = this.body.tys.intern(TyKind::Slice(el));
            let r = this.body.tys.mk_ref(m, sl);
            let l = this.local(r);
            this.assign(Place::local(l), Rvalue::SliceOf(op.deref()));
            Ok((l, el))
        };
        let (dl, el) = slice_of(self, d, true)?;
        let (sl, _) = slice_of(self, s, false)?;
        let ft = self.op_ty(&f)?;
        let fl = self.local(ft);
        self.assign(Place::local(fl), Rvalue::Use(f));
        let by_clone_from = match self.body.tys.kind(ft) {
            TyKind::FnPtr(sig) => self.body.tys.tys_of(self.body.tys.sig(sig).value.inputs).len() == 2,
            _ => false,
        };
        let (n, m) = (self.local(USIZE), self.local(USIZE));
        self.assign(Place::local(n), Rvalue::LenOf(Place::local(dl).deref()));
        self.assign(Place::local(m), Rvalue::LenOf(Place::local(sl).deref()));
        let c = self.cmp(Ne, Operand::Copy(Place::local(n)), Operand::Copy(Place::local(m)));
        let (bad, good) = self.branch(c);
        self.cur = bad;
        self.term(Terminator::Panic(vec![FmtPart::Lit("destination and source slices have different lengths".into())]));
        self.cur = good;
        let i = self.local(USIZE);
        self.assign(Place::local(i), Rvalue::Use(Self::usize_c(0)));
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        let c = self.cmp(Lt, Operand::Copy(Place::local(i)), Operand::Copy(Place::local(n)));
        let (body, done) = self.branch(c);
        self.cur = body;
        let sr = self.ref_to(false, Place::local(sl).deref().project(Proj::Index(i)), el);
        if by_clone_from {
            let dr = self.ref_to(true, Place::local(dl).deref().project(Proj::Index(i)), el);
            let u = self.local(UNIT);
            self.call(CallTarget::Indirect(fl), vec![Operand::Move(Place::local(dr)), Operand::Move(Place::local(sr))], Place::local(u));
        } else {
            let v = self.local(el);
            self.call(CallTarget::Indirect(fl), vec![Operand::Move(Place::local(sr))], Place::local(v));
            self.assign(Place::local(dl).deref().project(Proj::Index(i)), Rvalue::Use(Operand::Copy(Place::local(v))));
        }
        self.assign(Place::local(i), Rvalue::Bin(Add, Operand::Copy(Place::local(i)), Self::usize_c(1)));
        self.goto(lp);
        self.cur = done;
        self.assign(dest, Rvalue::Use(Operand::Const(Const::Unit)));
        Ok(())
    }

    /// `[S]::join(sep)` (`concat` with no `sep`) over an element with a
    /// written `Borrow<str>` impl, whose `borrow` fn is `f`: alloc's
    /// `join_generic_copy`. The first part is borrowed once; each other
    /// part is borrowed for the length, then again for its copy. The
    /// String has exactly the reserved capacity; a separator or part
    /// that no longer fits (a `borrow` that grew between its two calls)
    /// panics as core's `split_at_mut` does, at the join's
    /// `specialize_for_lengths!` site. A length sum past `usize::MAX`
    /// (core's `expect` panic) needs about `usize::MAX` parts and is
    /// not modeled.
    fn join_borrow(&mut self, r: Operand, sep: Option<Operand>, f: Operand, dest: Place) -> R {
        use crate::ast::BinOp::*;
        let rt = self.op_ty(&r)?;
        let elem = match self.body.tys.kind(rt) {
            TyKind::Ref(_, _, inner) => match self.body.tys.kind(inner) {
                TyKind::Slice(e) | TyKind::Array(e, _) => e,
                _ => self.body.tys.vec_elem(inner).ok_or("join expansion: not a slice receiver")?,
            },
            _ => return Err("join expansion: not a reference receiver".into()),
        };
        let rp = self.op_place(r, rt);
        let sl = self.body.tys.intern(TyKind::Slice(elem));
        let slr = self.body.tys.mk_ref(false, sl);
        let s = self.local(slr);
        self.assign(Place::local(s), Rvalue::SliceOf(rp.deref()));
        let n = self.local(USIZE);
        self.assign(Place::local(n), Rvalue::LenOf(Place::local(s).deref()));
        let ft = self.op_ty(&f)?;
        let fl = self.local(ft);
        self.assign(Place::local(fl), Rvalue::Use(f));
        let sep_len = self.local(USIZE);
        let sep = match sep {
            Some(o) => {
                let l = self.local(REF_STR);
                self.assign(Place::local(l), Rvalue::Use(o));
                self.call_builtin(Builtin::StrLen, vec![Operand::Copy(Place::local(l))], Place::local(sep_len));
                Some(l)
            }
            None => {
                self.assign(Place::local(sep_len), Rvalue::Use(Self::usize_c(0)));
                None
            }
        };
        let str_len = |this: &mut Self, v: Local| -> Local {
            let l = this.local(USIZE);
            this.call_builtin(Builtin::StrLen, vec![Operand::Copy(Place::local(v))], Place::local(l));
            l
        };
        // `borrow(&s[i])`, as a new `&str` local.
        let borrow = |this: &mut Self, i: Local| -> Local {
            let er = this.ref_to(false, Place::local(s).deref().project(Proj::Index(i)), elem);
            let out = this.local(REF_STR);
            this.call(CallTarget::Indirect(fl), vec![Operand::Move(Place::local(er))], Place::local(out));
            out
        };
        // `mid > len` at alloc/src/str.rs:200:22 (`STD_FILES` 34) when `len` bytes do not
        // fit in the `remain` left.
        let fits = |this: &mut Self, len: Operand, remain: Local| {
            let c = this.cmp(Gt, len, Operand::Copy(Place::local(remain)));
            let (bad, good) = this.branch(c);
            this.cur = bad;
            this.term(Terminator::Panic(vec![FmtPart::Lit("mid > len".into())]));
            this.body.blocks[this.cur.0 as usize].term_span = crate::diag::Span::std_site(34, 200, 22);
            this.cur = good;
        };
        let join = self.block();
        let z = self.cmp(Eq, Operand::Copy(Place::local(n)), Self::usize_c(0));
        let (empty, go) = self.branch(z);
        self.cur = empty;
        self.call_builtin(Builtin::StringNew, vec![], dest.clone());
        self.goto(join);
        self.cur = go;
        let zero = self.copy_local(Self::usize_c(0), USIZE);
        let first = borrow(self, zero);
        let first_len = str_len(self, first);
        // reserved = sep_len * (n - 1) + first.len() + the other parts' lengths.
        let res = self.local(USIZE);
        let n1 = self.local(USIZE);
        self.assign(Place::local(n1), Rvalue::Bin(Sub, Operand::Copy(Place::local(n)), Self::usize_c(1)));
        self.assign(Place::local(res), Rvalue::Bin(Mul, Operand::Copy(Place::local(sep_len)), Operand::Copy(Place::local(n1))));
        self.assign(Place::local(res), Rvalue::Bin(Add, Operand::Copy(Place::local(res)), Operand::Copy(Place::local(first_len))));
        let i = self.local(USIZE);
        // Pass 1: the lengths of parts 1..n.
        self.assign(Place::local(i), Rvalue::Use(Self::usize_c(1)));
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        let c = self.cmp(Lt, Operand::Copy(Place::local(i)), Operand::Copy(Place::local(n)));
        let (body, done) = self.branch(c);
        self.cur = body;
        let b = borrow(self, i);
        let bl = str_len(self, b);
        self.assign(Place::local(res), Rvalue::Bin(Add, Operand::Copy(Place::local(res)), Operand::Copy(Place::local(bl))));
        self.assign(Place::local(i), Rvalue::Bin(Add, Operand::Copy(Place::local(i)), Self::usize_c(1)));
        self.goto(lp);
        self.cur = done;
        let out = self.local(STRING);
        self.call_builtin(Builtin::StringWithCapacity, vec![Operand::Copy(Place::local(res))], Place::local(out));
        let push = |this: &mut Self, v: Local| {
            let m = this.ref_to(true, Place::local(out), STRING);
            let u = this.local(UNIT);
            this.call_builtin(Builtin::StringPushStr, vec![Operand::Move(Place::local(m)), Operand::Copy(Place::local(v))], Place::local(u));
        };
        push(self, first);
        let remain = self.local(USIZE);
        self.assign(Place::local(remain), Rvalue::Bin(Sub, Operand::Copy(Place::local(res)), Operand::Copy(Place::local(first_len))));
        // Pass 2: each other part borrowed again, after its separator.
        self.assign(Place::local(i), Rvalue::Use(Self::usize_c(1)));
        let lp2 = self.block();
        self.goto(lp2);
        self.cur = lp2;
        let c = self.cmp(Lt, Operand::Copy(Place::local(i)), Operand::Copy(Place::local(n)));
        let (body, done) = self.branch(c);
        self.cur = body;
        let b = borrow(self, i);
        if let Some(sep) = sep {
            fits(self, Operand::Copy(Place::local(sep_len)), remain);
            push(self, sep);
            self.assign(Place::local(remain), Rvalue::Bin(Sub, Operand::Copy(Place::local(remain)), Operand::Copy(Place::local(sep_len))));
        }
        let bl = str_len(self, b);
        fits(self, Operand::Copy(Place::local(bl)), remain);
        push(self, b);
        self.assign(Place::local(remain), Rvalue::Bin(Sub, Operand::Copy(Place::local(remain)), Operand::Copy(Place::local(bl))));
        self.assign(Place::local(i), Rvalue::Bin(Add, Operand::Copy(Place::local(i)), Self::usize_c(1)));
        self.goto(lp2);
        self.cur = done;
        self.assign(dest, Rvalue::Use(Operand::Move(Place::local(out))));
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// core's `RepeatN::advance_by(n)` (no clones): the count drops by
    /// `n`; when that reaches 0 the element drops (`self.inner = None`)
    /// and the remainder is what was left of `n`.
    fn repeat_n_advance(&mut self, itp: Place, elem: Ty, n: Local) -> Result<Local, String> {
        use crate::ast::BinOp::*;
        let f = |i: u32| itp.project(Proj::Field(i));
        let rem = self.local(USIZE);
        let join = self.block();
        let c = self.cmp(Lt, Operand::Copy(Place::local(n)), Operand::Copy(f(1)));
        let (part, all) = self.branch(c);
        self.cur = part;
        self.assign(f(1), Rvalue::Bin(Sub, Operand::Copy(f(1)), Operand::Copy(Place::local(n))));
        self.assign(Place::local(rem), Rvalue::Use(Self::usize_c(0)));
        self.goto(join);
        self.cur = all;
        self.assign(Place::local(rem), Rvalue::Bin(Sub, Operand::Copy(Place::local(n)), Operand::Copy(f(1))));
        self.assign(f(1), Rvalue::Use(Self::usize_c(0)));
        let ot = self.body.tys.mk_option(elem);
        let t = self.local(ot);
        self.take_none(f(0), ot, Place::local(t));
        self.drop_local(t);
        self.goto(join);
        self.cur = join;
        Ok(rem)
    }

    /// `itp.advance_back_by(n)` as the remainder local: the back
    /// form of `advance`, with the same per-kind overrides.
    fn advance_back(&mut self, itp: Place, ty: Ty, n: Local) -> Result<Local, String> {
        use crate::ast::BinOp::*;
        use IterKind as K;
        if self.is_char_range(ty) {
            return self.char_range_advance(itp, ty, n, true);
        }
        let Some((k, a)) = self.kind_args(ty) else {
            return self.advance_loop(itp, ty, n, true);
        };
        let f = |i: u32| itp.project(Proj::Field(i));
        match k {
            K::Range => {
                let (w, _) = self.wide_ty(a[0])?;
                let rem = self.local(USIZE);
                let join = self.block();
                let c = self.cmp(Lt, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (go, no) = self.branch(c);
                self.cur = no;
                self.assign(Place::local(rem), Rvalue::Use(Operand::Copy(Place::local(n))));
                self.goto(join);
                self.cur = go;
                let ws = self.cast_local(Operand::Copy(f(0)), w);
                let we = self.cast_local(Operand::Copy(f(1)), w);
                let steps = self.wide_bin(true, we, ws, w);
                let wn = self.cast_local(Operand::Copy(Place::local(n)), w);
                let taken_w = self.local(w);
                let lt = self.cmp(Lt, Operand::Copy(Place::local(steps)), Operand::Copy(Place::local(wn)));
                let (fewer, enough) = self.branch(lt);
                let mid = self.block();
                self.cur = fewer;
                self.assign(Place::local(taken_w), Rvalue::Use(Operand::Copy(Place::local(steps))));
                self.goto(mid);
                self.cur = enough;
                self.assign(Place::local(taken_w), Rvalue::Use(Operand::Copy(Place::local(wn))));
                self.goto(mid);
                self.cur = mid;
                let ne_w = self.wide_bin(true, we, taken_w, w);
                let ne = self.cast_local(Operand::Copy(Place::local(ne_w)), a[0]);
                self.assign(f(1), Rvalue::Use(Operand::Copy(Place::local(ne))));
                let taken = self.cast_local(Operand::Copy(Place::local(taken_w)), USIZE);
                self.assign(Place::local(rem), Rvalue::Bin(Sub, Operand::Copy(Place::local(n)), Operand::Copy(Place::local(taken))));
                self.goto(join);
                self.cur = join;
                Ok(rem)
            }
            K::Rev => self.advance(f(0), a[0], n),
            K::Copied => self.advance_back(f(0), a[0], n),
            // core: `advance_back_by` is `advance_by`.
            K::RepeatN => self.repeat_n_advance(itp, a[0], n),
            K::Chain => {
                let bty = self.place_ty(&f(1))?;
                let out = self.local(USIZE);
                let n2 = self.local(USIZE);
                let join = self.block();
                let aside = self.block();
                let (bsome, bnone) = self.switch_opt(&f(1));
                self.cur = bnone;
                self.assign(Place::local(n2), Rvalue::Use(Operand::Copy(Place::local(n))));
                self.goto(aside);
                self.cur = bsome;
                let rem = self.advance_back(Self::payload(&f(1)), a[1], n)?;
                let z = self.cmp(Eq, Operand::Copy(Place::local(rem)), Self::usize_c(0));
                let (full, short) = self.branch(z);
                self.cur = full;
                self.assign(Place::local(out), Rvalue::Use(Self::usize_c(0)));
                self.goto(join);
                self.cur = short;
                self.assign(Place::local(n2), Rvalue::Use(Operand::Copy(Place::local(rem))));
                self.none(&f(1), bty);
                self.goto(aside);
                self.cur = aside;
                let (asome, anone) = self.switch_opt(&f(0));
                self.cur = anone;
                self.assign(Place::local(out), Rvalue::Use(Operand::Copy(Place::local(n2))));
                self.goto(join);
                self.cur = asome;
                let ra = self.advance_back(Self::payload(&f(0)), a[0], n2)?;
                self.assign(Place::local(out), Rvalue::Use(Operand::Copy(Place::local(ra))));
                self.goto(join);
                self.cur = join;
                Ok(out)
            }
            _ => self.advance_loop(itp, ty, n, true),
        }
    }

    // ---------- Random access (TrustedRandomAccess) ----------

    /// True when Rust 1.99 implements `TrustedRandomAccess` for this
    /// type: `Zip` then pulls by index, only as far as the short side.
    fn tra(&self, ty: Ty) -> bool {
        use IterKind as K;
        let Some((k, a)) = self.kind_args(ty) else { return false };
        match k {
            // `array::IntoIter` is random access in Rust 1.99 for `Copy`
            // items (a zip with it pulls only `min` items from a mapped
            // side), in the `NoCoerce` form only.
            K::ArrayIntoIter => is_copy(self.p, &self.body.tys, a[0]),
            K::SliceIter | K::SliceIterMut | K::Windows => true,
            K::Chunks | K::ChunksMut | K::ChunksExact | K::ChunksExactMut => true,
            K::Range => matches!(
                self.body.tys.kind(a[0]),
                TyKind::Int(IntTy::Usize | IntTy::U8 | IntTy::U16 | IntTy::U32 | IntTy::U64 | IntTy::Isize | IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64)
            ),
            K::Map | K::Enumerate | K::Copied | K::Cloned | K::Skip => self.tra(a[0]),
            K::Zip => self.tra(a[0]) && self.tra(a[1]),
            _ => false,
        }
    }

    /// True when Rust 1.99 implements the full `TrustedRandomAccess`
    /// (not only `TrustedRandomAccessNoCoerce`): `Skip` and `StepBy`
    /// are `TrustedLen` only over it. `array::IntoIter` has only the
    /// `NoCoerce` form.
    fn tra_coerce(&self, ty: Ty) -> bool {
        use IterKind as K;
        match self.kind_args(ty) {
            Some((K::ArrayIntoIter, _)) => false,
            Some((K::Map | K::Enumerate | K::Copied | K::Cloned | K::Skip, a)) => self.tra_coerce(a[0]),
            Some((K::Zip, a)) => self.tra_coerce(a[0]) && self.tra_coerce(a[1]),
            _ => self.tra(ty),
        }
    }

    /// The exact remaining length of a random-access iterator.
    fn size(&mut self, itp: Place, ty: Ty) -> Result<Operand, String> {
        use crate::ast::BinOp::*;
        use IterKind as K;
        if self.is_char_range(ty) {
            return self.char_range_size(itp, ty);
        }
        let (k, a) = self.kind_args(ty).ok_or("iterator expansion: size of a non-iterator")?;
        let f = |i: u32| itp.project(Proj::Field(i));
        let out = self.local(USIZE);
        match k {
            K::SliceIter | K::SliceIterMut => self.assign(Place::local(out), Rvalue::LenOf(f(0).deref())),
            K::Range => {
                let c = self.cmp(Lt, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (s, n) = self.branch(c);
                let join = self.block();
                self.cur = s;
                let wide = int(IntTy::I128);
                let (lo, hi) = (self.local(wide), self.local(wide));
                self.assign(Place::local(lo), Rvalue::Cast(Operand::Copy(f(0)), wide));
                self.assign(Place::local(hi), Rvalue::Cast(Operand::Copy(f(1)), wide));
                let d = self.local(wide);
                self.assign(Place::local(d), Rvalue::Bin(Sub, Operand::Copy(Place::local(hi)), Operand::Copy(Place::local(lo))));
                self.assign(Place::local(out), Rvalue::Cast(Operand::Copy(Place::local(d)), USIZE));
                self.goto(join);
                self.cur = n;
                self.assign(Place::local(out), Rvalue::Use(Self::usize_c(0)));
                self.goto(join);
                self.cur = join;
            }
            K::Map | K::Enumerate | K::Copied | K::Cloned => return self.size(f(0), a[0]),
            K::Skip => {
                let inner = self.size(f(0), a[0])?;
                self.call_builtin(Builtin::SaturatingSub, vec![inner, Operand::Copy(f(1))], Place::local(out));
            }
            K::Zip if self.tra_coerce(a[0]) && self.tra_coerce(a[1]) => {
                self.assign(Place::local(out), Rvalue::Bin(Sub, Operand::Copy(f(3)), Operand::Copy(f(2))));
            }
            // The `NoCoerce` form pulls its sides with `next`: the
            // general `size_hint`, exact over random-access sides.
            K::Zip => {
                let x = self.size(f(0), a[0])?;
                let y = self.size(f(1), a[1])?;
                self.call_builtin(Builtin::Min, vec![x, y], Place::local(out));
            }
            K::ArrayIntoIter => {
                self.assign(Place::local(out), Rvalue::Bin(Sub, Operand::Copy(f(2)), Operand::Copy(f(1))));
            }
            K::RepeatN => self.assign(Place::local(out), Rvalue::Use(Operand::Copy(f(1)))),
            // `Windows`: len - size + 1, or 0 when shorter than a window.
            K::Windows => {
                let len = self.local(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(f(0).deref()));
                let c = self.cmp(Lt, Operand::Copy(Place::local(len)), Operand::Copy(f(1)));
                let (short, s) = self.branch(c);
                let join = self.block();
                self.cur = s;
                let d = self.local(USIZE);
                self.assign(Place::local(d), Rvalue::Bin(Sub, Operand::Copy(Place::local(len)), Operand::Copy(f(1))));
                self.assign(Place::local(out), Rvalue::Bin(Add, Operand::Copy(Place::local(d)), Self::usize_c(1)));
                self.goto(join);
                self.cur = short;
                self.assign(Place::local(out), Rvalue::Use(Self::usize_c(0)));
                self.goto(join);
                self.cur = join;
            }
            // `Chunks`: the ceiling of len / size, computed as
            // std's `div_ceil` so a huge `len` cannot overflow.
            K::Chunks | K::ChunksMut => {
                let len = self.local(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(f(0).deref()));
                let c = self.cmp(Eq, Operand::Copy(Place::local(len)), Self::usize_c(0));
                let (empty, s) = self.branch(c);
                let join = self.block();
                self.cur = s;
                let d = self.local(USIZE);
                self.assign(Place::local(d), Rvalue::Bin(Sub, Operand::Copy(Place::local(len)), Self::usize_c(1)));
                let q = self.local(USIZE);
                self.assign(Place::local(q), Rvalue::Bin(Div, Operand::Copy(Place::local(d)), Operand::Copy(f(1))));
                self.assign(Place::local(out), Rvalue::Bin(Add, Operand::Copy(Place::local(q)), Self::usize_c(1)));
                self.goto(join);
                self.cur = empty;
                self.assign(Place::local(out), Rvalue::Use(Self::usize_c(0)));
                self.goto(join);
                self.cur = join;
            }
            K::ChunksExact | K::ChunksExactMut => {
                let len = self.local(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(f(0).deref()));
                self.assign(Place::local(out), Rvalue::Bin(Div, Operand::Copy(Place::local(len)), Operand::Copy(f(2))));
            }
            // The `option` and `result` iterators: 0 or 1.
            K::OptionIntoIter | K::OptionIter | K::OptionIterMut | K::ResultIter | K::ResultIterMut | K::ResultIntoIter => {
                let (s, n) = self.switch_opt(&f(0));
                let join = self.block();
                self.cur = s;
                self.assign(Place::local(out), Rvalue::Use(Self::usize_c(1)));
                self.goto(join);
                self.cur = n;
                self.assign(Place::local(out), Rvalue::Use(Self::usize_c(0)));
                self.goto(join);
                self.cur = join;
            }
            _ => return Err("iterator expansion: size of a non-random-access iterator".into()),
        }
        Ok(Operand::Copy(Place::local(out)))
    }

    /// True when `len()` on `ty` runs std's exact-size assert over a
    /// user `size_hint`: a `ByNext` core under the adapters whose
    /// own `len` delegates to their inner iterator's.
    fn len_asserts(&mut self, ty: Ty) -> bool {
        use IterKind as K;
        match self.kind_args(ty) {
            Some((K::ByNext, a)) => self.by_mut_builtin(a[0]).is_none_or(|inner| self.len_asserts(inner)),
            Some((K::Map | K::Enumerate | K::Rev | K::Copied | K::Cloned | K::Peekable | K::Inspect, a)) => self.len_asserts(a[0]),
            _ => false,
        }
    }

    /// The `assert_eq!(upper, Some(lower))` panic of std's default
    /// `ExactSizeIterator::len` (core's exact_size.rs), with the
    /// hint's upper bound on the left and `Some(lower)` on the right.
    fn exact_len_panic(&mut self, hi: Local, right: Local, ou: Ty) {
        let dbg = crate::ast::FmtSpec { kind: crate::ast::FmtKind::Debug, ..crate::ast::FmtSpec::default() };
        let lref = self.ref_to(false, Place::local(hi), ou);
        let rref = self.ref_to(false, Place::local(right), ou);
        let parts = vec![
            FmtPart::Lit("assertion `left == right` failed".into()),
            FmtPart::Lit("\n  left: ".into()),
            FmtPart::Arg { value: Operand::Copy(Place::local(lref)), ty: ou, debug: true, spec: dbg, width: None, prec: None },
            FmtPart::Lit("\n right: ".into()),
            FmtPart::Arg { value: Operand::Copy(Place::local(rref)), ty: ou, debug: true, spec: dbg, width: None, prec: None },
        ];
        self.term(Terminator::Panic(parts));
        self.body.blocks[self.cur.0 as usize].term_span = Span::std_site(13, 122, 9);
    }

    // ---------- size_hint ----------

    /// `itp.size_hint()` as (lower, upper) locals: `usize` and
    /// `Option<usize>`, with Rust 1.99's arithmetic per kind.
    fn hint(&mut self, itp: Place, ty: Ty) -> Result<(Local, Local), String> {
        use crate::ast::BinOp::*;
        use IterKind as K;
        if self.is_char_range(ty) {
            return self.char_range_hint(itp, ty);
        }
        let ou = self.body.tys.mk_option(USIZE);
        let (lo, hi) = (self.local(USIZE), self.local(ou));
        let set_exact = |this: &mut Self, n: Operand| {
            this.assign(Place::local(lo), Rvalue::Use(n.clone()));
            this.some(&Place::local(hi), ou, n);
        };
        if self.body.tys.is_chars_ty(ty) {
            // ((bytes + 3) / 4, Some(bytes)) over the bytes left.
            let r = self.ref_to(false, itp, ty);
            let bytes = self.local(USIZE);
            self.call_builtin(Builtin::CharsBytesLeft, vec![Operand::Move(Place::local(r))], Place::local(bytes));
            let b3 = self.local(USIZE);
            self.assign(Place::local(b3), Rvalue::Bin(Add, Operand::Copy(Place::local(bytes)), Self::usize_c(3)));
            self.assign(Place::local(lo), Rvalue::Bin(Div, Operand::Copy(Place::local(b3)), Self::usize_c(4)));
            self.some(&Place::local(hi), ou, Operand::Copy(Place::local(bytes)));
            return Ok((lo, hi));
        }
        let (k, a) = self.kind_args(ty).ok_or("iterator expansion: size_hint of a non-iterator")?;
        let f = |i: u32| itp.project(Proj::Field(i));
        match k {
            // std's default `(0, None)`.
            K::RecvIter | K::RecvTryIter | K::RecvIntoIter => {
                self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(0)));
                self.none(&Place::local(hi), ou);
            }
            K::SliceIter | K::SliceIterMut | K::Range | K::Zip if k != K::Zip || (self.tra(a[0]) && self.tra(a[1])) => {
                let n = self.size(itp.clone(), ty)?;
                set_exact(self, n);
            }
            K::VecIntoIter => {
                let r = self.ref_to(false, itp, ty);
                let n = self.local(USIZE);
                self.call_builtin(Builtin::VecIterLen, vec![Operand::Move(Place::local(r))], Place::local(n));
                set_exact(self, Operand::Copy(Place::local(n)));
            }
            K::ArrayIntoIter | K::RepeatN | K::Windows => {
                let n = self.size(itp.clone(), ty)?;
                set_exact(self, n);
            }
            // The slice splits: `(0, Some(0))` once finished, else
            // `(1, Some(len + 1))` (`SplitInclusive`: `max(1, len)`);
            // the N forms cap both bounds at the count left.
            K::SliceSplit | K::SliceSplitMut => {
                use crate::ty::iter::SliceSplitMode as M;
                let mode = it::slice_split_mode(&self.body.tys, a[2]).ok_or("iterator expansion: bad slice split mode")?;
                let up = self.local(USIZE);
                let (done, go) = self.branch(Operand::Copy(f(2)));
                let set = self.block();
                self.cur = done;
                self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(0)));
                self.assign(Place::local(up), Rvalue::Use(Self::usize_c(0)));
                self.goto(set);
                self.cur = go;
                self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(1)));
                let len = self.local(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(f(0).deref()));
                if mode == M::SplitInclusive {
                    self.call_builtin(Builtin::Max, vec![Self::usize_c(1), Operand::Copy(Place::local(len))], Place::local(up));
                } else {
                    self.assign(Place::local(up), Rvalue::Bin(Add, Operand::Copy(Place::local(len)), Self::usize_c(1)));
                }
                self.goto(set);
                self.cur = set;
                if matches!(mode, M::SplitN | M::RSplitN) {
                    let (l2, u2) = (self.local(USIZE), self.local(USIZE));
                    self.call_builtin(Builtin::Min, vec![Operand::Copy(f(3)), Operand::Copy(Place::local(lo))], Place::local(l2));
                    self.call_builtin(Builtin::Min, vec![Operand::Copy(f(3)), Operand::Copy(Place::local(up))], Place::local(u2));
                    self.assign(Place::local(lo), Rvalue::Use(Operand::Copy(Place::local(l2))));
                    self.assign(Place::local(up), Rvalue::Use(Operand::Copy(Place::local(u2))));
                }
                self.some(&Place::local(hi), ou, Operand::Copy(Place::local(up)));
            }
            // `ChunkBy`: `(0, Some(0))` when empty, else `(1, Some(len))`.
            K::ChunkBy | K::ChunkByMut => {
                let len = self.local(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(f(0).deref()));
                let c = self.cmp(Eq, Operand::Copy(Place::local(len)), Self::usize_c(0));
                let lo1 = self.local(USIZE);
                self.assign(Place::local(lo1), Rvalue::Use(Operand::Const(Const::Int(0, IntTy::Usize))));
                let (empty, some) = self.branch(c);
                let set = self.block();
                self.cur = some;
                self.assign(Place::local(lo1), Rvalue::Use(Self::usize_c(1)));
                self.goto(set);
                self.cur = empty;
                self.goto(set);
                self.cur = set;
                self.assign(Place::local(lo), Rvalue::Use(Operand::Copy(Place::local(lo1))));
                self.some(&Place::local(hi), ou, Operand::Copy(Place::local(len)));
            }
            // `env::Args`: exact, back index minus front index.
            K::Args => {
                let n = self.local(USIZE);
                self.assign(Place::local(n), Rvalue::Bin(Sub, Operand::Copy(f(1)), Operand::Copy(f(0))));
                set_exact(self, Operand::Copy(Place::local(n)));
            }
            K::Chunks | K::ChunksMut | K::ChunksExact | K::ChunksExactMut => {
                let n = self.size(itp.clone(), ty)?;
                set_exact(self, n);
            }
            // `Utf8Chunks`: std's default `(0, None)`.
            K::Utf8Chunks | K::Utf8Chunk => {
                self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(0)));
                self.none(&Place::local(hi), ou);
            }
            // `&mut I` over a builtin iterator: its own hint.
            K::ByNext if let Some(inner) = self.by_mut_builtin(a[0]) => {
                let at = self.by_mut_place(a[0], f(0));
                let (l, h) = self.hint(at, inner)?;
                self.assign(Place::local(lo), Rvalue::Use(Operand::Copy(Place::local(l))));
                self.assign(Place::local(hi), Rvalue::Use(Operand::Move(Place::local(h))));
            }
            // The wrapped iterator's own `size_hint`, else the trait's
            // default `(0, None)` (W-STD-B).
            K::ByNext => match crate::check::iter::by_next_fns(self.p, &self.body.tys, self.by_next_held(a[0], f(0)).0)?.size_hint {
                Some(sh) => {
                    let (inner, at) = self.by_next_held(a[0], f(0));
                    let r = self.ref_to(false, at, inner);
                    let tt = self.tuple_ty(&[USIZE, ou]);
                    let t = self.local(tt);
                    self.call(CallTarget::Fn(sh), vec![Operand::Move(Place::local(r))], Place::local(t));
                    self.assign(Place::local(lo), Rvalue::Use(Operand::Copy(Place::local(t).project(Proj::Field(0)))));
                    self.assign(Place::local(hi), Rvalue::Use(Operand::Move(Place::local(t).project(Proj::Field(1)))));
                }
                None => {
                    self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(0)));
                    self.none(&Place::local(hi), ou);
                }
            },
            // hashbrown's iterators know their remaining count exactly.
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
            | K::SetDrain => {
                let r = self.ref_to(false, itp, ty);
                let n = self.local(USIZE);
                self.call_builtin(Builtin::HashIterLen, vec![Operand::Move(Place::local(r))], Place::local(n));
                set_exact(self, Operand::Copy(Place::local(n)));
            }
            K::VecDrain => {
                let r = self.ref_to(false, itp, ty);
                let n = self.local(USIZE);
                self.call_builtin(Builtin::VecDrainLen, vec![Operand::Move(Place::local(r))], Place::local(n));
                set_exact(self, Operand::Copy(Place::local(n)));
            }
            K::StringDrain => {
                // The `Chars` hint over the bytes left, as above.
                let r = self.ref_to(false, itp, ty);
                let bytes = self.local(USIZE);
                self.call_builtin(Builtin::VecDrainLen, vec![Operand::Move(Place::local(r))], Place::local(bytes));
                let b3 = self.local(USIZE);
                self.assign(Place::local(b3), Rvalue::Bin(Add, Operand::Copy(Place::local(bytes)), Self::usize_c(3)));
                self.assign(Place::local(lo), Rvalue::Bin(Div, Operand::Copy(Place::local(b3)), Self::usize_c(4)));
                self.some(&Place::local(hi), ou, Operand::Copy(Place::local(bytes)));
            }
            // `(usize::MAX, None)`.
            K::RangeFrom => {
                self.assign(Place::local(lo), Rvalue::Use(Operand::Const(Const::Int(u128::from(u64::MAX), IntTy::Usize))));
                self.none(&Place::local(hi), ou);
            }
            K::RangeTo | K::RangeFull | K::RangeToInclusive => {
                return Err("iterator expansion: size_hint of an open-ended range kind".into());
            }
            K::RangeInclusive => {
                // Exhausted or empty: (0, Some(0)); else steps + 1, with
                // `checked_add` on the upper bound.
                let join = self.block();
                let zero = self.block();
                let (ex, live) = self.branch(Operand::Copy(f(2)));
                self.cur = ex;
                self.goto(zero);
                self.cur = live;
                let c = self.cmp(Le, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (go, empty) = self.branch(c);
                self.cur = empty;
                self.goto(zero);
                self.cur = go;
                let wide = int(IntTy::I128);
                let (l0, l1) = (self.local(wide), self.local(wide));
                self.assign(Place::local(l0), Rvalue::Cast(Operand::Copy(f(0)), wide));
                self.assign(Place::local(l1), Rvalue::Cast(Operand::Copy(f(1)), wide));
                let d = self.local(wide);
                self.assign(Place::local(d), Rvalue::Bin(Sub, Operand::Copy(Place::local(l1)), Operand::Copy(Place::local(l0))));
                let steps = self.local(USIZE);
                self.assign(Place::local(steps), Rvalue::Cast(Operand::Copy(Place::local(d)), USIZE));
                self.call_builtin(Builtin::SaturatingAdd, vec![Operand::Copy(Place::local(steps)), Self::usize_c(1)], Place::local(lo));
                self.call_builtin(Builtin::CheckedAdd, vec![Operand::Copy(Place::local(steps)), Self::usize_c(1)], Place::local(hi));
                self.goto(join);
                self.cur = zero;
                set_exact(self, Self::usize_c(0));
                self.goto(join);
                self.cur = join;
            }
            K::Map | K::Inspect | K::Copied | K::Cloned | K::Enumerate | K::Rev => return self.hint(f(0), a[0]),
            // `ProcessResults::size_hint`: no lower bound (the next
            // item can fail), the source's upper bound.
            K::TryCollect => {
                let (_, ihi) = self.hint(f(0), a[0])?;
                self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(0)));
                self.assign(Place::local(hi), Rvalue::Use(Operand::Move(Place::local(ihi))));
            }
            // `CharIndices` forwards to its `Chars`.
            K::CharIndices => return self.hint(f(0), CHARS),
            // The str matches forms: std's default `(0, None)`.
            K::StrMatches => {
                self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(0)));
                self.none(&Place::local(hi), ou);
            }
            // `EncodeUtf16` (tf-str): with `b` bytes left in the
            // `Chars` and a buffered low surrogate counted in `x`,
            // `((b + 2) / 3 + x, Some(b + x))`, as std bounds it.
            K::EncodeUtf16 => {
                let bytes = self.local(USIZE);
                let r = self.ref_to(false, f(0), CHARS);
                self.call_builtin(Builtin::CharsBytesLeft, vec![Operand::Move(Place::local(r))], Place::local(bytes));
                let x = self.local(USIZE);
                let has = self.cmp(Ne, Operand::Copy(f(1)), Self::usize_c(0));
                let (hb, nb) = self.branch(has);
                let after_x = self.block();
                self.cur = hb;
                self.assign(Place::local(x), Rvalue::Use(Self::usize_c(1)));
                self.goto(after_x);
                self.cur = nb;
                self.assign(Place::local(x), Rvalue::Use(Self::usize_c(0)));
                self.goto(after_x);
                self.cur = after_x;
                let b2 = self.local(USIZE);
                self.assign(Place::local(b2), Rvalue::Bin(Add, Operand::Copy(Place::local(bytes)), Self::usize_c(2)));
                let base = self.local(USIZE);
                self.assign(Place::local(base), Rvalue::Bin(Div, Operand::Copy(Place::local(b2)), Self::usize_c(3)));
                self.assign(Place::local(lo), Rvalue::Bin(Add, Operand::Copy(Place::local(base)), Operand::Copy(Place::local(x))));
                let top = self.local(USIZE);
                self.assign(Place::local(top), Rvalue::Bin(Add, Operand::Copy(Place::local(bytes)), Operand::Copy(Place::local(x))));
                self.some(&Place::local(hi), ou, Operand::Copy(Place::local(top)));
            }
            // The str splits: std's default `(0, None)`, but
            // `split_ascii_whitespace`, whose slice split bounds it.
            K::StrSplit => {
                self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(0)));
                if it::split_mode(&self.body.tys, a[1]) == Some(it::SplitMode::SplitAsciiWhitespace) {
                    let r = self.ref_to(false, itp, ty);
                    let u = self.local(USIZE);
                    self.call_builtin(Builtin::StrSplitUpper, vec![Operand::Move(Place::local(r))], Place::local(u));
                    self.some(&Place::local(hi), ou, Operand::Copy(Place::local(u)));
                } else {
                    self.none(&Place::local(hi), ou);
                }
            }
            // The `option` and `result` iterators: exact, 0 or 1.
            K::OptionIntoIter | K::OptionIter | K::OptionIterMut | K::ResultIter | K::ResultIterMut | K::ResultIntoIter => {
                let (s, n) = self.switch_opt(&f(0));
                let j2 = self.block();
                self.cur = s;
                set_exact(self, Self::usize_c(1));
                self.goto(j2);
                self.cur = n;
                set_exact(self, Self::usize_c(0));
                self.goto(j2);
                self.cur = j2;
            }
            // `Flatten`: std's FlattenCompat::size_hint, with the fixed-size
            // form for array items (ConstSizeIntoIterator).
            K::Flatten => {
                let (flo, fhi) = self.flat_side_hint(f(1), a[1])?;
                let (blo, bhi) = self.flat_side_hint(f(2), a[1])?;
                let sum = self.local(USIZE);
                self.call_builtin(Builtin::SaturatingAdd, vec![Operand::Copy(Place::local(flo)), Operand::Copy(Place::local(blo))], Place::local(sum));
                // The outer iterator's hint ((0, Some(0)) once it ended).
                let (ilo, ihi) = (self.local(USIZE), self.local(ou));
                {
                    let (s, n) = self.switch_opt(&f(0));
                    let j2 = self.block();
                    self.cur = s;
                    let (l, h) = self.hint(Self::payload(&f(0)), a[0])?;
                    self.assign(Place::local(ilo), Rvalue::Use(Operand::Copy(Place::local(l))));
                    self.assign(Place::local(ihi), Rvalue::Use(Operand::Move(Place::local(h))));
                    self.goto(j2);
                    self.cur = n;
                    self.assign(Place::local(ilo), Rvalue::Use(Self::usize_c(0)));
                    self.some(&Place::local(ihi), ou, Self::usize_c(0));
                    self.goto(j2);
                    self.cur = j2;
                }
                let x = self.item(a[0])?;
                let none_hi = |this: &mut Self| this.none(&Place::local(hi), ou);
                match self.const_size(x) {
                    Some(fixed) => {
                        // lower = ilo * N + sum (saturating); upper = fhi? + bhi? + N * ihi? (checked).
                        let prod = self.local(USIZE);
                        self.call_builtin(Builtin::SaturatingMul, vec![Operand::Copy(Place::local(ilo)), Self::usize_c(fixed)], Place::local(prod));
                        self.call_builtin(Builtin::SaturatingAdd, vec![Operand::Copy(Place::local(prod)), Operand::Copy(Place::local(sum))], Place::local(lo));
                        let j2 = self.block();
                        let mut parts = vec![(fhi, None), (bhi, None), (ihi, Some(fixed))];
                        let acc = self.local(USIZE);
                        self.assign(Place::local(acc), Rvalue::Use(Self::usize_c(0)));
                        let fail = self.block();
                        for (h, mul) in parts.drain(..) {
                            let (s, n) = self.switch_opt(&Place::local(h));
                            self.cur = n;
                            self.goto(fail);
                            self.cur = s;
                            let v = match mul {
                                Some(m) => {
                                    let ck = self.local(ou);
                                    self.call_builtin(Builtin::CheckedMul, vec![Operand::Copy(Self::payload(&Place::local(h))), Self::usize_c(m)], Place::local(ck));
                                    let (ms, mn) = self.switch_opt(&Place::local(ck));
                                    self.cur = mn;
                                    self.goto(fail);
                                    self.cur = ms;
                                    Operand::Copy(Self::payload(&Place::local(ck)))
                                }
                                None => Operand::Copy(Self::payload(&Place::local(h))),
                            };
                            let ck = self.local(ou);
                            self.call_builtin(Builtin::CheckedAdd, vec![Operand::Copy(Place::local(acc)), v], Place::local(ck));
                            let (as_, an) = self.switch_opt(&Place::local(ck));
                            self.cur = an;
                            self.goto(fail);
                            self.cur = as_;
                            self.assign(Place::local(acc), Rvalue::Use(Operand::Copy(Self::payload(&Place::local(ck)))));
                        }
                        self.some(&Place::local(hi), ou, Operand::Copy(Place::local(acc)));
                        self.goto(j2);
                        self.cur = fail;
                        none_hi(self);
                        self.goto(j2);
                        self.cur = j2;
                    }
                    // std's `OneShot` specialization: an inner iterator of
                    // at most one item never stays in front or back, so
                    // the hint is (0, the outer's upper).
                    None if self.one_shot(a[1]) => {
                        self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(0)));
                        self.assign(Place::local(hi), Rvalue::Use(Operand::Move(Place::local(ihi))));
                    }
                    None => {
                        // (lo, fhi + bhi) only when the outer is exactly empty.
                        self.assign(Place::local(lo), Rvalue::Use(Operand::Copy(Place::local(sum))));
                        let j2 = self.block();
                        let other = self.block();
                        let c0 = self.cmp(Eq, Operand::Copy(Place::local(ilo)), Self::usize_c(0));
                        let (z, nz) = self.branch(c0);
                        self.cur = nz;
                        self.goto(other);
                        self.cur = z;
                        let (is, inn) = self.switch_opt(&Place::local(ihi));
                        self.cur = inn;
                        self.goto(other);
                        self.cur = is;
                        let c1 = self.cmp(Eq, Operand::Copy(Self::payload(&Place::local(ihi))), Self::usize_c(0));
                        let (z2, nz2) = self.branch(c1);
                        self.cur = nz2;
                        self.goto(other);
                        self.cur = z2;
                        let (fs, fnn) = self.switch_opt(&Place::local(fhi));
                        self.cur = fnn;
                        self.goto(other);
                        self.cur = fs;
                        let (bs, bnn) = self.switch_opt(&Place::local(bhi));
                        self.cur = bnn;
                        self.goto(other);
                        self.cur = bs;
                        self.call_builtin(
                            Builtin::CheckedAdd,
                            vec![Operand::Copy(Self::payload(&Place::local(fhi))), Operand::Copy(Self::payload(&Place::local(bhi)))],
                            Place::local(hi),
                        );
                        self.goto(j2);
                        self.cur = other;
                        none_hi(self);
                        self.goto(j2);
                        self.cur = j2;
                    }
                }
            }
            // `MapWhile`: `(0, upper)` of the inner hint, as core's.
            K::Filter | K::FilterMap | K::MapWhile | K::SkipWhile => {
                let (_, ih) = self.hint(f(0), a[0])?;
                self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(0)));
                self.assign(Place::local(hi), Rvalue::Use(Operand::Move(Place::local(ih))));
            }
            K::TakeWhile => {
                let join = self.block();
                let (done, open) = self.branch(Operand::Copy(f(1)));
                self.cur = done;
                set_exact(self, Self::usize_c(0));
                self.goto(join);
                self.cur = open;
                let (_, ih) = self.hint(f(0), a[0])?;
                self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(0)));
                self.assign(Place::local(hi), Rvalue::Use(Operand::Move(Place::local(ih))));
                self.goto(join);
                self.cur = join;
            }
            K::Take => {
                let join = self.block();
                let z = self.cmp(Eq, Operand::Copy(f(1)), Self::usize_c(0));
                let (zero, go) = self.branch(z);
                self.cur = zero;
                set_exact(self, Self::usize_c(0));
                self.goto(join);
                self.cur = go;
                let (il, ih) = self.hint(f(0), a[0])?;
                self.call_builtin(Builtin::Min, vec![Operand::Copy(Place::local(il)), Operand::Copy(f(1))], Place::local(lo));
                // Some(x) if x < n => Some(x), _ => Some(n)
                let (s, n) = self.switch_opt(&Place::local(ih));
                let take_n = self.block();
                self.cur = s;
                let x = Self::payload(&Place::local(ih));
                let lt = self.cmp(Lt, Operand::Copy(x.clone()), Operand::Copy(f(1)));
                let (keep, cap) = self.branch(lt);
                self.cur = keep;
                self.some(&Place::local(hi), ou, Operand::Copy(x));
                self.goto(join);
                self.cur = cap;
                self.goto(take_n);
                self.cur = n;
                self.goto(take_n);
                self.cur = take_n;
                self.some(&Place::local(hi), ou, Operand::Copy(f(1)));
                self.goto(join);
                self.cur = join;
            }
            K::Skip => {
                let (il, ih) = self.hint(f(0), a[0])?;
                self.call_builtin(Builtin::SaturatingSub, vec![Operand::Copy(Place::local(il)), Operand::Copy(f(1))], Place::local(lo));
                let join = self.block();
                let (s, n) = self.switch_opt(&Place::local(ih));
                self.cur = s;
                let x = self.local(USIZE);
                self.call_builtin(Builtin::SaturatingSub, vec![Operand::Copy(Self::payload(&Place::local(ih))), Operand::Copy(f(1))], Place::local(x));
                self.some(&Place::local(hi), ou, Operand::Copy(Place::local(x)));
                self.goto(join);
                self.cur = n;
                self.none(&Place::local(hi), ou);
                self.goto(join);
                self.cur = join;
            }
            K::Chain => {
                // (Some, Some): saturating sum, checked upper; one side
                // alone: its hint; neither: (0, Some(0)).
                let join = self.block();
                let (as_, an) = self.switch_opt(&f(0));
                self.cur = as_;
                let (al, ah) = self.hint(Self::payload(&f(0)), a[0])?;
                let (bs, bn) = self.switch_opt(&f(1));
                self.cur = bs;
                let (bl, bh) = self.hint(Self::payload(&f(1)), a[1])?;
                self.call_builtin(Builtin::SaturatingAdd, vec![Operand::Copy(Place::local(al)), Operand::Copy(Place::local(bl))], Place::local(lo));
                let both_none = self.block();
                let (ahs, ahn) = self.switch_opt(&Place::local(ah));
                self.cur = ahn;
                self.goto(both_none);
                self.cur = ahs;
                let (bhs, bhn) = self.switch_opt(&Place::local(bh));
                self.cur = bhn;
                self.goto(both_none);
                self.cur = bhs;
                self.call_builtin(
                    Builtin::CheckedAdd,
                    vec![Operand::Copy(Self::payload(&Place::local(ah))), Operand::Copy(Self::payload(&Place::local(bh)))],
                    Place::local(hi),
                );
                self.goto(join);
                self.cur = both_none;
                self.none(&Place::local(hi), ou);
                self.goto(join);
                self.cur = bn;
                self.assign(Place::local(lo), Rvalue::Use(Operand::Copy(Place::local(al))));
                self.assign(Place::local(hi), Rvalue::Use(Operand::Copy(Place::local(ah))));
                self.goto(join);
                self.cur = an;
                let (bs2, bn2) = self.switch_opt(&f(1));
                self.cur = bs2;
                let (bl2, bh2) = self.hint(Self::payload(&f(1)), a[1])?;
                self.assign(Place::local(lo), Rvalue::Use(Operand::Copy(Place::local(bl2))));
                self.assign(Place::local(hi), Rvalue::Use(Operand::Copy(Place::local(bh2))));
                self.goto(join);
                self.cur = bn2;
                set_exact(self, Self::usize_c(0));
                self.goto(join);
                self.cur = join;
            }
            K::Zip => {
                // The general impl: min of the lowers; the upper is the
                // min of the known uppers.
                let (al, ah) = self.hint(f(0), a[0])?;
                let (bl, bh) = self.hint(f(1), a[1])?;
                self.call_builtin(Builtin::Min, vec![Operand::Copy(Place::local(al)), Operand::Copy(Place::local(bl))], Place::local(lo));
                let join = self.block();
                let (ahs, ahn) = self.switch_opt(&Place::local(ah));
                self.cur = ahs;
                let (bhs, bhn) = self.switch_opt(&Place::local(bh));
                self.cur = bhs;
                let m = self.local(USIZE);
                self.call_builtin(
                    Builtin::Min,
                    vec![Operand::Copy(Self::payload(&Place::local(ah))), Operand::Copy(Self::payload(&Place::local(bh)))],
                    Place::local(m),
                );
                self.some(&Place::local(hi), ou, Operand::Copy(Place::local(m)));
                self.goto(join);
                self.cur = bhn;
                self.assign(Place::local(hi), Rvalue::Use(Operand::Copy(Place::local(ah))));
                self.goto(join);
                self.cur = ahn;
                self.assign(Place::local(hi), Rvalue::Use(Operand::Copy(Place::local(bh))));
                self.goto(join);
                self.cur = join;
            }
            K::StepBy => {
                // `first_size` (1 + (n - 1) / step for n > 0) before the
                // first take, `other_size` (n / step) after; the upper
                // bound maps the same way.
                let (il, ih) = self.hint(f(0), a[0])?;
                let step = self.local(USIZE);
                self.assign(Place::local(step), Rvalue::Bin(Add, Operand::Copy(f(1)), Self::usize_c(1)));
                let size = |this: &mut Self, n: Operand, out: Place| {
                    let join = this.block();
                    let (first, other) = this.branch(Operand::Copy(f(2)));
                    this.cur = first;
                    let z = this.cmp(Eq, n.clone(), Self::usize_c(0));
                    let (zero, pos) = this.branch(z);
                    this.cur = zero;
                    this.assign(out.clone(), Rvalue::Use(Self::usize_c(0)));
                    this.goto(join);
                    this.cur = pos;
                    let (m, q) = (this.local(USIZE), this.local(USIZE));
                    this.assign(Place::local(m), Rvalue::Bin(Sub, n.clone(), Self::usize_c(1)));
                    this.assign(Place::local(q), Rvalue::Bin(Div, Operand::Copy(Place::local(m)), Operand::Copy(Place::local(step))));
                    this.assign(out.clone(), Rvalue::Bin(Add, Operand::Copy(Place::local(q)), Self::usize_c(1)));
                    this.goto(join);
                    this.cur = other;
                    this.assign(out, Rvalue::Bin(Div, n, Operand::Copy(Place::local(step))));
                    this.goto(join);
                    this.cur = join;
                };
                size(self, Operand::Copy(Place::local(il)), Place::local(lo));
                let join = self.block();
                let (s, n) = self.switch_opt(&Place::local(ih));
                self.cur = s;
                let x = self.local(USIZE);
                size(self, Operand::Copy(Self::payload(&Place::local(ih))), Place::local(x));
                self.some(&Place::local(hi), ou, Operand::Copy(Place::local(x)));
                self.goto(join);
                self.cur = n;
                self.none(&Place::local(hi), ou);
                self.goto(join);
                self.cur = join;
            }
            K::Peekable => {
                // A peeked `None` ends it; a peeked item adds 1.
                let join = self.block();
                let slot = f(1);
                let add = self.local(USIZE);
                let go = self.block();
                let (full, empty) = self.switch_opt(&slot);
                self.cur = empty;
                self.assign(Place::local(add), Rvalue::Use(Self::usize_c(0)));
                self.goto(go);
                self.cur = full;
                let (some, none) = self.switch_opt(&Self::payload(&slot));
                self.cur = none;
                set_exact(self, Self::usize_c(0));
                self.goto(join);
                self.cur = some;
                self.assign(Place::local(add), Rvalue::Use(Self::usize_c(1)));
                self.goto(go);
                self.cur = go;
                let (il, ih) = self.hint(f(0), a[0])?;
                self.call_builtin(Builtin::SaturatingAdd, vec![Operand::Copy(Place::local(il)), Operand::Copy(Place::local(add))], Place::local(lo));
                let (hs, hn) = self.switch_opt(&Place::local(ih));
                self.cur = hs;
                self.call_builtin(Builtin::CheckedAdd, vec![Operand::Copy(Self::payload(&Place::local(ih))), Operand::Copy(Place::local(add))], Place::local(hi));
                self.goto(join);
                self.cur = hn;
                self.none(&Place::local(hi), ou);
                self.goto(join);
                self.cur = join;
            }
            K::SliceIter | K::SliceIterMut | K::Range => unreachable!("handled above"),
        }
        Ok((lo, hi))
    }

    /// True when Rust 1.99 implements `TrustedLen` for this type (the
    /// kinds lust has), which picks `collect`'s exact-capacity path.
    fn trusted_len(&mut self, ty: Ty) -> bool {
        use IterKind as K;
        let Some((k, a)) = self.kind_args(ty) else { return false };
        match k {
            K::SliceIter | K::SliceIterMut | K::VecIntoIter | K::Range | K::RangeInclusive | K::VecDrain => true,
            K::Map | K::Enumerate | K::Rev | K::Take | K::Copied | K::Cloned | K::Peekable => self.trusted_len(a[0]),
            K::Chain | K::Zip => self.trusted_len(a[0]) && self.trusted_len(a[1]),
            K::Skip | K::StepBy => self.tra_coerce(a[0]),
            K::Filter | K::FilterMap | K::MapWhile | K::TakeWhile | K::SkipWhile | K::Inspect => false,
            K::RecvIter | K::RecvTryIter | K::RecvIntoIter => false,
            // Not `TrustedLen` in Rust 1.99 (`collect` of two keys
            // allocates 4).
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
            | K::SetDrain => false,
            K::ArrayIntoIter | K::RepeatN => true,
            // A user iterator may implement the unstable TrustedLen only
            // in std itself: of the std source iterators, core's `Once`
            // and `OnceWith` do (library/core/src/iter.rs).
            // core: `impl<I: TrustedLen + ?Sized> TrustedLen for &mut I`.
            K::ByNext if let Some(inner) = self.by_mut_builtin(a[0]) => self.trusted_len(inner),
            K::ByNext => self.std_trusted_len(a[0]),
            K::CharIndices | K::StrSplit | K::StrMatches | K::EncodeUtf16 => false,
            K::Windows | K::OptionIntoIter | K::OptionIter | K::OptionIterMut | K::ResultIter | K::ResultIterMut | K::ResultIntoIter => {
                true
            }
            K::Chunks | K::ChunksMut | K::ChunksExact | K::ChunksExactMut => true,
            K::Utf8Chunks | K::Utf8Chunk => false,
            // std's impls: an outer TrustedLen over arrays (or references
            // to arrays) of a fixed size.
            K::Flatten => self.trusted_len(a[0]) && self.item_const_size(a[0]).is_some(),
            // `TrustedLen for RangeFrom<A: TrustedStep>` (ints and char).
            K::RangeFrom => true,
            K::StringDrain | K::RangeTo | K::RangeFull | K::RangeToInclusive => false,
            // `ProcessResults` is not `TrustedLen` (a failure can
            // end it early), whatever the source is.
            K::TryCollect => false,
            // `env::Args` and the slice splits are not `TrustedLen` in std.
            K::Args | K::SliceSplit | K::SliceSplitMut | K::ChunkBy | K::ChunkByMut => false,
        }
    }

    /// True for the inner iterators Rust 1.99 marks `OneShot` (at most
    /// one item; core/src/iter/adapters/flatten.rs): `Once`, `OnceWith`,
    /// the Option and Result iterators, `array::IntoIter<T, 0 or 1>`,
    /// and `Map`, `Filter`, `FilterMap`, `Copied`, `Cloned` over one.
    fn one_shot(&self, ty: Ty) -> bool {
        use IterKind as K;
        let Some((k, a)) = self.kind_args(ty) else { return false };
        match k {
            K::OptionIntoIter | K::OptionIter | K::OptionIterMut | K::ResultIntoIter | K::ResultIter | K::ResultIterMut => true,
            K::ArrayIntoIter => self.const_size(a[1]).is_some_and(|n| n <= 1),
            K::ByNext => self.std_trusted_len(a[0]),
            K::Map | K::Filter | K::FilterMap | K::Copied | K::Cloned => self.one_shot(a[0]),
            _ => false,
        }
    }

    /// True for the std source iterator types that Rust 1.99 marks
    /// `TrustedLen` (`unsafe impl` in core/src/iter/sources/once.rs and
    /// once_with.rs). `FromFn` and `Successors` are not.
    fn std_trusted_len(&self, t: Ty) -> bool {
        let Some(a) = self.body.tys.local_adt(t) else { return false };
        self.p.is_std_adt(a) && matches!(self.p.display_path(self.p.adt(a).name).as_str(), "core::iter::Once" | "core::iter::OnceWith" | "core::iter::Repeat" | "core::iter::RepeatWith")
    }

    /// `dest = itp.start_bound()` (or `end_bound`), a `Bound<&T>`
    /// over the stored field of a builtin range kind, or over one
    /// side of a `(Bound<T>, Bound<T>)` pair reborrowed through
    /// `Bound::as_ref`.
    fn range_bound(&mut self, itp: Place, ty: Ty, dest: Place, dest_ty: Ty, start: bool) -> R {
        use IterKind as K;
        let bound = match self.body.tys.local_adt(dest_ty) {
            Some(a) => a,
            None => self.p.adt_by_def(crate::check::generics::bound_def()).ok_or("iterator expansion: Bound has no Adt")?,
        };
        let idx = crate::check::generics::bound_elem(&self.body.tys, dest_ty)
            .and_then(|r| match self.body.tys.kind(r) {
                TyKind::Ref(_, _, i) => Some(i),
                _ => None,
            })
            .ok_or("iterator expansion: bound has no index type")?;
        let incl = |this: &mut Self, pl: Place, variant: u32| {
            let r = this.ref_to(false, pl, idx);
            this.assign(dest.clone(), Rvalue::Aggregate(bound, variant, vec![Operand::Move(Place::local(r))]));
        };
        let f = |i: u32| itp.project(Proj::Field(i));
        if let Some((k, _)) = self.kind_args(ty) {
            match (k, start) {
                (K::Range, true) | (K::RangeInclusive, true) | (K::RangeFrom, true) => incl(self, f(0), 0),
                (K::Range, false) => incl(self, f(1), 1),
                // core: `Excluded(&start)` once exhausted (empty).
                (K::RangeInclusive, false) => {
                    let (ex, live) = self.branch(Operand::Copy(f(2)));
                    let join = self.block();
                    self.cur = ex;
                    incl(self, f(0), 1);
                    self.goto(join);
                    self.cur = live;
                    incl(self, f(1), 0);
                    self.goto(join);
                    self.cur = join;
                }
                (K::RangeTo, false) => incl(self, f(0), 1),
                (K::RangeToInclusive, false) => incl(self, f(0), 0),
                _ => self.assign(dest, Rvalue::Aggregate(bound, 2, Vec::new())),
            }
            return Ok(());
        }
        // A `(Bound<T>, Bound<T>)` pair: the side's own variant,
        // with a reference to its payload.
        let side = f(if start { 0 } else { 1 });
        let join = self.block();
        let d = self.local(int(IntTy::U32));
        self.assign(Place::local(d), Rvalue::Discriminant(side.clone()));
        let (inc_b, exc_b, unb_b) = (self.block(), self.block(), self.block());
        self.term(Terminator::Switch(Operand::Copy(Place::local(d)), vec![(0, inc_b), (1, exc_b)], unb_b));
        let payload_is_ref = match self.body.tys.kind(ty) {
            TyKind::Tuple(ts) => {
                let es: Vec<Ty> = self.body.tys.tys_of(ts).to_vec();
                es.first().and_then(|&e| crate::check::generics::bound_elem(&self.body.tys, e))
                    .is_some_and(|p| matches!(self.body.tys.kind(p), TyKind::Ref(..)))
            }
            _ => false,
        };
        for (bb, variant) in [(inc_b, 0u32), (exc_b, 1u32)] {
            self.cur = bb;
            let payload = side.project(Proj::Downcast(variant)).project(Proj::Field(0));
            let op = if payload_is_ref {
                Operand::Copy(payload)
            } else {
                let r = self.ref_to(false, payload, idx);
                Operand::Move(Place::local(r))
            };
            self.assign(dest.clone(), Rvalue::Aggregate(bound, variant, vec![op]));
            self.goto(join);
        }
        self.cur = unb_b;
        self.assign(dest, Rvalue::Aggregate(bound, 2, Vec::new()));
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// One `Bound` inherent method (`as_ref`, `map`, `cloned`): rebuild the same variant of the destination
    /// `Bound` around the transformed payload.
    fn bound_map_like(&mut self, b: Builtin, itp: Place, ty: Ty, f: Option<(Place, Ty)>, dest: Place, dest_ty: Ty) -> R {
        let bound = match self.body.tys.local_adt(dest_ty) {
            Some(a) => a,
            None => self.p.adt_by_def(crate::check::generics::bound_def()).ok_or("iterator expansion: Bound has no Adt")?,
        };
        let elem = crate::check::generics::bound_elem(&self.body.tys, ty).ok_or("iterator expansion: Bound has no type argument")?;
        let out_elem = crate::check::generics::bound_elem(&self.body.tys, dest_ty).ok_or("iterator expansion: Bound has no type argument")?;
        let join = self.block();
        let d = self.local(int(IntTy::U32));
        self.assign(Place::local(d), Rvalue::Discriminant(itp.clone()));
        let (inc_b, exc_b, unb_b) = (self.block(), self.block(), self.block());
        self.term(Terminator::Switch(Operand::Copy(Place::local(d)), vec![(0, inc_b), (1, exc_b)], unb_b));
        for (bb, variant) in [(inc_b, 0u32), (exc_b, 1u32)] {
            self.cur = bb;
            let payload = itp.project(Proj::Downcast(variant)).project(Proj::Field(0));
            let op = match b {
                Builtin::BoundAsRef => {
                    let r = self.ref_to(false, payload, elem);
                    Operand::Move(Place::local(r))
                }
                Builtin::BoundCloned => {
                    let y = self.local(out_elem);
                    self.call_builtin(Builtin::Clone, vec![Operand::Copy(payload)], Place::local(y));
                    Operand::Move(Place::local(y))
                }
                _ => {
                    let (fp, fty) = f.clone().ok_or("iterator expansion: Bound::map has no closure")?;
                    let y = self.local(out_elem);
                    let x = self.take(payload, elem);
                    self.call_fn(fty, fp, vec![x], Place::local(y))?;
                    Operand::Move(Place::local(y))
                }
            };
            self.assign(dest.clone(), Rvalue::Aggregate(bound, variant, vec![op]));
            self.goto(join);
        }
        self.cur = unb_b;
        self.assign(dest, Rvalue::Aggregate(bound, 2, Vec::new()));
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// One range query (`is_empty`, `contains`, or
    /// `RangeInclusive::start`/`end`) over a builtin range kind's
    /// stored fields, or one pair side per bound for a
    /// `(Bound, Bound)` pair's `contains` (core's formulas).
    fn range_query(&mut self, b: Builtin, itp: Place, ty: Ty, item: Option<Place>, dest: Place) -> R {
        use crate::ast::BinOp::{And, Ge, Le, Lt, Or};
        use IterKind as K;
        let f = |i: u32| itp.project(Proj::Field(i));
        let cp = |pl: Place| Operand::Copy(pl);
        if b == Builtin::RangeInclStart || b == Builtin::RangeInclEnd {
            let idx = self.kind_args(ty).map(|(_, a)| a[0]).ok_or("iterator expansion: range has no index type")?;
            let r = self.ref_to(false, f(if b == Builtin::RangeInclStart { 0 } else { 1 }), idx);
            self.assign(dest, Rvalue::Use(Operand::Move(Place::local(r))));
            return Ok(());
        }
        if let Some((k, _)) = self.kind_args(ty) {
            if b == Builtin::RangeIsEmpty {
                let v = match k {
                    K::Range => self.cmp(Ge, cp(f(0)), cp(f(1))),
                    K::RangeInclusive => {
                        let gt = self.cmp(crate::ast::BinOp::Gt, cp(f(0)), cp(f(1)));
                        self.cmp(Or, Operand::Copy(f(2)), gt)
                    }
                    _ => return Err("iterator expansion: is_empty of a range kind without one".into()),
                };
                self.assign(dest, Rvalue::Use(v));
                return Ok(());
            }
            // contains
            let Some(x) = item else { return Err("iterator expansion: contains has no item".into()) };
            let xo = Operand::Copy(x);
            let both = |this: &mut Self, a: Operand, b2: Operand| this.cmp(And, a, b2);
            let v = match k {
                K::Range => {
                    let a = self.cmp(Le, cp(f(0)), xo.clone());
                    let b2 = self.cmp(Lt, xo, cp(f(1)));
                    both(self, a, b2)
                }
                // An exhausted range contains nothing: core's
                // `end_bound` is then `Excluded(&start)`.
                K::RangeInclusive => {
                    let a = self.cmp(Le, cp(f(0)), xo.clone());
                    let b2 = self.cmp(Le, xo, cp(f(1)));
                    let live = self.cmp(crate::ast::BinOp::Eq, cp(f(2)), Operand::Const(Const::Bool(false)));
                    let ab = both(self, a, b2);
                    both(self, ab, live)
                }
                K::RangeFrom => self.cmp(Le, cp(f(0)), xo),
                K::RangeTo => self.cmp(Lt, xo, cp(f(0))),
                K::RangeToInclusive => self.cmp(Le, xo, cp(f(0))),
                _ => Operand::Const(Const::Bool(true)),
            };
            self.assign(dest, Rvalue::Use(v));
            return Ok(());
        }
        // A `(Bound<T>, Bound<T>)` pair's contains: each side as core
        // tests it. The payload may be a reference itself.
        let Some(x) = item else { return Err("iterator expansion: contains has no item".into()) };
        let payload_is_ref = match self.body.tys.kind(ty) {
            TyKind::Tuple(ts) => {
                let es: Vec<Ty> = self.body.tys.tys_of(ts).to_vec();
                es.first().and_then(|&e| crate::check::generics::bound_elem(&self.body.tys, e))
                    .is_some_and(|p| matches!(self.body.tys.kind(p), TyKind::Ref(..)))
            }
            _ => false,
        };
        let mut side_ok = |this: &mut Self, side: Place, is_start: bool| -> Local {
            let out = this.local(BOOL);
            let d = this.local(int(IntTy::U32));
            this.assign(Place::local(d), Rvalue::Discriminant(side.clone()));
            let (inc_b, exc_b, unb_b, join) = (this.block(), this.block(), this.block(), this.block());
            this.term(Terminator::Switch(Operand::Copy(Place::local(d)), vec![(0, inc_b), (1, exc_b)], unb_b));
            for (bb, variant, strict) in [(inc_b, 0u32, false), (exc_b, 1u32, true)] {
                this.cur = bb;
                let mut payload = side.project(Proj::Downcast(variant)).project(Proj::Field(0));
                if payload_is_ref {
                    payload = payload.deref();
                }
                let v = match (is_start, strict) {
                    (true, false) => this.cmp(Le, Operand::Copy(payload), Operand::Copy(x.clone())),
                    (true, true) => this.cmp(Lt, Operand::Copy(payload), Operand::Copy(x.clone())),
                    (false, false) => this.cmp(Le, Operand::Copy(x.clone()), Operand::Copy(payload)),
                    (false, true) => this.cmp(Lt, Operand::Copy(x.clone()), Operand::Copy(payload)),
                };
                this.assign(Place::local(out), Rvalue::Use(v));
                this.goto(join);
            }
            this.cur = unb_b;
            this.assign(Place::local(out), Rvalue::Use(Operand::Const(Const::Bool(true))));
            this.goto(join);
            this.cur = join;
            out
        };
        let lo = side_ok(self, f(0), true);
        let hi = side_ok(self, f(1), false);
        let v = self.cmp(And, Operand::Copy(Place::local(lo)), Operand::Copy(Place::local(hi)));
        self.assign(dest, Rvalue::Use(v));
        Ok(())
    }

    // ---------- Consumers ----------

    /// One pull for a consumer loop: `t = it.next()`, then (some, none)
    /// with the item moved into a fresh local on the some side.
    fn pull(&mut self, itp: &Place, ty: Ty) -> Result<(Bb, Bb, Local, Ty), String> {
        let item = self.item(ty)?;
        let opt = self.body.tys.mk_option(item);
        let t = self.local(opt);
        self.next(itp.clone(), ty, Place::local(t), false)?;
        let (s, n) = self.switch_opt(&Place::local(t));
        self.cur = s;
        let x = self.local(item);
        let px = self.take(Self::payload(&Place::local(t)), item);
        self.assign(Place::local(x), Rvalue::Use(px));
        Ok((self.cur, n, x, item))
    }

    /// Internal iteration (Rust's `fold`, which `count`, `sum`,
    /// `for_each`, `last`, `max`, and `collect`'s trusted-length path
    /// use): `k` consumes each item local. It differs from a `next`
    /// loop only through a `Zip` of two `TrustedLen` sides, which folds
    /// exactly `min` pairs; the adapters Rust delegates `fold` through
    /// are followed down to it.
    fn each(&mut self, itp: &Place, ty: Ty, k: &mut dyn FnMut(&mut Self, Local, Ty) -> R) -> R {
        use IterKind as K;
        if !self.fold_differs(ty) {
            let lp = self.block();
            self.goto(lp);
            self.cur = lp;
            let (_, n, x, item) = self.pull(itp, ty)?;
            k(self, x, item)?;
            self.goto(lp);
            self.cur = n;
            return Ok(());
        }
        let (kd, a) = self.kind_args(ty).ok_or("iterator expansion: fold of a non-iterator")?;
        let f = |i: u32| itp.project(Proj::Field(i));
        let item = self.item(ty)?;
        match kd {
            K::Map | K::Inspect | K::Filter | K::FilterMap => {
                let fty = a[1];
                self.each(&f(0), a[0], &mut |this, x, xt| {
                    match kd {
                        K::Map => {
                            let y = this.local(item);
                            let ax = this.take(Place::local(x), xt);
                            this.call_fn(fty, f(1), vec![ax], Place::local(y))?;
                            k(this, y, item)
                        }
                        K::Inspect => {
                            let rx = this.ref_to(false, Place::local(x), xt);
                            let u = this.local(UNIT);
                            this.call_fn(fty, f(1), vec![Operand::Move(Place::local(rx))], Place::local(u))?;
                            k(this, x, xt)
                        }
                        K::Filter => {
                            let rx = this.ref_to(false, Place::local(x), xt);
                            let b = this.local(BOOL);
                            this.call_fn(fty, f(1), vec![Operand::Move(Place::local(rx))], Place::local(b))?;
                            let (yes, no) = this.branch(Operand::Copy(Place::local(b)));
                            let after = this.block();
                            this.cur = no;
                            this.drop_local(x);
                            this.goto(after);
                            this.cur = yes;
                            k(this, x, xt)?;
                            this.goto(after);
                            this.cur = after;
                            Ok(())
                        }
                        _ => {
                            let opt = this.body.tys.mk_option(item);
                            let o = this.local(opt);
                            let ax = this.take(Place::local(x), xt);
                            this.call_fn(fty, f(1), vec![ax], Place::local(o))?;
                            let (hit, miss) = this.switch_opt(&Place::local(o));
                            let after = this.block();
                            this.cur = miss;
                            this.goto(after);
                            this.cur = hit;
                            let y = this.local(item);
                            let py = this.take(Self::payload(&Place::local(o)), item);
                            this.assign(Place::local(y), Rvalue::Use(py));
                            k(this, y, item)?;
                            this.goto(after);
                            this.cur = after;
                            Ok(())
                        }
                    }
                })
            }
            K::Copied | K::Cloned => self.each(&f(0), a[0], &mut |this, r, _| {
                let y = this.local(item);
                if kd == K::Copied {
                    this.assign(Place::local(y), Rvalue::Use(Operand::Copy(Place::local(r).deref())));
                } else {
                    this.call_builtin(Builtin::Clone, vec![Operand::Copy(Place::local(r))], Place::local(y));
                }
                k(this, y, item)
            }),
            K::Enumerate => self.each(&f(0), a[0], &mut |this, x, xt| {
                let i = this.local(USIZE);
                this.assign(Place::local(i), Rvalue::Use(Operand::Copy(f(1))));
                this.assign(f(1), Rvalue::Bin(crate::ast::BinOp::Add, Operand::Copy(f(1)), Self::usize_c(1)));
                let ax = this.take(Place::local(x), xt);
                let tup = this.local(item);
                this.assign(Place::local(tup), Rvalue::TupleAgg(item, vec![Operand::Copy(Place::local(i)), ax]));
                k(this, tup, item)
            }),
            K::Peekable => {
                let slot = f(1);
                let done = self.block();
                let go = self.block();
                let (full, empty) = self.switch_opt(&slot);
                self.cur = empty;
                self.goto(go);
                self.cur = full;
                let (some, none) = self.switch_opt(&Self::payload(&slot));
                self.cur = none;
                self.goto(done);
                self.cur = some;
                let sty = self.place_ty(&slot)?;
                let o = self.local(sty);
                self.take_none(slot.clone(), sty, Place::local(o));
                let v = self.local(item);
                let pv = self.take(Self::payload(&Self::payload(&Place::local(o))), item);
                self.assign(Place::local(v), Rvalue::Use(pv));
                k(self, v, item)?;
                self.goto(go);
                self.cur = go;
                self.each(&f(0), a[0], k)?;
                self.goto(done);
                self.cur = done;
                Ok(())
            }
            K::SkipWhile => {
                let done = self.block();
                let go = self.block();
                let (flagged, open) = self.branch(Operand::Copy(f(1)));
                self.cur = flagged;
                self.goto(go);
                self.cur = open;
                let opt = self.body.tys.mk_option(item);
                let t = self.local(opt);
                self.next(itp.clone(), ty, Place::local(t), false)?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = n;
                self.goto(done);
                self.cur = s;
                let v = self.local(item);
                let pv = self.take(Self::payload(&Place::local(t)), item);
                self.assign(Place::local(v), Rvalue::Use(pv));
                k(self, v, item)?;
                self.goto(go);
                self.cur = go;
                self.each(&f(0), a[0], k)?;
                self.goto(done);
                self.cur = done;
                Ok(())
            }
            K::Skip => {
                use crate::ast::BinOp::*;
                let done = self.block();
                let go = self.block();
                let c = self.cmp(Lt, Self::usize_c(0), Operand::Copy(f(1)));
                let (skip, plain) = self.branch(c);
                self.cur = plain;
                self.goto(go);
                self.cur = skip;
                let n1 = self.local(USIZE);
                self.assign(Place::local(n1), Rvalue::Bin(Sub, Operand::Copy(f(1)), Self::usize_c(1)));
                let opt = self.body.tys.mk_option(item);
                let t = self.local(opt);
                self.nth(f(0), a[0], n1, Place::local(t))?;
                let (s, n) = self.switch_opt(&Place::local(t));
                self.cur = n;
                self.goto(done);
                self.cur = s;
                self.drop_local(t);
                self.goto(go);
                self.cur = go;
                self.each(&f(0), a[0], k)?;
                self.goto(done);
                self.cur = done;
                Ok(())
            }
            K::Chain => {
                // `a.fold` then `b.fold`: each side is consumed (and
                // dropped) when its fold returns.
                for side in [0u32, 1] {
                    let next_side = self.block();
                    let (s, n) = self.switch_opt(&f(side));
                    self.cur = n;
                    self.goto(next_side);
                    self.cur = s;
                    self.each(&Self::payload(&f(side)), a[side as usize], k)?;
                    let sty = self.place_ty(&f(side))?;
                    self.none(&f(side), sty);
                    self.goto(next_side);
                    self.cur = next_side;
                }
                Ok(())
            }
            K::Zip => {
                // `SpecFold` for two `TrustedLen` sides: `upper` pairs
                // per round, no `None` checks, then stop unless the
                // upper bound was unknown.
                let (ia, ib) = (self.item(a[0])?, self.item(a[1])?);
                let round = self.block();
                self.goto(round);
                self.cur = round;
                let (_, hi) = self.hint(itp.clone(), ty)?;
                let (upper, more) = (self.local(USIZE), self.local(BOOL));
                let (known, unknown) = self.switch_opt(&Place::local(hi));
                let go = self.block();
                self.cur = known;
                self.assign(Place::local(upper), Rvalue::Use(Operand::Copy(Self::payload(&Place::local(hi)))));
                self.assign(Place::local(more), Rvalue::Use(Operand::Const(Const::Bool(false))));
                self.goto(go);
                self.cur = unknown;
                self.assign(Place::local(upper), Rvalue::Use(Self::usize_c(u64::MAX)));
                self.assign(Place::local(more), Rvalue::Use(Operand::Const(Const::Bool(true))));
                self.goto(go);
                self.cur = go;
                let i = self.local(USIZE);
                self.assign(Place::local(i), Rvalue::Use(Self::usize_c(0)));
                let lp = self.block();
                self.goto(lp);
                self.cur = lp;
                let c = self.cmp(crate::ast::BinOp::Lt, Operand::Copy(Place::local(i)), Operand::Copy(Place::local(upper)));
                let (body, end) = self.branch(c);
                self.cur = body;
                self.assign(Place::local(i), Rvalue::Bin(crate::ast::BinOp::Add, Operand::Copy(Place::local(i)), Self::usize_c(1)));
                let (oa, ob) = (self.body.tys.mk_option(ia), self.body.tys.mk_option(ib));
                let (ta, tb) = (self.local(oa), self.local(ob));
                self.next(f(0), a[0], Place::local(ta), false)?;
                self.next(f(1), a[1], Place::local(tb), false)?;
                let px = self.take(Self::payload(&Place::local(ta)), ia);
                let py = self.take(Self::payload(&Place::local(tb)), ib);
                let tup = self.local(item);
                self.assign(Place::local(tup), Rvalue::TupleAgg(item, vec![px, py]));
                k(self, tup, item)?;
                self.goto(lp);
                self.cur = end;
                let fin = self.block();
                let (again, stop) = self.branch(Operand::Copy(Place::local(more)));
                self.cur = again;
                self.goto(round);
                self.cur = stop;
                self.goto(fin);
                self.cur = fin;
                Ok(())
            }
            _ => Err("iterator expansion: fold path for this kind".into()),
        }
    }

    /// True when `fold` over this type pulls differently from a `next`
    /// loop (see `each`).
    fn fold_differs(&mut self, ty: Ty) -> bool {
        use IterKind as K;
        let Some((k, a)) = self.kind_args(ty) else { return false };
        match k {
            // Two `TrustedLen` sides (`SpecFold`), or random-access sides
            // in the `NoCoerce` form only (an indexed `fold` over the
            // `min` length); both fold exactly the hint's upper pairs.
            K::Zip => {
                (self.trusted_len(a[0]) && self.trusted_len(a[1]) || self.tra(a[0]) && self.tra(a[1]))
                    && !(self.tra_coerce(a[0]) && self.tra_coerce(a[1]))
            }
            K::Map | K::Filter | K::FilterMap | K::Inspect | K::Copied | K::Cloned | K::Enumerate | K::Peekable | K::SkipWhile | K::Skip => {
                self.fold_differs(a[0])
            }
            K::Chain => self.fold_differs(a[0]) || self.fold_differs(a[1]),
            _ => false,
        }
    }

    /// `dest = itp.count()`, with Rust 1.99's per-kind overrides:
    /// the O(1) range forms (with the `count overflowed usize`
    /// panic) and the delegating adapters. Other kinds count by
    /// internal iteration, as the default `fold` does.
    fn count(&mut self, itp: Place, ty: Ty, dest: Place) -> R {
        use crate::ast::BinOp::*;
        use IterKind as K;
        if self.is_char_range(ty) {
            return self.char_range_count(itp, ty, dest);
        }
        let Some((k, a)) = self.kind_args(ty) else {
            return self.count_loop(itp, ty, dest);
        };
        let join = self.block();
        let f = |i: u32| itp.project(Proj::Field(i));
        match k {
            K::Range => {
                let (w, _) = self.wide_ty(a[0])?;
                let c = self.cmp(Lt, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (go, no) = self.branch(c);
                self.cur = no;
                self.assign(dest.clone(), Rvalue::Use(Self::usize_c(0)));
                self.goto(join);
                self.cur = go;
                let ws = self.cast_local(Operand::Copy(f(0)), w);
                let we = self.cast_local(Operand::Copy(f(1)), w);
                let steps = self.wide_bin(true, we, ws, w);
                let maxu = self.cast_local(Self::usize_c(u64::MAX), w);
                let over = self.cmp(Gt, Operand::Copy(Place::local(steps)), Operand::Copy(Place::local(maxu)));
                let (bad, good) = self.branch(over);
                self.cur = good;
                let cnt = self.cast_local(Operand::Copy(Place::local(steps)), USIZE);
                self.assign(dest, Rvalue::Use(Operand::Copy(Place::local(cnt))));
                self.goto(join);
                self.cur = bad;
                self.term(Terminator::Panic(vec![FmtPart::Lit("count overflowed usize".into())]));
                // `Step::steps_between(..).expect(..)` in core's range.rs.
                self.body.blocks[self.cur.0 as usize].term_span = crate::diag::Span::std_site(8, 1200, 59);
            }
            K::RangeInclusive => {
                let (w, _) = self.wide_ty(a[0])?;
                let zero = self.block();
                let (ex, live) = self.branch(Operand::Copy(f(2)));
                self.cur = ex;
                self.goto(zero);
                self.cur = live;
                let c = self.cmp(Le, Operand::Copy(f(0)), Operand::Copy(f(1)));
                let (go, empty) = self.branch(c);
                self.cur = empty;
                self.goto(zero);
                self.cur = go;
                let ws = self.cast_local(Operand::Copy(f(0)), w);
                let we = self.cast_local(Operand::Copy(f(1)), w);
                let steps = self.wide_bin(true, we, ws, w);
                let maxu = self.cast_local(Self::usize_c(u64::MAX), w);
                let over = self.cmp(Ge, Operand::Copy(Place::local(steps)), Operand::Copy(Place::local(maxu)));
                let (bad, good) = self.branch(over);
                self.cur = good;
                let cnt = self.cast_local(Operand::Copy(Place::local(steps)), USIZE);
                self.assign(dest.clone(), Rvalue::Bin(Add, Operand::Copy(Place::local(cnt)), Self::usize_c(1)));
                self.goto(join);
                self.cur = bad;
                self.term(Terminator::Panic(vec![FmtPart::Lit("count overflowed usize".into())]));
                self.body.blocks[self.cur.0 as usize].term_span = crate::diag::Span::std_site(8, 1560, 14);
                self.cur = zero;
                self.assign(dest.clone(), Rvalue::Use(Self::usize_c(0)));
                self.goto(join);
            }
            K::Skip => {
                // One inner `count` site for both paths (linear code in
                // nested `Skip`s, fx-cgen-ice).
                let rest = self.block();
                let c = self.cmp(Gt, Operand::Copy(f(1)), Self::usize_c(0));
                let (skip_b, plain) = self.branch(c);
                self.cur = plain;
                self.goto(rest);
                self.cur = skip_b;
                let item = self.item(ty)?;
                let opt = self.body.tys.mk_option(item);
                let m1 = self.local(USIZE);
                self.assign(Place::local(m1), Rvalue::Bin(Sub, Operand::Copy(f(1)), Self::usize_c(1)));
                let t = self.local(opt);
                self.nth(f(0), a[0], m1, Place::local(t))?;
                let (s, no) = self.switch_opt(&Place::local(t));
                self.cur = no;
                self.assign(dest.clone(), Rvalue::Use(Self::usize_c(0)));
                self.goto(join);
                self.cur = s;
                self.drop_local(t);
                self.goto(rest);
                self.cur = rest;
                self.count(f(0), a[0], dest.clone())?;
                self.goto(join);
            }
            K::Take => {
                let z = self.cmp(Eq, Operand::Copy(f(1)), Self::usize_c(0));
                let (zero, go) = self.branch(z);
                self.cur = zero;
                self.assign(dest.clone(), Rvalue::Use(Self::usize_c(0)));
                self.goto(join);
                self.cur = go;
                let budget = self.copy_local(Operand::Copy(f(1)), USIZE);
                let rem = self.advance(f(0), a[0], budget)?;
                self.assign(dest, Rvalue::Bin(Sub, Operand::Copy(Place::local(budget)), Operand::Copy(Place::local(rem))));
                self.goto(join);
            }
            K::Enumerate | K::Copied => {
                self.count(f(0), a[0], dest)?;
                self.goto(join);
            }
            K::Peekable => {
                let item = self.item(ty)?;
                let iopt = self.body.tys.mk_option(item);
                let slot = f(1);
                let pty = self.place_ty(&slot)?;
                // One inner `count` site for both paths (linear code in
                // nested `Peekable`s, fx-cgen-ice). The peeked item, held
                // in `held`, counts once and drops after the inner count,
                // as in Rust.
                let held = self.local(iopt);
                self.none(&Place::local(held), iopt);
                let extra = self.local(USIZE);
                self.assign(Place::local(extra), Rvalue::Use(Self::usize_c(0)));
                let site = self.block();
                let (full, empty) = self.switch_opt(&slot);
                self.cur = empty;
                self.goto(site);
                self.cur = full;
                let inner = Self::payload(&slot);
                let (some, spent) = self.switch_opt(&inner);
                self.cur = spent;
                self.assign(dest.clone(), Rvalue::Use(Self::usize_c(0)));
                self.goto(join);
                self.cur = some;
                let o = self.local(pty);
                self.take_none(slot.clone(), pty, Place::local(o));
                let pv = self.take(Self::payload(&Self::payload(&Place::local(o))), item);
                self.some(&Place::local(held), iopt, pv);
                self.assign(Place::local(extra), Rvalue::Use(Self::usize_c(1)));
                self.goto(site);
                self.cur = site;
                let cnt = self.local(USIZE);
                self.count(f(0), a[0], Place::local(cnt))?;
                self.drop_local(held);
                self.assign(dest, Rvalue::Bin(Add, Operand::Copy(Place::local(cnt)), Operand::Copy(Place::local(extra))));
                self.goto(join);
            }
            K::Chain => {
                let (ca, cb) = (self.local(USIZE), self.local(USIZE));
                for (side, out) in [(0u32, ca), (1u32, cb)] {
                    let nxt = self.block();
                    let (s, no) = self.switch_opt(&f(side));
                    self.cur = no;
                    self.assign(Place::local(out), Rvalue::Use(Self::usize_c(0)));
                    self.goto(nxt);
                    self.cur = s;
                    self.count(Self::payload(&f(side)), a[side as usize], Place::local(out))?;
                    let sty = self.place_ty(&f(side))?;
                    self.none(&f(side), sty);
                    self.goto(nxt);
                    self.cur = nxt;
                }
                self.assign(dest, Rvalue::Bin(Add, Operand::Copy(Place::local(ca)), Operand::Copy(Place::local(cb))));
                self.goto(join);
            }
            // core's slice `Iter::count` and alloc's `vec::IntoIter::count`
            // are the length (no walk, so a zero-sized element costs nothing
            // for any length). An IntoIter whose elements need a drop keeps
            // the loop: it drops them in the same order.
            K::SliceIter | K::SliceIterMut => {
                let n = self.size(itp, ty)?;
                self.assign(dest, Rvalue::Use(n));
                self.goto(join);
            }
            K::VecIntoIter if !crate::check::collect::needs_drop(self.p, &self.body.tys, a[0]) => {
                let r = self.ref_to(false, itp, ty);
                self.call_builtin(Builtin::VecIterLen, vec![Operand::Move(Place::local(r))], dest);
                self.goto(join);
            }
            // core's `RepeatN::count` is its length (no clones); the
            // element drops with the iterator.
            K::RepeatN => {
                self.assign(dest, Rvalue::Use(Operand::Copy(itp.project(Proj::Field(1)))));
                self.goto(join);
            }
            _ => {
                self.count_loop(itp, ty, dest)?;
                self.goto(join);
            }
        }
        self.cur = join;
        Ok(())
    }

    /// The default `count`: internal iteration, one per item.
    fn count_loop(&mut self, itp: Place, ty: Ty, dest: Place) -> R {
        let c = self.local(USIZE);
        self.assign(Place::local(c), Rvalue::Use(Self::usize_c(0)));
        self.each(&itp, ty, &mut |this, x, _| {
            this.drop_local(x);
            this.assign(Place::local(c), Rvalue::Bin(crate::ast::BinOp::Add, Operand::Copy(Place::local(c)), Self::usize_c(1)));
            Ok(())
        })?;
        self.assign(dest, Rvalue::Use(Operand::Copy(Place::local(c))));
        Ok(())
    }

    /// `dest = itp.last()`, with Rust 1.99's per-kind overrides: the
    /// ranges answer with `next_back`, and `Skip`, `Copied`,
    /// `Peekable`, and `Chain` delegate. Other kinds take the
    /// default internal iteration.
    fn last(&mut self, itp: Place, ty: Ty, dest: Place, dest_ty: Ty) -> R {
        use crate::ast::BinOp::*;
        use IterKind as K;
        let Some((k, a)) = self.kind_args(ty) else {
            return self.last_loop(itp, ty, dest, dest_ty);
        };
        let join = self.block();
        let f = |i: u32| itp.project(Proj::Field(i));
        match k {
            // core's `ChunkBy::last` is `next_back` too (R13).
            K::Range | K::RangeInclusive | K::ChunkBy | K::ChunkByMut => {
                self.next(itp, ty, dest.clone(), true)?;
                self.goto(join);
            }
            // core's `RepeatN::last` takes the element (no clones).
            K::RepeatN => {
                self.take_none(f(0), dest_ty, dest.clone());
                self.goto(join);
            }
            // alloc's `vec::IntoIter::last` is `next_back`; the rest then
            // drops with the iterator. With no element drop to run, the rest
            // needs no walk (a zero-sized element costs nothing for any
            // length). Drop elements keep the loop: it drops them in the
            // same order.
            K::VecIntoIter if !crate::check::collect::needs_drop(self.p, &self.body.tys, a[0]) => {
                self.next(itp, ty, dest.clone(), true)?;
                self.goto(join);
            }
            // core's `FlattenCompat::last`: `iter_fold(None, |last, it|
            // it.last().or(last))` over the front iterator, each outer
            // item's `IntoIter`, then the back iterator. Each inner
            // iterator is consumed (and dropped) by its own `last`; a
            // `Some` then replaces the running answer, which drops the
            // older item after the newer inner run.
            K::Flatten => {
                let u = a[1];
                let res = self.local(dest_ty);
                self.none(&Place::local(res), dest_ty);
                let fold = |this: &mut Self, inner: Operand| -> R {
                    let ul = this.local(u);
                    this.assign(Place::local(ul), Rvalue::Use(inner));
                    let t = this.local(dest_ty);
                    this.last(Place::local(ul), u, Place::local(t), dest_ty)?;
                    this.drop_local(ul);
                    let (s, n) = this.switch_opt(&Place::local(t));
                    let j = this.block();
                    this.cur = s;
                    this.assign(Place::local(res), Rvalue::Use(Operand::Move(Place::local(t))));
                    this.goto(j);
                    this.cur = n;
                    this.goto(j);
                    this.cur = j;
                    Ok(())
                };
                let ut = self.place_ty(&f(1))?;
                for side in [1u32, 0, 2] {
                    let (has, empty) = self.switch_opt(&f(side));
                    let next = self.block();
                    self.cur = empty;
                    self.goto(next);
                    self.cur = has;
                    if side == 0 {
                        self.each(&Self::payload(&f(0)), a[0], &mut |this, x, xt| {
                            let xv = this.take(Place::local(x), xt);
                            let uo = this.into_iter(xv, u)?;
                            fold(this, uo)
                        })?;
                        let ot = self.place_ty(&f(0))?;
                        self.none(&f(0), ot);
                    } else {
                        let o = self.local(ut);
                        self.take_none(f(side), ut, Place::local(o));
                        let inner = self.take(Self::payload(&Place::local(o)), u);
                        fold(self, inner)?;
                    }
                    self.goto(next);
                    self.cur = next;
                }
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(res))));
                self.goto(join);
            }
            K::Skip => {
                // One inner `last` site for both paths (linear code in
                // nested `Skip`s, fx-cgen-ice).
                let rest = self.block();
                let c = self.cmp(Gt, Operand::Copy(f(1)), Self::usize_c(0));
                let (skip_b, plain) = self.branch(c);
                self.cur = plain;
                self.goto(rest);
                self.cur = skip_b;
                let item = self.item(ty)?;
                let opt = self.body.tys.mk_option(item);
                let m1 = self.local(USIZE);
                self.assign(Place::local(m1), Rvalue::Bin(Sub, Operand::Copy(f(1)), Self::usize_c(1)));
                let t = self.local(opt);
                self.nth(f(0), a[0], m1, Place::local(t))?;
                let (s, no) = self.switch_opt(&Place::local(t));
                self.cur = no;
                self.none(&dest, dest_ty);
                self.goto(join);
                self.cur = s;
                self.drop_local(t);
                self.goto(rest);
                self.cur = rest;
                self.last(f(0), a[0], dest.clone(), dest_ty)?;
                self.goto(join);
            }
            K::Copied => {
                let ii = self.item(a[0])?;
                let iopt = self.body.tys.mk_option(ii);
                let t = self.local(iopt);
                self.last(f(0), a[0], Place::local(t), iopt)?;
                let (s, no) = self.switch_opt(&Place::local(t));
                self.cur = s;
                self.some(&dest, dest_ty, Operand::Copy(Self::payload(&Place::local(t)).deref()));
                self.goto(join);
                self.cur = no;
                self.none(&dest, dest_ty);
                self.goto(join);
            }
            K::Peekable => {
                let item = self.item(ty)?;
                let slot = f(1);
                let pty = self.place_ty(&slot)?;
                let held = self.local(dest_ty);
                let (full, empty) = self.switch_opt(&slot);
                let go = self.block();
                self.cur = empty;
                self.none(&Place::local(held), dest_ty);
                self.goto(go);
                self.cur = full;
                let inner = Self::payload(&slot);
                let (some, spent) = self.switch_opt(&inner);
                self.cur = spent;
                self.none(&dest, dest_ty);
                self.goto(join);
                self.cur = some;
                let o = self.local(pty);
                self.take_none(slot.clone(), pty, Place::local(o));
                let v = self.local(item);
                let pv = self.take(Self::payload(&Self::payload(&Place::local(o))), item);
                self.assign(Place::local(v), Rvalue::Use(pv));
                let av = self.take(Place::local(v), item);
                self.some(&Place::local(held), dest_ty, av);
                self.goto(go);
                self.cur = go;
                let t = self.local(dest_ty);
                self.last(f(0), a[0], Place::local(t), dest_ty)?;
                let (s, no) = self.switch_opt(&Place::local(t));
                self.cur = s;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(t))));
                self.drop_local(held);
                self.goto(join);
                self.cur = no;
                self.assign(dest, Rvalue::Use(Operand::Move(Place::local(held))));
                self.goto(join);
            }
            K::Chain => {
                // Both sides run, a first; b's last wins.
                let la = self.local(dest_ty);
                let (asome, anone) = self.switch_opt(&f(0));
                let bside = self.block();
                self.cur = anone;
                self.none(&Place::local(la), dest_ty);
                self.goto(bside);
                self.cur = asome;
                self.last(Self::payload(&f(0)), a[0], Place::local(la), dest_ty)?;
                let aty = self.place_ty(&f(0))?;
                self.none(&f(0), aty);
                self.goto(bside);
                self.cur = bside;
                let (bsome, bnone) = self.switch_opt(&f(1));
                self.cur = bnone;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(la))));
                self.goto(join);
                self.cur = bsome;
                let lb = self.local(dest_ty);
                self.last(Self::payload(&f(1)), a[1], Place::local(lb), dest_ty)?;
                let bty = self.place_ty(&f(1))?;
                self.none(&f(1), bty);
                let (s, no) = self.switch_opt(&Place::local(lb));
                self.cur = s;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(lb))));
                self.drop_local(la);
                self.goto(join);
                self.cur = no;
                self.assign(dest, Rvalue::Use(Operand::Move(Place::local(la))));
                self.goto(join);
            }
            _ => {
                self.last_loop(itp, ty, dest, dest_ty)?;
                self.goto(join);
            }
        }
        self.cur = join;
        Ok(())
    }

    /// The default `last`: internal iteration keeping the newest item.
    fn last_loop(&mut self, itp: Place, ty: Ty, dest: Place, dest_ty: Ty) -> R {
        let l = self.local(dest_ty);
        self.none(&Place::local(l), dest_ty);
        self.each(&itp, ty, &mut |this, x, item| {
            let ax = this.take(Place::local(x), item);
            this.some(&Place::local(l), dest_ty, ax);
            Ok(())
        })?;
        self.assign(dest, Rvalue::Use(Operand::Move(Place::local(l))));
        Ok(())
    }

    fn for_each(&mut self, itp: Place, ty: Ty, fpl: Place, fty: Ty) -> R {
        self.each(&itp, ty, &mut |this, x, item| {
            let ax = this.take(Place::local(x), item);
            let u = this.local(UNIT);
            this.call_fn(fty, fpl.clone(), vec![ax], Place::local(u))
        })
    }

    /// `partition(f)` (with `f`) and `unzip()` into `(Vec<A>, Vec<B>)`, as
    /// core 1.99: two empty Vecs, then one fold that pushes each item to
    /// the side `f(&x)` picks, or each pair's halves to both. `unzip`
    /// first reserves the hint's lower bound in both when it is not 0
    /// (the tuple's `extend_reserve`).
    fn partition_unzip(&mut self, itp: Place, ty: Ty, f: Option<(Local, Ty)>, dest: Place, dest_ty: Ty) -> R {
        let TyKind::Tuple(ts) = self.body.tys.kind(dest_ty) else { return Err("iterator expansion: partition into a non-pair".into()) };
        let (da, db) = {
            let v = self.body.tys.tys_of(ts);
            (v[0], v[1])
        };
        // A `VecDeque` side fills a Vec and wraps it at the end (head 0):
        // core's `extend_one` is its `push_back`, which grows by the Vec
        // rule and keeps the head at 0 from empty.
        let deque_of = |this: &mut Self, t: Ty| -> Option<(AdtId, Ty)> {
            let a = this.body.tys.local_adt(t).filter(|&a| this.p.is_vec_deque_adt(a))?;
            let e = this.body.tys.adt_first_ty_arg(t)?;
            Some((a, this.body.tys.mk_vec(e)))
        };
        let (qa, qb) = (deque_of(self, da), deque_of(self, db));
        let (va, vb) = (qa.map_or(da, |q| q.1), qb.map_or(db, |q| q.1));
        let (Some(ea), Some(eb)) = (self.body.tys.vec_elem(va), self.body.tys.vec_elem(vb)) else {
            return Err("iterator expansion: partition into non-Vecs".into());
        };
        let (a, b) = (self.local(va), self.local(vb));
        self.assign(Place::local(a), Rvalue::VecLit(ea, Vec::new()));
        self.assign(Place::local(b), Rvalue::VecLit(eb, Vec::new()));
        let push = |this: &mut Self, v: Local, vt: Ty, x: Operand| {
            let rv = this.ref_to(true, Place::local(v), vt);
            let u = this.local(UNIT);
            this.call_builtin(Builtin::VecPush, vec![Operand::Move(Place::local(rv)), x], Place::local(u));
        };
        // An item of type `have` for a side of element `want`: the item itself, or a copy
        // through it when it is `&want` (`Vec<T>: Extend<&T>`, check `extends_by_copy`).
        let item_for = |this: &mut Self, pl: Place, have: Ty, want: Ty| -> Operand {
            if have != want && matches!(this.body.tys.kind(have), TyKind::Ref(_, _, inner) if inner == want) {
                Operand::Copy(pl.deref())
            } else {
                this.take(pl, want)
            }
        };
        if f.is_none() {
            let (lo, _) = self.hint(itp.clone(), ty)?;
            let some = self.cmp(crate::ast::BinOp::Gt, Operand::Copy(Place::local(lo)), Self::usize_c(0));
            let (yes, no) = self.branch(some);
            let join = self.block();
            self.cur = yes;
            for (v, vt) in [(a, va), (b, vb)] {
                let rv = self.ref_to(true, Place::local(v), vt);
                let u = self.local(UNIT);
                self.call_builtin(Builtin::VecReserve, vec![Operand::Move(Place::local(rv)), Operand::Copy(Place::local(lo))], Place::local(u));
            }
            self.goto(join);
            self.cur = no;
            self.goto(join);
            self.cur = join;
        }
        self.each(&itp, ty, &mut |this, x, item| {
            match f {
                Some((fl, fty)) => {
                    let rx = this.ref_to(false, Place::local(x), item);
                    let r = this.local(BOOL);
                    this.call_fn(fty, Place::local(fl), vec![Operand::Move(Place::local(rx))], Place::local(r))?;
                    let (yes, no) = this.branch(Operand::Copy(Place::local(r)));
                    let join = this.block();
                    this.cur = yes;
                    let ax = item_for(this, Place::local(x), item, ea);
                    push(this, a, va, ax);
                    this.goto(join);
                    this.cur = no;
                    let ax = item_for(this, Place::local(x), item, eb);
                    push(this, b, vb, ax);
                    this.goto(join);
                    this.cur = join;
                }
                None => {
                    let parts = match this.body.tys.kind(item) {
                        TyKind::Tuple(ts) => this.body.tys.tys_of(ts).to_vec(),
                        _ => vec![ea, eb],
                    };
                    let x0 = item_for(this, Place::local(x).project(Proj::Field(0)), parts[0], ea);
                    push(this, a, va, x0);
                    let x1 = item_for(this, Place::local(x).project(Proj::Field(1)), parts[1], eb);
                    push(this, b, vb, x1);
                }
            }
            Ok(())
        })?;
        let mut side = |this: &mut Self, v: Local, vt: Ty, q: Option<(AdtId, Ty)>, dt: Ty| -> Operand {
            let m = this.take(Place::local(v), vt);
            let Some((adt, _)) = q else { return m };
            let d = this.local(dt);
            this.assign(Place::local(d), Rvalue::Aggregate(adt, 0, vec![m]));
            this.take(Place::local(d), dt)
        };
        let (ma, mb) = (side(self, a, va, qa, da), side(self, b, vb, qb, db));
        self.assign(dest, Rvalue::TupleAgg(dest_ty, vec![ma, mb]));
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn fold(&mut self, itp: Place, ty: Ty, init: Operand, fpl: Place, fty: Ty, dest: Place, dest_ty: Ty) -> R {
        let acc = self.local(dest_ty);
        self.assign(Place::local(acc), Rvalue::Use(init));
        self.each(&itp, ty, &mut |this, x, item| {
            let aa = this.take(Place::local(acc), dest_ty);
            let ax = this.take(Place::local(x), item);
            let next = this.local(dest_ty);
            this.call_fn(fty, fpl.clone(), vec![aa, ax], Place::local(next))?;
            let an = this.take(Place::local(next), dest_ty);
            this.assign(Place::local(acc), Rvalue::Use(an));
            Ok(())
        })?;
        let aa = self.take(Place::local(acc), dest_ty);
        self.assign(dest, Rvalue::Use(aa));
        Ok(())
    }

    /// `dest = itp.try_fold(init, f)` for an `Option` or `Result` result:
    /// each `Some`/`Ok` payload is the next accumulator, the first
    /// `None`/`Err` is the result as it is (the rest stays in the
    /// iterator), and the end wraps the accumulator. The pulls are std's
    /// `try_fold` steps, as in `search`.
    #[allow(clippy::too_many_arguments)]
    fn try_fold(&mut self, itp: Place, ty: Ty, init: Operand, fpl: Place, fty: Ty, dest: Place, dest_ty: Ty) -> R {
        // `core::ops::ControlFlow<B, C>` (std source): the accumulator is
        // `C`, and `Continue` is variant 0.
        let flow = self.body.tys.local_adt(dest_ty).filter(|&a| self.p.is_control_flow_adt(a));
        let (acc_ty, is_res) = match (self.body.tys.option_elem(dest_ty), flow) {
            (Some(t), _) => (t, false),
            (None, Some(_)) => {
                let c = self.body.tys.adt_parts(dest_ty).and_then(|(_, a)| self.body.tys.args(a).get(1).and_then(|g| g.as_ty()));
                (c.ok_or("iterator expansion: `try_fold` into a ControlFlow without its `C`")?, true)
            }
            (None, None) => (self.body.tys.result_args(dest_ty).ok_or("iterator expansion: `try_fold` result is not an Option or a Result")?.0, true),
        };
        // `Some` is discriminant 1, `Ok` and `Continue` 0; the payload is field 0.
        let (go_d, go_v) = if is_res { (0, 0) } else { (1, 1) };
        let acc = self.local(acc_ty);
        self.assign(Place::local(acc), Rvalue::Use(init));
        let join = self.block();
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        let saved = std::mem::replace(&mut self.fold, true);
        let pulled = self.pull(&itp, ty);
        self.fold = saved;
        let (_, n, x, item) = pulled?;
        let aa = self.take(Place::local(acc), acc_ty);
        let ax = self.take(Place::local(x), item);
        let r = self.local(dest_ty);
        self.call_fn(fty, fpl, vec![aa, ax], Place::local(r))?;
        let d = self.local(int(IntTy::U32));
        self.assign(Place::local(d), Rvalue::Discriminant(Place::local(r)));
        let (go, stop) = (self.block(), self.block());
        self.term(Terminator::Switch(Operand::Copy(Place::local(d)), vec![(go_d, go)], stop));
        self.cur = go;
        let v = self.take(Place::local(r).project(Proj::Downcast(go_v)).project(Proj::Field(0)), acc_ty);
        self.assign(Place::local(acc), Rvalue::Use(v));
        self.goto(lp);
        self.cur = stop;
        self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(r))));
        self.goto(join);
        self.cur = n;
        let aa = self.take(Place::local(acc), acc_ty);
        if let Some(adt) = flow {
            self.assign(dest, Rvalue::Aggregate(adt, 0, vec![aa]));
        } else if is_res {
            self.assign(dest, Rvalue::Res(dest_ty, true, aa));
        } else {
            self.some(&dest, dest_ty, aa);
        }
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// `any`, `all`, `find`, `find_map`, and `position`: pull until the
    /// closure decides, then stop (the rest stays in the iterator). The
    /// pulls are std's `try_fold` steps, so a Take's count drops only per
    /// item its inner yields.
    #[allow(clippy::too_many_arguments)]
    fn search(&mut self, b: Builtin, itp: Place, ty: Ty, fpl: Place, fty: Ty, dest: Place, dest_ty: Ty) -> R {
        use Builtin as B;
        let join = self.block();
        let pos = self.local(USIZE);
        self.assign(Place::local(pos), Rvalue::Use(Self::usize_c(0)));
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        // std runs these through `try_fold` (see `Ex::fold`).
        let saved = std::mem::replace(&mut self.fold, true);
        let pulled = self.pull(&itp, ty);
        self.fold = saved;
        let (_, n, x, item) = pulled?;
        match b {
            B::IterAny | B::IterAll => {
                let ax = self.take(Place::local(x), item);
                let r = self.local(BOOL);
                self.call_fn(fty, fpl, vec![ax], Place::local(r))?;
                let (yes, no) = self.branch(Operand::Copy(Place::local(r)));
                let (stop, go) = if b == B::IterAny { (yes, no) } else { (no, yes) };
                self.cur = stop;
                self.assign(dest.clone(), Rvalue::Use(Operand::Const(Const::Bool(b == B::IterAny))));
                self.goto(join);
                self.cur = go;
                self.goto(lp);
                self.cur = n;
                self.assign(dest, Rvalue::Use(Operand::Const(Const::Bool(b == B::IterAll))));
            }
            B::IterFind => {
                let rx = self.ref_to(false, Place::local(x), item);
                let r = self.local(BOOL);
                self.call_fn(fty, fpl, vec![Operand::Move(Place::local(rx))], Place::local(r))?;
                let (yes, no) = self.branch(Operand::Copy(Place::local(r)));
                self.cur = yes;
                let ax = self.take(Place::local(x), item);
                self.some(&dest, dest_ty, ax);
                self.goto(join);
                self.cur = no;
                self.drop_local(x);
                self.goto(lp);
                self.cur = n;
                self.none(&dest, dest_ty);
            }
            B::IterFindMap => {
                let ax = self.take(Place::local(x), item);
                let o = self.local(dest_ty);
                self.call_fn(fty, fpl, vec![ax], Place::local(o))?;
                let (hit, miss) = self.switch_opt(&Place::local(o));
                self.cur = hit;
                self.assign(dest.clone(), Rvalue::Use(Operand::Move(Place::local(o))));
                self.goto(join);
                self.cur = miss;
                self.goto(lp);
                self.cur = n;
                self.none(&dest, dest_ty);
            }
            _ => {
                let ax = self.take(Place::local(x), item);
                let r = self.local(BOOL);
                self.call_fn(fty, fpl, vec![ax], Place::local(r))?;
                let (yes, no) = self.branch(Operand::Copy(Place::local(r)));
                self.cur = yes;
                self.some(&dest, dest_ty, Operand::Copy(Place::local(pos)));
                self.goto(join);
                self.cur = no;
                self.assign(Place::local(pos), Rvalue::Bin(crate::ast::BinOp::Add, Operand::Copy(Place::local(pos)), Self::usize_c(1)));
                self.goto(lp);
                self.cur = n;
                self.none(&dest, dest_ty);
            }
        }
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// A `Flatten` side (front or back) iterator's hint: its own, or
    /// `(0, Some(0))` when the slot is empty (W-STD-B).
    fn flat_side_hint(&mut self, slot: Place, u: Ty) -> Result<(Local, Local), String> {
        let ou = self.body.tys.mk_option(USIZE);
        let (lo, hi) = (self.local(USIZE), self.local(ou));
        let (s, n) = self.switch_opt(&slot);
        let join = self.block();
        self.cur = s;
        let (l, h) = self.hint(Self::payload(&slot), u)?;
        self.assign(Place::local(lo), Rvalue::Use(Operand::Copy(Place::local(l))));
        self.assign(Place::local(hi), Rvalue::Use(Operand::Move(Place::local(h))));
        self.goto(join);
        self.cur = n;
        self.assign(Place::local(lo), Rvalue::Use(Self::usize_c(0)));
        self.some(&Place::local(hi), ou, Self::usize_c(0));
        self.goto(join);
        self.cur = join;
        Ok((lo, hi))
    }

    /// True when Rust 1.99 implements FusedIterator for the type: every
    /// std iterator lust has, and adapters over fused ones; not a user
    /// iterator (`ByNext`).
    fn fused(&mut self, t: Ty) -> bool {
        match self.kind_args(t) {
            None => true,
            // core: `impl<I: FusedIterator + ?Sized> FusedIterator for &mut I`.
            Some((IterKind::ByNext, a)) => self.by_mut_builtin(a[0]).is_some_and(|inner| self.fused(inner)),
            Some((_, a)) => a.iter().all(|&x| self.kind_args(x).is_none() || self.fused(x)),
        }
    }

    /// `const_size` of an iterator type's item, read from the kind's
    /// args (no interning).
    fn item_const_size(&self, t: Ty) -> Option<u64> {
        use IterKind as K;
        let (k, a) = self.kind_args(t)?;
        match k {
            K::SliceIter | K::SliceIterMut | K::VecIntoIter | K::ArrayIntoIter | K::RepeatN | K::OptionIntoIter => self.const_size(a[0]),
            K::Map | K::FilterMap | K::MapWhile => self.const_size(a[2]),
            K::Copied | K::Cloned | K::ByNext => self.const_size(a[1]),
            K::Filter | K::Rev | K::Take | K::Skip | K::Chain | K::TakeWhile | K::SkipWhile | K::StepBy | K::Peekable | K::Inspect => {
                self.item_const_size(a[0])
            }
            K::Flatten => self.item_const_size(a[1]),
            _ => None,
        }
    }

    /// The fixed length of an array item, `&[T; N]`, or `&mut [T; N]`
    /// (std's ConstSizeIntoIterator), for `Flatten`'s size_hint.
    fn const_size(&self, t: Ty) -> Option<u64> {
        let t = match self.body.tys.kind(t) {
            TyKind::Ref(_, _, inner) => inner,
            _ => t,
        };
        match self.body.tys.kind(t) {
            TyKind::Array(_, c) => match self.body.tys.const_kind(c) {
                ConstKind::Int(n) => Some(n as u64),
                _ => None,
            },
            _ => None,
        }
    }

    /// `rposition` (W-STD-B): the index counts down from the exact
    /// length while `next_back` pulls, as Rust's slice iterator does.
    fn rposition(&mut self, itp: Place, ty: Ty, fpl: Place, fty: Ty, dest: Place, dest_ty: Ty) -> R {
        use crate::ast::BinOp::Sub;
        let join = self.block();
        let n = self.size(itp.clone(), ty)?;
        let pos = self.local(USIZE);
        self.assign(Place::local(pos), Rvalue::Use(n));
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        let item = self.item(ty)?;
        let opt = self.body.tys.mk_option(item);
        let t = self.local(opt);
        self.next(itp.clone(), ty, Place::local(t), true)?;
        let (s, none) = self.switch_opt(&Place::local(t));
        self.cur = s;
        let x = self.local(item);
        let px = self.take(Self::payload(&Place::local(t)), item);
        self.assign(Place::local(x), Rvalue::Use(px));
        self.assign(Place::local(pos), Rvalue::Bin(Sub, Operand::Copy(Place::local(pos)), Self::usize_c(1)));
        let ax = self.take(Place::local(x), item);
        let r = self.local(BOOL);
        self.call_fn(fty, fpl, vec![ax], Place::local(r))?;
        let (yes, no) = self.branch(Operand::Copy(Place::local(r)));
        self.cur = yes;
        self.some(&dest, dest_ty, Operand::Copy(Place::local(pos)));
        self.goto(join);
        self.cur = no;
        self.goto(lp);
        self.cur = none;
        self.none(&dest, dest_ty);
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// `sum` and `product`: a fold from 0 or 1 (`-0.0` and `1.0` for
    /// floats, as Rust 1.99 does), with checked arithmetic.
    fn sum(&mut self, product: bool, itp: Place, ty: Ty, dest: Place, dest_ty: Ty) -> R {
        if self.body.tys.option_elem(dest_ty).is_some() || self.body.tys.result_args(dest_ty).is_some() {
            return self.sum_try(product, itp, ty, dest, dest_ty);
        }
        let zero = self.sum_zero(product, dest_ty)?;
        let acc = self.local(dest_ty);
        self.assign(Place::local(acc), Rvalue::Use(Operand::Const(zero)));
        let op = if product { crate::ast::BinOp::Mul } else { crate::ast::BinOp::Add };
        self.each(&itp, ty, &mut |this, x, item| {
            let v = if matches!(this.body.tys.kind(item), TyKind::Ref(..)) { Place::local(x).deref() } else { Place::local(x) };
            this.sum_step(op, acc, v);
            Ok(())
        })?;
        self.assign(dest, Rvalue::Use(Operand::Copy(Place::local(acc))));
        Ok(())
    }

    /// `acc = acc op v`, where an overflow reports at core's
    /// `integer_sum_product!` line.
    fn sum_step(&mut self, op: crate::ast::BinOp, acc: Local, v: Place) {
        let at = std::mem::replace(&mut self.span, crate::diag::Span::std_site(7, 206, 1));
        self.assign(Place::local(acc), Rvalue::Bin(op, Operand::Copy(Place::local(acc)), Operand::Copy(v)));
        self.span = at;
    }

    /// `sum`/`product` into `Option<T>` or `Result<T, E>` (core's
    /// `try_process` over a `GenericShunt`): each `Some`/`Ok` payload adds
    /// in; the first `None` or `Err` stops the pull and is the result (the
    /// rest stays in the iterator); the end wraps the total. The pulls are
    /// std's `try_fold` steps, as in `search`.
    fn sum_try(&mut self, product: bool, itp: Place, ty: Ty, dest: Place, dest_ty: Ty) -> R {
        let (t, is_res) = match self.body.tys.option_elem(dest_ty) {
            Some(t) => (t, false),
            None => (self.body.tys.result_args(dest_ty).ok_or("iterator expansion: sum into a non-numeric type")?.0, true),
        };
        let zero = self.sum_zero(product, t)?;
        let acc = self.local(t);
        self.assign(Place::local(acc), Rvalue::Use(Operand::Const(zero)));
        let op = if product { crate::ast::BinOp::Mul } else { crate::ast::BinOp::Add };
        // `Some` is discriminant 1 and `Ok` 0; the payload is field 0.
        let (go_d, go_v) = if is_res { (0, 0) } else { (1, 1) };
        let join = self.block();
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        let saved = std::mem::replace(&mut self.fold, true);
        let pulled = self.pull(&itp, ty);
        self.fold = saved;
        let (_, n, x, item) = pulled?;
        let u = match self.body.tys.option_elem(item) {
            Some(u) => u,
            None => self.body.tys.result_args(item).ok_or("iterator expansion: sum of non-Option items")?.0,
        };
        let d = self.local(int(IntTy::U32));
        self.assign(Place::local(d), Rvalue::Discriminant(Place::local(x)));
        let (go, stop) = (self.block(), self.block());
        self.term(Terminator::Switch(Operand::Copy(Place::local(d)), vec![(go_d, go)], stop));
        self.cur = go;
        let payload = Place::local(x).project(Proj::Downcast(go_v)).project(Proj::Field(0));
        let v = if matches!(self.body.tys.kind(u), TyKind::Ref(..)) { payload.deref() } else { payload };
        self.sum_step(op, acc, v);
        self.drop_local(x);
        self.goto(lp);
        self.cur = stop;
        if is_res {
            let e = self.take(Place::local(x).project(Proj::Downcast(1)).project(Proj::Field(0)), self.body.tys.result_args(item).map_or(ERROR, |r| r.1));
            self.assign(dest.clone(), Rvalue::Res(dest_ty, false, e));
        } else {
            self.none(&dest, dest_ty);
        }
        self.goto(join);
        self.cur = n;
        if is_res {
            self.assign(dest, Rvalue::Res(dest_ty, true, Operand::Copy(Place::local(acc))));
        } else {
            self.some(&dest, dest_ty, Operand::Copy(Place::local(acc)));
        }
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// The start value of `sum` (0, or -0.0 for floats as core's
    /// `float_sum_product!`) or `product` (1) for the numeric type `t`.
    fn sum_zero(&self, product: bool, t: Ty) -> Result<Const, String> {
        Ok(match self.body.tys.kind(t) {
            TyKind::Int(i) => Const::Int(u128::from(product), i),
            TyKind::Float(fl) => {
                let v: f64 = if product { 1.0 } else { -0.0 };
                Const::Float(if fl == FloatTy::F32 { u64::from((v as f32).to_bits()) } else { v.to_bits() }, fl)
            }
            _ => return Err("iterator expansion: sum into a non-numeric type".into()),
        })
    }

    /// `Iterator::eq` (`ne` negates): core 1.99's `SpecIterEq`. Two
    /// `TrustedLen` sides whose upper bounds differ are unequal before
    /// any pull; else `iter_eq`: `a`'s `try_fold` steps, one `b.next()`
    /// per item (an end of `b` first is unequal, the item drops), the
    /// pair compared and dropped (`y`, then `x`), and at the end of `a`
    /// one more `b.next()` decides.
    #[allow(clippy::too_many_arguments)]
    fn iter_eq(&mut self, ap: Place, at: Ty, bp: Place, bt: Ty, dest: Place, ne: bool) -> R {
        use crate::ast::BinOp::Eq;
        let join = self.block();
        let result = |this: &mut Self, v: bool| {
            this.assign(dest.clone(), Rvalue::Use(Operand::Const(Const::Bool(v != ne))));
            this.goto(join);
        };
        if self.trusted_len(at) && self.trusted_len(bt) {
            let (_, ha) = self.hint(ap.clone(), at)?;
            let (_, hb) = self.hint(bp.clone(), bt)?;
            let go = self.block();
            let (sa, na) = self.switch_opt(&Place::local(ha));
            self.cur = sa;
            let (sb, nb) = self.switch_opt(&Place::local(hb));
            self.cur = sb;
            let c = self.cmp(Eq, Operand::Copy(Self::payload(&Place::local(ha))), Operand::Copy(Self::payload(&Place::local(hb))));
            let (same, diff) = self.branch(c);
            self.cur = same;
            self.goto(go);
            self.cur = diff;
            result(self, false);
            self.cur = nb;
            result(self, false);
            self.cur = na;
            let (sb2, nb2) = self.switch_opt(&Place::local(hb));
            self.cur = sb2;
            result(self, false);
            self.cur = nb2;
            self.goto(go);
            self.cur = go;
        }
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        let saved = std::mem::replace(&mut self.fold, true);
        let pulled = self.pull(&ap, at);
        self.fold = saved;
        let (_, a_end, x, xt) = pulled?;
        let (_, b_end, y, _) = self.pull(&bp, bt)?;
        let r = self.local(BOOL);
        self.item_eq(x, xt, y, r);
        self.drop_local(y);
        self.drop_local(x);
        let (yes, no) = self.branch(Operand::Copy(Place::local(r)));
        self.cur = yes;
        self.goto(lp);
        self.cur = no;
        result(self, false);
        self.cur = b_end;
        self.drop_local(x);
        result(self, false);
        self.cur = a_end;
        let (_, b_end2, y2, _) = self.pull(&bp, bt)?;
        self.drop_local(y2);
        result(self, false);
        self.cur = b_end2;
        result(self, true);
        self.cur = join;
        Ok(())
    }

    /// `r = x == y` for two items of type `t` (check took one type):
    /// through the references (`PartialEq for &A` compares the
    /// pointees), a `&str` by its bytes, anything else by the eq glue.
    fn item_eq(&mut self, x: Local, t: Ty, y: Local, r: Local) {
        let (mut px, mut py, mut t) = (Place::local(x), Place::local(y), t);
        while let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
            if inner == STR {
                self.assign(Place::local(r), Rvalue::StrCmp(crate::ast::BinOp::Eq, Operand::Copy(px), Operand::Copy(py)));
                return;
            }
            px = px.deref();
            py = py.deref();
            t = inner;
        }
        let ra = self.ref_to(false, px, t);
        let rb = self.ref_to(false, py, t);
        self.assign(Place::local(r), Rvalue::Eq { a: Operand::Move(Place::local(ra)), b: Operand::Move(Place::local(rb)), ty: t, ne: false });
    }

    /// `min`/`max` (key None) and `min_by_key`/`max_by_key`: Rust's
    /// `reduce` over `cmp::max_by`/`min_by`, so `max` keeps the last of
    /// equal items and `min` the first; the loser drops at once.
    #[allow(clippy::too_many_arguments)]
    fn min_max(&mut self, max: bool, itp: Place, ty: Ty, key: Option<(Place, Ty)>, dest: Place, dest_ty: Ty) -> R {
        let item = self.item(ty)?;
        if key.is_none() && matches!(self.kind_args(ty), Some((IterKind::Range | IterKind::RangeInclusive, _))) {
            // Rust's range `min` is `next`, its `max` is `next_back`.
            return self.next(itp, ty, dest, max);
        }
        let join = self.block();
        // `reduce`: the first item by `next`, the rest by `fold`.
        let (_, n, first, _) = self.pull(&itp, ty)?;
        let best = self.local(item);
        let a0 = self.take(Place::local(first), item);
        self.assign(Place::local(best), Rvalue::Use(a0));
        let key_ty = match &key {
            Some((fpl, fty)) => {
                let kt = self.closure_output(*fty)?;
                Some((fpl.clone(), *fty, kt))
            }
            None => None,
        };
        let best_key = match &key_ty {
            Some((fpl, fty, kt)) => {
                let k = self.local(*kt);
                let rb = self.ref_to(false, Place::local(best), item);
                self.call_fn(*fty, fpl.clone(), vec![Operand::Move(Place::local(rb))], Place::local(k))?;
                Some(k)
            }
            None => None,
        };
        self.each(&itp, ty, &mut |this, x, _| {
            let x_key = match &key_ty {
                Some((fpl, fty, kt)) => {
                    let k = this.local(*kt);
                    let rx = this.ref_to(false, Place::local(x), item);
                    this.call_fn(*fty, fpl.clone(), vec![Operand::Move(Place::local(rx))], Place::local(k))?;
                    Some(k)
                }
                None => None,
            };
            // `max_by(best, x)`: x wins unless best > x; `min_by`: x
            // wins only if best > x. The loser drops, key first.
            let (lhs, rhs, ct) = match (best_key, x_key, &key_ty) {
                (Some(bk), Some(xk), Some((_, _, kt))) => (Place::local(bk), Place::local(xk), *kt),
                _ => (Place::local(best), Place::local(x), item),
            };
            let gt = this.greater(lhs, rhs, ct)?;
            let (best_gt, best_le) = this.branch(gt);
            let (keep_best, take_x) = if max { (best_gt, best_le) } else { (best_le, best_gt) };
            let after = this.block();
            this.cur = keep_best;
            if let Some(xk) = x_key {
                this.drop_local(xk);
            }
            this.drop_local(x);
            this.goto(after);
            this.cur = take_x;
            if let (Some(bk), Some(xk)) = (best_key, x_key) {
                let kt = key_ty.as_ref().map(|k| k.2).unwrap_or(ERROR);
                this.drop_local(bk);
                let ak = this.take(Place::local(xk), kt);
                this.assign(Place::local(bk), Rvalue::Use(ak));
            }
            this.drop_local(best);
            let ax = this.take(Place::local(x), item);
            this.assign(Place::local(best), Rvalue::Use(ax));
            this.goto(after);
            this.cur = after;
            Ok(())
        })?;
        if let Some(bk) = best_key {
            self.drop_local(bk);
        }
        let ab = self.take(Place::local(best), item);
        self.some(&dest, dest_ty, ab);
        self.goto(join);
        self.cur = n;
        self.none(&dest, dest_ty);
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// The output type of a key fn type (`min_by_key`, `max_by_key`): a
    /// closure, a fn pointer, or a local fn item, as `call_fn` calls them.
    fn closure_output(&self, fty: Ty) -> Result<Ty, String> {
        match self.body.tys.kind(fty) {
            TyKind::Closure(def, _) => self.p.gx.closures.get(&def).map(|e| e.output).ok_or_else(|| "iterator expansion: closure not registered".into()),
            TyKind::FnPtr(s) => Ok(self.body.tys.sig(s).value.output),
            TyKind::FnDef(def, fargs) => {
                let f = self.p.local_def(def.hash).ok_or("iterator expansion: a key fn item that is not a local fn")?;
                let args = self.body.tys.args(fargs).to_vec();
                let f = if args.is_empty() { f } else { crate::check::generics::instance_for(self.p, &self.body.tys, f, &args).ok_or("iterator expansion: no key fn instance")? };
                Ok(self.p.fn_info(f).ret)
            }
            // Behind a reference or a box, and a `dyn Fn` value: its
            // `Output` binding (`call_fn` calls the vtable's entry).
            TyKind::Ref(_, _, inner) => self.closure_output(inner),
            _ if let Some(inner) = self.body.tys.boxed_elem(fty) => self.closure_output(inner),
            TyKind::Dyn(..) => {
                let pr = crate::check::object::principal_of(&self.body.tys, fty).ok_or("iterator expansion: a dyn key fn with no principal")?;
                Ok(self.body.tys.bindings(pr.bindings).first().and_then(|(_, g)| g.as_ty()).unwrap_or(crate::ty::UNIT))
            }
            _ => Err("iterator expansion: key fn is not a closure, fn pointer, or fn item".into()),
        }
    }

    /// A bool operand for `a > b` over an `Ord` type lust compares
    /// (check/collect.rs `has_total_ord`): scalars and strings, through
    /// references, and tuples lexicographically, inline; any other type
    /// (a derived `Ord`) through the `cmp` glue.
    fn greater(&mut self, a: Place, b: Place, ty: Ty) -> Result<Operand, String> {
        use crate::ast::BinOp::*;
        match self.body.tys.kind(ty) {
            TyKind::Int(_) | TyKind::Bool | TyKind::Char => Ok(self.cmp(Gt, Operand::Copy(a), Operand::Copy(b))),
            TyKind::Unit => Ok(Operand::Const(Const::Bool(false))),
            TyKind::Ref(_, _, inner) => {
                if inner == STR {
                    let c = self.local(BOOL);
                    self.assign(Place::local(c), Rvalue::StrCmp(Gt, Operand::Copy(a), Operand::Copy(b)));
                    return Ok(Operand::Copy(Place::local(c)));
                }
                self.greater(a.deref(), b.deref(), inner)
            }
            TyKind::Tuple(ts) => {
                // First field that differs decides; all equal is not >.
                let elems: Vec<Ty> = self.body.tys.tys_of(ts).to_vec();
                let out = self.local(BOOL);
                let join = self.block();
                for (i, &e) in elems.iter().enumerate() {
                    let (fa, fb) = (a.project(Proj::Field(i as u32)), b.project(Proj::Field(i as u32)));
                    let g = self.greater(fa.clone(), fb.clone(), e)?;
                    let (yes, no) = self.branch(g);
                    self.cur = yes;
                    self.assign(Place::local(out), Rvalue::Use(Operand::Const(Const::Bool(true))));
                    self.goto(join);
                    self.cur = no;
                    let l = self.greater(fb, fa, e)?;
                    let (less, eq) = self.branch(l);
                    self.cur = less;
                    self.assign(Place::local(out), Rvalue::Use(Operand::Const(Const::Bool(false))));
                    self.goto(join);
                    self.cur = eq;
                }
                self.assign(Place::local(out), Rvalue::Use(Operand::Const(Const::Bool(false))));
                self.goto(join);
                self.cur = join;
                Ok(Operand::Copy(Place::local(out)))
            }
            _ if self.body.tys.is_string_ty(ty) => {
                let (ra, rb) = (self.ref_to(false, a, ty), self.ref_to(false, b, ty));
                let (sa, sb) = (self.local(REF_STR), self.local(REF_STR));
                self.call_builtin(Builtin::StringAsStr, vec![Operand::Copy(Place::local(ra))], Place::local(sa));
                self.call_builtin(Builtin::StringAsStr, vec![Operand::Copy(Place::local(rb))], Place::local(sb));
                let c = self.local(BOOL);
                self.assign(Place::local(c), Rvalue::StrCmp(Gt, Operand::Copy(Place::local(sa)), Operand::Copy(Place::local(sb))));
                Ok(Operand::Copy(Place::local(c)))
            }
            _ => {
                let (ra, rb) = (self.ref_to(false, a, ty), self.ref_to(false, b, ty));
                let c = self.local(BOOL);
                self.assign(Place::local(c), Rvalue::Cmp { op: Gt, a: Operand::Copy(Place::local(ra)), b: Operand::Copy(Place::local(rb)), ty });
                Ok(Operand::Copy(Place::local(c)))
            }
        }
    }

    /// `collect` into `Vec<T>` (Rust's `SpecFromIter` capacity rules),
    /// `Box<[T]>` (a `Vec` collect boxed at the end), or `String`
    /// (the `FromIterator` impl per item type). A try target
    /// (`Result<C, E>`, `Option<C>`) goes through `collect_try`.
    fn collect(&mut self, itp: Place, ty: Ty, dest: Place, dest_ty: Ty) -> R {
        use crate::ast::BinOp::*;
        let item = self.item(ty)?;
        // Try collect (F3): the checker has unified the item with
        // `Result<T, E>` or `Option<T>` for these destinations.
        let try_parts = match (self.body.tys.result_args(dest_ty), self.body.tys.result_args(item)) {
            (Some((c, e)), Some((t, _))) => Some((c, e, t, true)),
            _ => match (self.body.tys.option_elem(dest_ty), self.body.tys.option_elem(item)) {
                (Some(c), Some(t)) => Some((c, UNIT, t, false)),
                _ => None,
            },
        };
        if let Some((c, err_ty, inner, is_result)) = try_parts {
            return self.collect_try(itp, ty, dest, dest_ty, c, err_ty, inner, is_result);
        }
        // `Box<[T]>` is the `Vec` arm below.
        if let Some((k, pointee)) = crate::check::own::own_parts(&self.body.tys, dest_ty).filter(|_| self.body.tys.boxed_slice_elem(dest_ty).is_none()) {
            return self.collect_own(itp, ty, dest, dest_ty, k, pointee);
        }
        let join = self.block();
        if self.body.tys.is_string_ty(dest_ty) {
            let s = self.local(STRING);
            let push = |this: &mut Self, s: Local, x: Local, item: Ty| -> R {
                let rs = this.ref_to(true, Place::local(s), STRING);
                let u = this.local(UNIT);
                let it = this.body.tys.kind(item);
                if item == CHAR {
                    this.call_builtin(Builtin::StringPush, vec![Operand::Move(Place::local(rs)), Operand::Copy(Place::local(x))], Place::local(u));
                } else if matches!(it, TyKind::Ref(_, _, c) if c == CHAR) {
                    this.call_builtin(
                        Builtin::StringPush,
                        vec![Operand::Move(Place::local(rs)), Operand::Copy(Place::local(x).deref())],
                        Place::local(u),
                    );
                } else if item == REF_STR {
                    this.call_builtin(Builtin::StringPushStr, vec![Operand::Move(Place::local(rs)), Operand::Copy(Place::local(x))], Place::local(u));
                } else {
                    let rx = this.ref_to(false, Place::local(x), STRING);
                    let sx = this.local(REF_STR);
                    this.call_builtin(Builtin::StringAsStr, vec![Operand::Copy(Place::local(rx))], Place::local(sx));
                    this.call_builtin(Builtin::StringPushStr, vec![Operand::Move(Place::local(rs)), Operand::Copy(Place::local(sx))], Place::local(u));
                    this.drop_local(x);
                }
                Ok(())
            };
            if item == STRING {
                // The first String is the buffer; the rest append.
                let (_, n, first, _) = self.pull(&itp, ty)?;
                self.assign(Place::local(s), Rvalue::Use(Operand::Move(Place::local(first))));
                self.each(&itp, ty, &mut |this, x, item| push(this, s, x, item))?;
                self.goto(join);
                self.cur = n;
                self.call_builtin(Builtin::StringNew, vec![], Place::local(s));
                self.goto(join);
            } else {
                self.call_builtin(Builtin::StringNew, vec![], Place::local(s));
                if item == CHAR || matches!(self.body.tys.kind(item), TyKind::Ref(_, _, c) if c == CHAR) {
                    // `Extend<char>` reserves the lower bound first.
                    let (lo, _) = self.hint(itp.clone(), ty)?;
                    let rs = self.ref_to(true, Place::local(s), STRING);
                    let u = self.local(UNIT);
                    self.call_builtin(Builtin::StringReserve, vec![Operand::Move(Place::local(rs)), Operand::Copy(Place::local(lo))], Place::local(u));
                }
                self.each(&itp, ty, &mut |this, x, item| push(this, s, x, item))?;
                self.goto(join);
            }
            self.cur = join;
            self.assign(dest, Rvalue::Use(Operand::Move(Place::local(s))));
            return Ok(());
        }
        // `HashMap::from_iter` and `HashSet::from_iter` (W-STD-B):
        // `with_hasher(S::default())`, then `extend`.
        if crate::ty::hash::hash_parts(&self.body.tys, dest_ty).is_some() {
            let m = self.local(dest_ty);
            self.call_builtin(Builtin::HashDefault, vec![], Place::local(m));
            let rm = self.ref_to(true, Place::local(m), dest_ty);
            self.hash_extend(itp, ty, rm)?;
            self.assign(dest, Rvalue::Use(Operand::Move(Place::local(m))));
            return Ok(());
        }
        // A `VecDeque` destination collects into a `Vec` first and
        // wraps it at the end: std's deque collect capacity is the
        // `Vec` one's (W-STD-C phase 2). A `Box<[T]>` destination
        // does the same: alloc's `FromIterator for Box<[T]>` is a
        // `Vec` collect turned into a boxed slice.
        let deque = self.body.tys.local_adt(dest_ty).filter(|&a| self.p.is_vec_deque_adt(a));
        let boxed = self.body.tys.boxed_slice_elem(dest_ty);
        let wrapped = deque.is_some() || boxed.is_some();
        let (Some(elem), vec_ty) = (match (deque, boxed) {
            (Some(_), _) => self.body.tys.adt_first_ty_arg(dest_ty),
            (None, Some(e)) => Some(e),
            (None, None) => self.body.tys.vec_elem(dest_ty),
        }, if wrapped {
            let e = boxed.or_else(|| self.body.tys.adt_first_ty_arg(dest_ty)).unwrap_or(ERROR);
            self.body.tys.mk_vec(e)
        } else {
            dest_ty
        }) else { return Err("iterator expansion: collect into an unsupported type".into()) };
        let v = self.local(vec_ty);
        let with_capacity = |this: &mut Self, cap: Operand| {
            this.assign(Place::local(v), Rvalue::VecLit(elem, Vec::new()));
            let rv = this.ref_to(true, Place::local(v), vec_ty);
            let u = this.local(UNIT);
            this.call_builtin(Builtin::VecReserveExact, vec![Operand::Move(Place::local(rv)), cap], Place::local(u));
        };
        let push = |this: &mut Self, x: Local| {
            let rv = this.ref_to(true, Place::local(v), vec_ty);
            let u = this.local(UNIT);
            let ax = this.take(Place::local(x), elem);
            this.call_builtin(Builtin::VecPush, vec![Operand::Move(Place::local(rv)), ax], Place::local(u));
        };
        // std's allocation reuse (W-STD-B, alloc's in_place_collect.rs): the
        // result keeps the source Vec's buffer, so its capacity is the
        // source's (in bytes). `vec.into_iter().collect()` itself reuses
        // the buffer when unadvanced or at least half full, else extends a
        // new Vec; through the in-place adapters the capacity is
        // `src_cap * size_of::<S>() / size_of::<T>()` when the alignments
        // match and `T` is no larger. Every item then fits.
        if let Some((path, src_elem)) = self.in_place_source(ty, elem) {
            let mut sp = itp.clone();
            for _ in 0..path {
                sp = sp.project(Proj::Field(0));
            }
            let vit = it::mk_iter(&mut self.body.tys, IterKind::VecIntoIter, &[src_elem]);
            let rsp = self.ref_to(false, sp, vit);
            let scap = self.local(USIZE);
            self.call_builtin(Builtin::VecIterCap, vec![Operand::Copy(Place::local(rsp))], Place::local(scap));
            if path == 0 {
                // `SpecFromIter<T, vec::IntoIter<T>>`.
                let (front, len) = (self.local(USIZE), self.local(USIZE));
                self.call_builtin(Builtin::VecIterFront, vec![Operand::Copy(Place::local(rsp))], Place::local(front));
                self.call_builtin(Builtin::VecIterLen, vec![Operand::Copy(Place::local(rsp))], Place::local(len));
                let unadvanced = self.cmp(Eq, Operand::Copy(Place::local(front)), Self::usize_c(0));
                let (reuse, check) = self.branch(unadvanced);
                let fresh = self.block();
                let fill = self.block();
                self.cur = check;
                let half = self.local(USIZE);
                self.assign(Place::local(half), Rvalue::Bin(Div, Operand::Copy(Place::local(scap)), Self::usize_c(2)));
                let big = self.cmp(Ge, Operand::Copy(Place::local(len)), Operand::Copy(Place::local(half)));
                let (reuse2, small) = self.branch(big);
                self.cur = reuse2;
                self.goto(reuse);
                self.cur = reuse;
                with_capacity(self, Operand::Copy(Place::local(scap)));
                self.goto(fill);
                // `Vec::new()` then `append_elements`: `reserve(len)`.
                self.cur = small;
                self.goto(fresh);
                self.cur = fresh;
                self.assign(Place::local(v), Rvalue::VecLit(elem, Vec::new()));
                let rvm = self.ref_to(true, Place::local(v), vec_ty);
                let u = self.local(UNIT);
                self.call_builtin(Builtin::VecReserve, vec![Operand::Move(Place::local(rvm)), Operand::Copy(Place::local(len))], Place::local(u));
                self.goto(fill);
                self.cur = fill;
            } else {
                let (s, t) = (self.layout(src_elem)?, self.layout(elem)?);
                let dcap = self.local(USIZE);
                self.assign(Place::local(dcap), Rvalue::Bin(Mul, Operand::Copy(Place::local(scap)), Self::usize_c(s.0)));
                self.assign(Place::local(dcap), Rvalue::Bin(Div, Operand::Copy(Place::local(dcap)), Self::usize_c(t.0)));
                with_capacity(self, Operand::Copy(Place::local(dcap)));
            }
            self.each(&itp, ty, &mut |this, x, _| {
                push(this, x);
                Ok(())
            })?;
            self.goto(join);
            self.cur = join;
            match (deque, boxed) {
                (Some(a), _) => self.assign(dest, Rvalue::Aggregate(a, 0, vec![Operand::Move(Place::local(v))])),
                (None, Some(_)) => self.call_builtin(Builtin::VecIntoBoxedSlice, vec![Operand::Move(Place::local(v))], dest),
                (None, None) => self.assign(dest, Rvalue::Use(Operand::Move(Place::local(v)))),
            }
            return Ok(());
        }
        if self.trusted_len(ty) {
            // `with_capacity(upper)`, then every item fits.
            let (_, hi) = self.hint(itp.clone(), ty)?;
            let (s, n) = self.switch_opt(&Place::local(hi));
            self.cur = n;
            self.term(Terminator::Panic(vec![FmtPart::Lit("capacity overflow".into())]));
            // TrustedLen `SpecFromIterNested` panics in alloc.
            self.body.blocks[self.cur.0 as usize].term_span = crate::diag::Span::std_site(6, 57, 18);
            self.cur = s;
            with_capacity(self, Operand::Copy(Self::payload(&Place::local(hi))));
            // `extend_trusted` writes through `for_each`, so a fold.
            self.each(&itp, ty, &mut |this, x, _| {
                push(this, x);
                Ok(())
            })?;
            self.goto(join);
        } else {
            // First item, then `max(MIN_NON_ZERO_CAP, lower + 1)`, then
            // `extend_desugared`: reserve `lower + 1` whenever full. The
            // amortized reserve of an empty Vec is that capacity (the
            // runtime knows the element size, which the Rust layout of a
            // std source type such as `Cell<T>` does not give here).
            let (_, n, first, _) = self.pull(&itp, ty)?;
            let (lo, _) = self.hint(itp.clone(), ty)?;
            let l1 = self.local(USIZE);
            self.call_builtin(Builtin::SaturatingAdd, vec![Operand::Copy(Place::local(lo)), Self::usize_c(1)], Place::local(l1));
            self.assign(Place::local(v), Rvalue::VecLit(elem, Vec::new()));
            let rvm = self.ref_to(true, Place::local(v), vec_ty);
            let u = self.local(UNIT);
            self.call_builtin(Builtin::VecReserve, vec![Operand::Move(Place::local(rvm)), Operand::Copy(Place::local(l1))], Place::local(u));
            push(self, first);
            let lp = self.block();
            self.goto(lp);
            self.cur = n;
            self.assign(Place::local(v), Rvalue::VecLit(elem, Vec::new()));
            self.goto(join);
            self.cur = lp;
            let (_, n2, x, _) = self.pull(&itp, ty)?;
            let rv = self.ref_to(false, Place::local(v), vec_ty);
            let (len, capn) = (self.local(USIZE), self.local(USIZE));
            self.call_builtin(Builtin::VecLen, vec![Operand::Copy(Place::local(rv))], Place::local(len));
            self.call_builtin(Builtin::VecCapacity, vec![Operand::Copy(Place::local(rv))], Place::local(capn));
            let full = self.cmp(Eq, Operand::Copy(Place::local(len)), Operand::Copy(Place::local(capn)));
            let (grow, ok) = self.branch(full);
            self.cur = grow;
            let (lo2, _) = self.hint(itp.clone(), ty)?;
            let add = self.local(USIZE);
            self.call_builtin(Builtin::SaturatingAdd, vec![Operand::Copy(Place::local(lo2)), Self::usize_c(1)], Place::local(add));
            let rvm = self.ref_to(true, Place::local(v), vec_ty);
            let u = self.local(UNIT);
            self.call_builtin(Builtin::VecReserve, vec![Operand::Move(Place::local(rvm)), Operand::Copy(Place::local(add))], Place::local(u));
            self.goto(ok);
            self.cur = ok;
            push(self, x);
            self.goto(lp);
            self.cur = n2;
            self.goto(join);
        }
        self.cur = join;
        match (deque, boxed) {
            (Some(a), _) => self.assign(dest, Rvalue::Aggregate(a, 0, vec![Operand::Move(Place::local(v))])),
            (None, Some(_)) => self.call_builtin(Builtin::VecIntoBoxedSlice, vec![Operand::Move(Place::local(v))], dest),
            (None, None) => self.assign(dest, Rvalue::Use(Operand::Move(Place::local(v)))),
        }
        Ok(())
    }

    /// `collect` into `Box<str>`, `Rc<[T]>`, or `Arc<[T]>` (alloc's
    /// impls). `Box<str>` is a `String` collect, then `into_boxed_str`.
    /// The shared slices are `ToRcSlice`: a `TrustedLen` source fills
    /// one allocation of its size hint's upper bound through `next`
    /// (`from_iter_exact`; no upper bound panics before any pull), any
    /// other source collects a `Vec` and converts it (`From<Vec<T>>`).
    fn collect_own(&mut self, itp: Place, ty: Ty, dest: Place, dest_ty: Ty, k: crate::check::own::Owner, pointee: Ty) -> R {
        let el = match self.body.tys.kind(pointee) {
            TyKind::Slice(el) if k != crate::check::own::Owner::Box => el,
            TyKind::Str if k == crate::check::own::Owner::Box => {
                let s = self.local(STRING);
                self.collect(itp, ty, Place::local(s), STRING)?;
                self.call_builtin(Builtin::OwnFrom(k), vec![Operand::Move(Place::local(s))], dest);
                return Ok(());
            }
            _ => return Err("iterator expansion: collect into an unsupported owning pointer".into()),
        };
        if !self.trusted_len(ty) {
            let vt = self.body.tys.mk_vec(el);
            let v = self.local(vt);
            self.collect(itp, ty, Place::local(v), vt)?;
            self.call_builtin(Builtin::OwnFrom(k), vec![Operand::Move(Place::local(v))], dest);
            return Ok(());
        }
        let (_, hi) = self.hint(itp.clone(), ty)?;
        let (some, none) = self.switch_opt(&Place::local(hi));
        self.cur = none;
        self.term(Terminator::Panic(vec![FmtPart::Lit("capacity overflow".into())]));
        // rc.rs and sync.rs (`stdloc::STD_FILES` 30 and 31).
        let (file, line) = if k == crate::check::own::Owner::Rc { (30, 3174) } else { (31, 4241) };
        self.body.blocks[self.cur.0 as usize].term_span = crate::diag::Span::std_site(file, line, 13);
        self.cur = some;
        let r = self.local(dest_ty);
        let rr = self.ref_to(true, Place::local(r), dest_ty);
        let u = self.local(UNIT);
        self.call_builtin(Builtin::OwnSliceAlloc(k), vec![Operand::Move(Place::local(rr)), Operand::Copy(Self::payload(&Place::local(hi)))], Place::local(u));
        let lp = self.block();
        self.goto(lp);
        self.cur = lp;
        let (_, done, x, _) = self.pull(&itp, ty)?;
        let rr = self.ref_to(true, Place::local(r), dest_ty);
        let ax = self.take(Place::local(x), el);
        let u = self.local(UNIT);
        self.call_builtin(Builtin::OwnSlicePush, vec![Operand::Move(Place::local(rr)), ax], Place::local(u));
        self.goto(lp);
        self.cur = done;
        self.assign(dest, Rvalue::Use(Operand::Move(Place::local(r))));
        Ok(())
    }

    /// `collect` into `Result<C, E>` or `Option<C>` (F3): core's
    /// generic impls collect `C` from a short-circuit wrapper over
    /// the source (the `TryCollect` kind, std's `ProcessResults`),
    /// then read the wrapper's stored failure. Drop order is
    /// std's: on a failure the wrapper drops first (the source
    /// iterator and its unconsumed items), then the built prefix
    /// of `C`; the error value itself moves into the result.
    /// Capacity on the success path is the inner collect's own,
    /// over the wrapper (its hint has no lower bound, and the
    /// in-place reuse rules read through it).
    fn collect_try(&mut self, itp: Place, ty: Ty, dest: Place, dest_ty: Ty, c: Ty, err_ty: Ty, inner: Ty, is_result: bool) -> R {
        let wrap_ty = it::mk_iter(&mut self.body.tys, IterKind::TryCollect, &[ty, err_ty, inner]);
        let w = self.local(wrap_ty);
        let opt_err = self.body.tys.mk_option(err_ty);
        let slot = self.local(opt_err);
        self.none(&Place::local(slot), opt_err);
        let src = self.take(itp, ty);
        self.assign(Place::local(w), Rvalue::TupleAgg(wrap_ty, vec![src, Operand::Move(Place::local(slot))]));
        let coll = self.local(c);
        self.collect(Place::local(w), wrap_ty, Place::local(coll), c)?;
        let join = self.block();
        let slot_pl = Place::local(w).project(Proj::Field(1));
        let (failed, ok) = self.switch_opt(&slot_pl);
        // Success: wrap the collection, then drop the wrapper (the
        // exhausted source), as std drops it before returning.
        self.cur = ok;
        let cv = self.take(Place::local(coll), c);
        if is_result {
            self.assign(dest.clone(), Rvalue::Res(dest_ty, true, cv));
        } else {
            self.some(&dest, dest_ty, cv);
        }
        self.drop_local(w);
        self.goto(join);
        // Failure: take the error out, drop the wrapper, then the
        // built prefix, then write the failure result.
        self.cur = failed;
        if is_result {
            let e = self.local(err_ty);
            let ev = self.take(Self::payload(&slot_pl), err_ty);
            self.assign(Place::local(e), Rvalue::Use(ev));
            self.drop_local(w);
            self.drop_local(coll);
            let ev = self.take(Place::local(e), err_ty);
            self.assign(dest.clone(), Rvalue::Res(dest_ty, false, ev));
        } else {
            self.drop_local(w);
            self.drop_local(coll);
            self.none(&dest, dest_ty);
        }
        self.goto(join);
        self.cur = join;
        Ok(())
    }

    /// When `collect` into `Vec<T>` keeps the source buffer (std's
    /// `SpecFromIter` impls, W-STD-B): a `vec::IntoIter<S>` itself (0
    /// adapter levels), or through std's InPlaceIterable adapters lust has
    /// (Map, Filter, FilterMap, MapWhile, Enumerate, Zip's first side, Skip, Take,
    /// SkipWhile, TakeWhile, Inspect, Cloned) when S and T are not zero
    /// sized, align the same, and T is no larger. The adapter depth (each
    /// level's source is its field 0) and S.
    fn in_place_source(&self, ty: Ty, item: Ty) -> Option<(usize, Ty)> {
        use IterKind as K;
        let (k, a) = self.kind_args(ty)?;
        if k == K::VecIntoIter {
            return Some((0, a[0]));
        }
        let mut depth = 0;
        let mut cur = (k, a);
        loop {
            match cur.0 {
                K::Map | K::Filter | K::FilterMap | K::MapWhile | K::Enumerate | K::Zip | K::Skip | K::Take | K::SkipWhile | K::TakeWhile | K::Inspect | K::Cloned | K::TryCollect => {
                    depth += 1;
                    cur = self.kind_args(cur.1[0])?;
                }
                K::VecIntoIter => break,
                _ => return None,
            }
        }
        let src = cur.1[0];
        let (s, t) = (self.layout(src).ok()?, self.layout(item).ok()?);
        (s.0 > 0 && t.0 > 0 && s.1 == t.1 && s.0 >= t.0).then_some((depth, src))
    }

    /// (size, align) of a type, as Rust lays it out.
    fn layout(&self, t: Ty) -> Result<(u64, u64), String> {
        let l = crate::ty::layout::layout_of_ty(&self.body.tys, self.p, t).map_err(|_| self.layout_unknown(t))?;
        Ok((l.size, l.align))
    }

    /// The error for an element type `layout_of_ty` has no layout for
    /// (it names the type, so a build failure points at the gap).
    fn layout_unknown(&self, t: Ty) -> String {
        format!("iterator expansion: element layout unknown: `{}`", crate::check::collect::ty_name(self.p, &self.body.tys, t))
    }
}
