// Lowering: checked AST to IR. Makes evaluation order, temporaries, moves, borrows, and drops explicit.
use crate::ast::{self, BinOp, Expr, ExprId, FmtKind, FmtPiece, FmtSpec, MacroKind, Pat, PatId, Stmt};
use crate::check::collect::*;
use crate::check::opaque::Hold;
use crate::check::{Autoref, BindMode, Builtin, Checked, CmpVia, Coerce, OrdPickKind, OrderingOpKind, PatRes, PrimCmpKind, PrimOpKind, Res};
use crate::diag::Span;
use crate::ir::*;
use crate::ty::*;
use crate::ty::constqual::Qualif;

mod any;
mod closure;
pub mod iter;
mod range_fmt;
pub mod tls;
mod unwind;

struct LoopInfo {
    break_bb: Bb,
    continue_bb: Bb,
    dest: Option<Place>,
    depth: usize,
    label: Option<(crate::intern::Sym, crate::diag::Span)>,
    is_block: bool,
}

struct Lower<'p> {
    p: &'p Program,
    ck: Checked<'p>,
    body: Body<'p>,
    cur: Bb,
    /// Each scope lists its locals in declaration order. They drop in reverse at scope exit.
    scopes: Vec<Vec<Local>>,
    loops: Vec<LoopInfo>,
    local_map: Vec<Local>,
    /// Depth of mutable place evaluation (see `place_for_mut`).
    mut_index: u32,
    /// A method receiver lowered as a Cow's `&B` view (W-STD-B,
    /// `Coerce::CowRecv`) or moved into a `ByNext` iterator
    /// (`Coerce::ByNext`): the receiver expression, and the local and
    /// type of the value made from it, which `place`, `operand`, and
    /// `ty` give for it while the method call lowers.
    cow_view: Option<(ExprId, Local, Ty)>,
    /// The Cow expression `cow_view_of` is currently lowering: `place`
    /// and `ty` answer for that Cow itself, not its view (any other
    /// expression still answers with its view, so nested Cow places
    /// work).
    making_cow_view: Option<ExprId>,
    /// `needs_drop` answers per body type: every scope exit asks for each of
    /// its locals, and the answer walks Adt fields.
    drop_ty: crate::intern::FxMap<Ty, bool>,
    /// Set while lowering a closure body fn (see `lower::closure`).
    upvars: Option<closure::Upvars>,
    /// While a match guard lowers, the place each of the arm's
    /// pattern bindings reads through (see `bind_pat_guard`):
    /// parallel to the checker's locals, `None` outside a guard.
    /// `place` consults it before `local_map`.
    guard_places: Vec<Option<Place>>,
    /// For each or-pattern with bindings that `test_pat` has
    /// tested, the local holding the index of the alternative
    /// that matched: `bind_pat` switches on it because bindings
    /// move only after the whole pattern (and any guard) pass.
    or_tags: Vec<(PatId, Local)>,
    /// While one expanded guard row lowers (see `match_into`),
    /// the alternative each or-pattern is fixed to for the row.
    or_forced: Vec<(PatId, usize)>,
    /// The guard temporary already made for a checker local, so
    /// every alternative (and guard row) that binds it writes
    /// the one temporary a guard later reads.
    guard_temps: Vec<(u32, Local)>,
    /// The IR local a pattern binding was created as, by
    /// checker local: all or-pattern alternatives of one name
    /// share a checker local and must assign the same IR local.
    bind_reuse: Vec<(u32, Local)>,
    /// Depth of `bind_pat` recursion, for tag cleanup at the
    /// outermost call (see `bind_pat`).
    bind_depth: u32,
    /// Binary-chain spine nodes already lowered into a temporary by
    /// `prelower_binary_spine`, with the generation of the spine run
    /// that made them (see `expr_into_raw`). An entry is taken out
    /// when the node's value is consumed, exactly once.
    prelowered: Vec<(ExprId, Place, u32)>,
    /// The current binary-spine run number; each run cleans up its
    /// own unconsumed `prelowered` entries.
    spine_gen: u32,
    /// Temporary lifetime extension (rustc `record_rvalue_scope`):
    /// while a `let` initializer lowers, the expressions whose
    /// temporaries live to the end of the enclosing block, with the
    /// index of that block's scope (see `let_stmt`, `materialize`).
    extended: Vec<(ExprId, usize)>,
    /// The shared unwind cleanup ladder of `call_into`: one block
    /// per (local, successor) pair, dropping that local and going
    /// to the successor, so cleanup paths that share a suffix
    /// share its blocks. Without sharing, each call re-emitted a
    /// drop for every local in scope, so a chain of n calls in one
    /// scope made O(n^2) statements (a 2000-link method chain
    /// lowered to about 2M statements).
    unwind_steps: crate::intern::FxMap<(Local, Bb), Bb>,
    /// The shared last block of every cleanup path: no drops, an
    /// `Unreachable` terminator.
    unwind_end: Option<Bb>,
    /// The most recent cleanup path, as its drop sequence (first
    /// local dropped first) and its entry block. A call whose
    /// sequence ends with it reuses it as the suffix, so only the
    /// locals added since then need new ladder steps.
    unwind_last: Option<(Vec<Local>, Bb)>,
    /// Set while a cleanup ladder step lowers its drops: those drops
    /// are cleanup themselves and get no cleanup entry.
    in_cleanup: bool,
    /// Each binding's IR local with its checker local, for its opaque
    /// mark (`mark_opaque_locals`).
    bind_of: Vec<(Local, u32)>,
    /// An expression that lowers as code even though the checker
    /// const-evaluated it: the root of an anonymous const's own body
    /// (`check_anon_consts`).
    as_code: Option<ExprId>,
}

/// The scope depth `mark_extending` gives a const initializer's
/// extended temporaries: none, they are promoted (`promoted_temp`).
const STATIC_SCOPE: usize = usize::MAX;

/// Lowers one checked function body to IR.
pub fn lower<'p>(p: &'p Program, fid: LocalDefId, mut ck: Checked<'p>) -> Body<'p> {
    if p.gx.closure_fns.contains_key(&fid) {
        return closure::lower_closure(p, fid, ck);
    }
    let f = p.fn_info(fid);
    // The owned type store lift (ARCH 2.1): the checked body's types move into the
    // lowered body through this boundary. Identity today; see `ty::lift_to_owned`.
    let tys = lift_to_owned(std::mem::replace(&mut ck.tys, Tys::new(&p.tys)));
    let reads = std::mem::take(&mut ck.reads);
    let entry = BlockData { stmts: Vec::new(), term: Terminator::Unreachable, term_span: Span::default() };
    let body = Body {
        fn_id: fid,
        tys,
        locals: Vec::new(),
        blocks: vec![entry],
        arg_count: f.params.len(),
        reads,
        lower_errs: Vec::new(),
        annotations: Vec::new(),
        promoted: Vec::new(),
        index_exprs: Vec::new(),
        pat_back_index: Vec::new(),
        pat_front_index: Vec::new(),
        pat_subslice: Vec::new(),
        dyn_coerce: Vec::new(),
        false_edges: Vec::new(),
        opaque_locals: Vec::new(),
        opaque_nodrop: Vec::new(),
        stmt_unwind: Vec::new(),
    };
    let mut lw = Lower {
        p,
        ck,
        body,
        cur: Bb(0),
        scopes: vec![Vec::new()],
        loops: Vec::new(),
        local_map: Vec::new(),
        mut_index: 0,
        cow_view: None,
        making_cow_view: None,
        drop_ty: Default::default(),
        upvars: None,
        guard_places: Vec::new(),
        or_tags: Vec::new(),
        or_forced: Vec::new(),
        guard_temps: Vec::new(),
        bind_reuse: Vec::new(),
        bind_depth: 0,
        prelowered: Vec::new(),
        spine_gen: 0,
        extended: Vec::new(),
        unwind_steps: Default::default(),
        unwind_end: None,
        unwind_last: None,
        in_cleanup: false,
        bind_of: Vec::new(),
        as_code: None,
    };
    // A template's own `impl Trait` return is its hidden type here, so the
    // borrow checker sees the returned value's regions (check/opaque.rs).
    let ret = match p.tys.kind(f.ret) {
        TyKind::Opaque(od, _) => lw.ck.opaque_hidden.iter().find(|(d, _)| *d == od).map_or(f.ret, |&(_, h)| h),
        _ => f.ret,
    };
    lw.new_local(ret, true, None);
    lw.local_map = vec![u32::MAX; lw.ck.locals.len()];
    lw.guard_places = vec![None; lw.ck.locals.len()];
    for i in 0..lw.ck.param_locals.len() {
        let cl = lw.ck.param_locals[i];
        let info = &lw.ck.locals[cl as usize];
        let (ty, m, name) = (info.ty, info.mutable, p.name(info.name).to_string());
        let l = lw.new_local(ty, m, Some(name));
        lw.local_map[cl as usize] = l;
        lw.bind_of.push((l, cl));
        lw.scopes[0].push(l);
    }
    // Pattern parameters bind out of their argument locals
    // before the body: the bindings drop first, then the parts
    // of the arguments they did not move drop with the locals
    // above, as in a destructuring `let`.
    {
        let skip = usize::from(f.def(&p.ast).self_param.is_some());
        let param_pats: Vec<(ast::PatId, Local)> = f
            .def(&p.ast)
            .params
            .iter()
            .zip(lw.ck.param_locals.iter().skip(skip))
            .filter_map(|(param, &cl)| param.pat.map(|pat| (pat, lw.local_map[cl as usize])))
            .collect();
        for (pat, arg) in param_pats {
            lw.bind_pat(pat, Place::local(arg));
        }
    }
    // A declaration shape (a trait method with no body) lowers to an
    // empty return so this can never panic; cgen refuses to generate
    // it or any call to it (`cgen::has_generated_body`).
    let (span, body) = match f.def(&p.ast).body {
        Some(b) => (p.ast.block(b).span, Some(b)),
        None => (Span::default(), None),
    };
    // A const or static initializer (check/const_body.rs), or the hidden
    // fn holding a copy of one (`Program::is_value_init_fn`): the
    // temporaries its value extends live in static storage, as rustc
    // gives a const initializer's extended temporaries `'static`.
    if (f.loc.is_const_init() || p.is_value_init_fn(fid))
        && let Some(t) = body.and_then(|b| p.ast.block(b).tail)
    {
        lw.mark_extending(t, STATIC_SCOPE);
    }
    if let Some(b) = body {
        lw.block_into(b, Some(&Place::local(0)));
    }
    lw.pop_scope(span);
    lw.terminate(Terminator::Return, span);
    lw.map_annotations();
    lw.mark_opaque_locals();
    check_anon_consts(lw)
}

/// Borrow-checks the anonymous consts of a body: `const { .. }` blocks,
/// and array repeat counts other than a literal or a path. The checker
/// typed their code, but the body uses only their values, so the code
/// never reached the IR. Each one lowers as a body of its own over the
/// same checked types, returning its value (the temporaries the value
/// extends are static, as in a const item), and its borrowck errors join
/// this body's lowering errors, which borrowck reports first.
fn check_anon_consts(lw: Lower<'_>) -> Body<'_> {
    let p = lw.p;
    let Lower { mut ck, body: mut main, .. } = lw;
    for e in anon_consts(p, main.fn_id, &ck) {
        let ty = ck.ty(e);
        let entry = BlockData { stmts: Vec::new(), term: Terminator::Unreachable, term_span: Span::default() };
        let sub = Body {
            fn_id: main.fn_id,
            tys: main.tys.clone(),
            locals: Vec::new(),
            blocks: vec![entry],
            arg_count: 0,
            reads: Default::default(),
            lower_errs: Vec::new(),
            annotations: Vec::new(),
            promoted: Vec::new(),
            index_exprs: Vec::new(),
            pat_back_index: Vec::new(),
            pat_front_index: Vec::new(),
            pat_subslice: Vec::new(),
            dyn_coerce: Vec::new(),
            false_edges: Vec::new(),
            opaque_locals: Vec::new(),
            opaque_nodrop: Vec::new(),
            stmt_unwind: Vec::new(),
        };
        let mut lw = Lower {
            p,
            ck,
            body: sub,
            cur: Bb(0),
            scopes: vec![Vec::new()],
            loops: Vec::new(),
            local_map: Vec::new(),
            mut_index: 0,
            cow_view: None,
            making_cow_view: None,
            drop_ty: Default::default(),
            upvars: None,
            guard_places: Vec::new(),
            or_tags: Vec::new(),
            or_forced: Vec::new(),
            guard_temps: Vec::new(),
            bind_reuse: Vec::new(),
            bind_depth: 0,
            prelowered: Vec::new(),
            spine_gen: 0,
            extended: Vec::new(),
            unwind_steps: Default::default(),
            unwind_end: None,
            unwind_last: None,
            in_cleanup: false,
            bind_of: Vec::new(),
            as_code: Some(e),
        };
        lw.new_local(ty, true, None);
        lw.local_map = vec![u32::MAX; lw.ck.locals.len()];
        lw.guard_places = vec![None; lw.ck.locals.len()];
        let span = p.ast.expr_span(e);
        let tail = match p.ast.expr(e) {
            Expr::ConstBlock(b) | Expr::Block(b) => p.ast.block(*b).tail,
            _ => Some(e),
        };
        if let Some(t) = tail {
            lw.mark_extending(t, STATIC_SCOPE);
        }
        match p.ast.expr(e) {
            Expr::ConstBlock(b) | Expr::Block(b) => lw.block_into(*b, Some(&Place::local(0))),
            _ => lw.expr_into(e, Some(&Place::local(0))),
        }
        lw.pop_scope(span);
        lw.terminate(Terminator::Return, span);
        let Lower { ck: back, body: mut sub, .. } = lw;
        ck = back;
        let ret = crate::check::const_body::all_static(&mut sub.tys, ty);
        main.lower_errs.extend(crate::borrowck::borrowck_const(p, &sub, ret));
    }
    main
}

/// The anonymous consts `check_anon_consts` lowers for fn `f`: in a
/// plain fn or a template (an instance or closure body is checked with
/// its source), the checker typed, and not inside a nested item (that
/// item's own body owns them).
fn anon_consts(p: &Program, f: LocalDefId, ck: &Checked) -> Vec<ExprId> {
    use crate::check::generics::FnClass;
    if !matches!(p.gx.fn_class.get(f.0 as usize), Some(FnClass::Plain | FnClass::Template)) || p.gx.closure_fns.contains_key(&f) {
        return Vec::new();
    }
    let (lo, hi) = p.fn_def(f).exprs;
    let mut out: Vec<ExprId> = Vec::new();
    for e in (lo..hi).map(ExprId) {
        match p.ast.expr(e) {
            Expr::ConstBlock(_) => out.push(e),
            Expr::ArrayRepeat { len, .. } if !matches!(p.ast.expr(*len), Expr::Int(..) | Expr::Path(_)) => out.push(*len),
            _ => {}
        }
    }
    // The anonymous consts of written types the checker typed.
    out.extend(ck.anon_exprs.iter().copied());
    out.retain(|&e| ck.ty(e) != ERROR);
    if out.is_empty() {
        return out;
    }
    let nested: Vec<(u32, u32)> = p
        .ast
        .stmt_items
        .iter()
        .filter_map(|it| match &it.kind {
            ast::ItemKind::Fn(d) => Some(d.exprs),
            ast::ItemKind::Const(c) => c.init_fn.as_ref().map(|d| d.exprs),
            ast::ItemKind::Static(s) => s.init_fn.as_ref().map(|d| d.exprs),
            _ => None,
        })
        .filter(|&(a, b)| a >= lo && b <= hi && (a, b) != (lo, hi))
        .collect();
    out.retain(|e| !nested.iter().any(|&(a, b)| e.0 >= a && e.0 < b));
    out
}

impl<'p> Lower<'p> {
    // ---------- Building blocks ----------

    fn new_local(&mut self, ty: Ty, mutable: bool, name: Option<String>) -> Local {
        self.body.locals.push(LocalDecl { ty, mutable, name });
        self.body.locals.len() as Local - 1
    }
    /// A temporary, owned by the innermost scope.
    fn temp(&mut self, ty: Ty) -> Local {
        let l = self.new_local(ty, true, None);
        self.scopes.last_mut().unwrap().push(l);
        l
    }
    /// A promoted temporary: the storage of a value borrowed for
    /// `'static` (a const reference's pointee, `&5`, `&[]`). It is in
    /// no scope, so it is never dropped, and cgen gives it static
    /// storage, so a reference to it may escape its function.
    fn promoted_temp(&mut self, ty: Ty) -> Local {
        let l = self.new_local(ty, true, None);
        self.body.promoted.push(l);
        l
    }
    /// Evaluates `e` (through its coercion unless `raw`) into a new
    /// temporary of type `ty`. As rustc's `as_temp` schedules a
    /// temporary's drop after evaluating its expression, the temporary
    /// joins its scope only then, so it drops before the temporaries
    /// of its own expression (`wrap(&mk()).0`: the wrapper, then the
    /// argument). Its scope is the innermost one, or the enclosing
    /// block's when a `let` extends it (`extended`).
    fn materialize(&mut self, e: ExprId, ty: Ty, raw: bool) -> Local {
        let t = self.new_local(ty, true, None);
        if raw {
            self.expr_into_raw(e, Some(&Place::local(t)));
        } else {
            self.expr_into(e, Some(&Place::local(t)));
        }
        self.push_extended(e, t);
        t
    }
    /// Puts temporary `t` of expression `e` in its scope: the innermost
    /// one, or the one a `let` extends `e` to, or static storage for a
    /// const initializer's value (`STATIC_SCOPE`).
    fn push_extended(&mut self, e: ExprId, t: Local) {
        match self.extended.iter().rev().find(|&&(x, _)| x == e).map_or(self.scopes.len() - 1, |&(_, d)| d) {
            STATIC_SCOPE => self.body.promoted.push(t),
            depth => self.scopes[depth].push(t),
        }
    }
    /// True while lowering a const or static initializer or an anonymous
    /// const other than an inline `const { .. }` block (`check_anon_consts`):
    /// the const contexts where rustc promotes a `const fn` call. An inline
    /// const promotes as a fn body does.
    /// True while lowering a body only borrowck reads: a const or static
    /// initializer, or an anonymous const (`check_anon_consts`).
    fn check_only(&self) -> bool {
        self.as_code.is_some() || self.p.fn_info(self.body.fn_id).loc.is_const_init()
    }
    fn const_context(&self) -> bool {
        match self.as_code {
            Some(e) => !matches!(self.p.ast.expr(e), Expr::ConstBlock(_)),
            None => self.p.fn_info(self.body.fn_id).loc.is_const_init() || self.p.is_value_init_fn(self.body.fn_id),
        }
    }
    /// True when `&e` is promoted to `'static` (rustc's promotion rules,
    /// a conservative subset): a literal, a negated or cast literal, a
    /// const path check folded, arithmetic over those (never a fn call), a
    /// unit variant or unit struct, a shared borrow of a promotable value,
    /// or a tuple, array, array repeat, struct literal, or constructor
    /// call of those, of a type this handles (`promotable_ty`), whose
    /// value needs no drop and has no interior mutability
    /// (`value_qualif`: `&None::<String>` is promoted).
    fn promotable(&mut self, e: ExprId) -> bool {
        let ty = self.ty(e);
        if !self.promotable_ty(ty, 0) || self.value_qualif(e).any() {
            return false;
        }
        match self.p.ast.expr(e) {
            Expr::Int(..) | Expr::Float(_) | Expr::Bool(_) | Expr::Char(_) | Expr::Str(_) | Expr::Unit => true,
            Expr::Unary { op: crate::ast::UnOp::Neg, expr } => matches!(self.p.ast.expr(*expr), Expr::Int(..) | Expr::Float(_)),
            // Arithmetic over promotable operands. As in rustc, a division
            // needs a divisor known to be nonzero (here: a nonzero literal),
            // and `&&` and `||` branch, so they are not promoted.
            Expr::Binary { op, lhs, rhs } => {
                use crate::ast::BinOp as B;
                let (op, lhs, rhs) = (*op, *lhs, *rhs);
                let op_ok = match op {
                    B::And | B::Or => false,
                    B::Div | B::Rem => matches!(self.p.ast.expr(rhs), Expr::Int(v, _) if *v != 0),
                    _ => true,
                };
                // On a reference operand (`&1 + 2`) the operator is a trait
                // call, which is never promoted.
                let by_ref = |s: &mut Self, x: ExprId| {
                    let t = s.ty(x);
                    matches!(s.kind(t), TyKind::Ref(..))
                };
                op_ok && !by_ref(self, lhs) && !by_ref(self, rhs) && self.promotable(lhs) && self.promotable(rhs)
            }
            // A numeric cast or a fn item to fn pointer (check types the
            // item as the pointer already) of a promotable operand. A pointer to integer cast is never promoted in rustc.
            Expr::Cast { expr, .. } => {
                let inner = *expr;
                let st = self.ty(inner);
                let scalar = |k: TyKind| matches!(k, TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char);
                let ok = (scalar(self.kind(st)) && scalar(self.kind(ty)))
                    || (matches!(self.kind(st), TyKind::FnDef(..) | TyKind::FnPtr(_)) && matches!(self.kind(ty), TyKind::FnPtr(_)));
                ok && self.promotable(inner)
            }
            Expr::Tuple(es) | Expr::Array(es) => es.clone().iter().all(|&x| self.promotable(x)),
            Expr::ArrayRepeat { value, .. } => self.promotable(*value),
            // A tuple struct, tuple variant, `Some`, `Ok` or `Err` constructor call.
            Expr::Call { callee, args } => {
                // In a const or static initializer (not in a fn), rustc
                // promotes a call to a `const fn` too.
                let const_call = self.const_context()
                    && [self.ck.res(e), self.ck.res(*callee)].into_iter().any(|r| matches!(r, Res::Fn(f) if self.p.fn_info(f).is_const));
                (const_call || matches!(self.ck.res(e), Res::Variant(..) | Res::OptSome | Res::ResOk | Res::ResErr))
                    && args.clone().iter().all(|&x| self.promotable(x))
            }
            Expr::Path(_) => {
                self.ck.const_value(e).is_some()
                    || matches!(self.ck.res(e), Res::OptNone | Res::Fn(_))
                    || (matches!(self.ck.res(e), Res::Variant(..)) && !matches!(self.kind(ty), TyKind::FnDef(..)))
            }
            Expr::StructLit { fields, update: None, .. } => fields.clone().iter().all(|f| self.promotable(f.2)),
            // A shared reference to a promotable value (`&&5`, `&&C`), or
            // a reborrow through one (`&&*"q"`), is a constant too.
            Expr::Ref { mutable: false, raw: false, expr } => {
                let inner = *expr;
                self.promotable(inner) || matches!(self.p.ast.expr(inner), Expr::Deref(d) if self.promotable(*d))
            }
            _ => false,
        }
    }

    /// True when a value of type `t` may be promoted by its shape:
    /// scalars, raw and fn pointers, fn items, `&str`, shared refs to such, and tuples,
    /// arrays, `Option`, `Result`, this crate's Adts built of them, and
    /// std Adts. Drops and interior mutability are the value's
    /// question (`value_qualif`).
    fn promotable_ty(&mut self, t: Ty, depth: u32) -> bool {
        if depth > 8 {
            return false;
        }
        match self.kind(t) {
            TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Str | TyKind::Never => true,
            TyKind::RawPtr(..) | TyKind::FnPtr(_) | TyKind::FnDef(..) => true,
            TyKind::Tuple(ts) => self.body.tys.tys_of(ts).to_vec().into_iter().all(|x| self.promotable_ty(x, depth + 1)),
            TyKind::Array(el, _) | TyKind::Slice(el) => self.promotable_ty(el, depth + 1),
            TyKind::Ref(_, Mut::Shared, inner) => self.promotable_ty(inner, depth + 1),
            _ if t == UNIT => true,
            _ => {
                if let Some(inner) = self.body.tys.option_elem(t) {
                    return self.promotable_ty(inner, depth + 1);
                }
                if let Some((ok, err)) = self.body.tys.result_args(t) {
                    return self.promotable_ty(ok, depth + 1) && self.promotable_ty(err, depth + 1);
                }
                // A std Adt (`String`, `Cell`): its fields are std's.
                let Some(a) = self.body.tys.local_adt(t) else { return matches!(self.kind(t), TyKind::Adt(..)) };
                if self.p.is_std_adt(a) {
                    return true;
                }
                let args: Vec<GenericArg> = match self.kind(t) {
                    TyKind::Adt(_, a) => self.body.tys.args(a).to_vec(),
                    _ => Vec::new(),
                };
                let fields: Vec<Ty> = self.p.adt(a).variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect();
                fields.into_iter().all(|f| {
                    let f = subst(&mut self.body.tys, f, &args);
                    self.promotable_ty(f, depth + 1)
                })
            }
        }
    }

    /// rustc's promotion qualifs (NeedsDrop, HasMutInterior) of the
    /// value `e` builds, by value as rustc's promote_consts computes
    /// them: an aggregate by its parts (plus NeedsDrop for an Adt with
    /// a `Drop` impl), a const item path by its initializer
    /// (`ty::constqual`, recorded by check), anything else by its type.
    fn value_qualif(&mut self, e: ExprId) -> Qualif {
        let ty = self.ty(e);
        let by_ty = Qualif { drop: self.needs_drop_ty(ty), cell: self.mut_interior_ty(ty, 0) };
        if !by_ty.any() {
            return Qualif::NONE;
        }
        let parts = |s: &mut Self, es: &[ExprId]| es.iter().fold(Qualif::NONE, |q, &x| q.or(s.value_qualif(x)));
        let inherent = |s: &mut Self| match s.body.tys.local_adt(ty) {
            Some(a) => Qualif { drop: s.p.gx.drop_methods.contains_key(&a) || s.p.drop_adts.contains(&a), cell: false },
            None => Qualif::NONE,
        };
        let q = match self.p.ast.expr(e) {
            Expr::Int(..) | Expr::Float(_) | Expr::Bool(_) | Expr::Char(_) | Expr::Str(_) | Expr::Unit => Qualif::NONE,
            Expr::Tuple(es) | Expr::Array(es) => parts(self, &es.clone()),
            Expr::ArrayRepeat { value, .. } => self.value_qualif(*value),
            Expr::Call { args, .. } if matches!(self.ck.res(e), Res::Variant(..) | Res::OptSome | Res::ResOk | Res::ResErr) => {
                let args = args.clone();
                inherent(self).or(parts(self, &args))
            }
            Expr::StructLit { fields, update: None, .. } => {
                let fs: Vec<ExprId> = fields.iter().map(|f| f.2).collect();
                inherent(self).or(parts(self, &fs))
            }
            Expr::Path(_) if self.ck.const_value(e).is_some() => self.ck.const_quals.get(&e).copied().unwrap_or(Qualif::ALL),
            Expr::Path(_) if matches!(self.ck.res(e), Res::OptNone) => Qualif::NONE,
            Expr::Path(_) if matches!(self.ck.res(e), Res::Variant(..)) => inherent(self),
            Expr::Ref { expr, .. } => self.value_qualif(*expr),
            _ => Qualif::ALL,
        };
        q.and(by_ty)
    }

    /// True when a value of type `t` may hold an `UnsafeCell` (not
    /// `Freeze`), read through this body's types: `collect::interior_mut`
    /// with Adt fields substituted here. Unknown shapes answer true.
    fn mut_interior_ty(&mut self, t: Ty, depth: u32) -> bool {
        if depth > 16 {
            return true;
        }
        match self.kind(t) {
            TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Str | TyKind::Never | TyKind::Unit => return false,
            TyKind::Ref(..) | TyKind::RawPtr(..) | TyKind::FnPtr(_) | TyKind::FnDef(..) => return false,
            TyKind::Tuple(ts) => return self.body.tys.tys_of(ts).to_vec().into_iter().any(|x| self.mut_interior_ty(x, depth + 1)),
            TyKind::Array(el, _) | TyKind::Slice(el) => return self.mut_interior_ty(el, depth + 1),
            TyKind::Adt(..) => {}
            _ => return true,
        }
        let tys = &self.body.tys;
        if tys.cell_elem(t).is_some()
            || tys.refcell_elem(t).is_some()
            || tys.lock_elem(t).is_some()
            || crate::ty::sync::sync_kind(tys, t) == Some(crate::ty::sync::SyncTy::OnceLock)
            || crate::ty::sync::atomic_of(tys, t).is_some()
        {
            return true;
        }
        if let Some(e) = self.body.tys.option_elem(t) {
            return self.mut_interior_ty(e, depth + 1);
        }
        if let Some((a, b)) = self.body.tys.result_args(t) {
            return self.mut_interior_ty(a, depth + 1) || self.mut_interior_ty(b, depth + 1);
        }
        let Some(a) = self.body.tys.local_adt(t) else { return false };
        if matches!(
            crate::intern::source_name(self.p.interner.get(self.p.adt(a).name)),
            "UnsafeCell" | "Once" | "OnceLock" | "OnceCell" | "LazyLock" | "LazyCell"
        ) {
            return true;
        }
        let args: Vec<GenericArg> = match self.kind(t) {
            TyKind::Adt(_, a) => self.body.tys.args(a).to_vec(),
            _ => Vec::new(),
        };
        let fields: Vec<Ty> = self.p.adt(a).variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect();
        fields.into_iter().any(|f| {
            let f = subst(&mut self.body.tys, f, &args);
            self.mut_interior_ty(f, depth + 1)
        })
    }

    /// Whether a value of type `ty` needs a drop (cached per body type).
    fn needs_drop_ty(&mut self, ty: Ty) -> bool {
        if let Some(&d) = self.drop_ty.get(&ty) {
            return d;
        }
        let d = needs_drop(self.p, &self.body.tys, ty);
        self.drop_ty.insert(ty, d);
        d
    }
    fn new_block(&mut self) -> Bb {
        self.body.blocks.push(BlockData { stmts: Vec::new(), term: Terminator::Unreachable, term_span: Span::default() });
        Bb(self.body.blocks.len() as u32 - 1)
    }
    fn push(&mut self, kind: StmtKind, span: Span) {
        let unwinds = self.p.unwind && !self.in_cleanup && self.may_unwind(&kind);
        self.body.blocks[self.cur.0 as usize].stmts.push(crate::ir::Stmt { kind, span });
        if unwinds {
            let n = self.body.blocks[self.cur.0 as usize].stmts.len() as u32 - 1;
            self.record_unwind(n, span);
        }
    }
    /// Records the cleanup entry at the current scopes for statement
    /// `idx` of the current block (`Body::stmt_unwind`).
    fn record_unwind(&mut self, idx: u32, span: Span) {
        let at = self.cur;
        let entry = self.unwind_block(span);
        self.body.stmt_unwind.push((at, idx, entry));
    }
    /// Whether a statement can start or pass on a panic, so it needs a
    /// cleanup entry under panic=unwind. Conservative: only moves,
    /// borrows, and value building of plain operands with no indexed
    /// place and no destination drop are known not to.
    fn may_unwind(&mut self, kind: &StmtKind) -> bool {
        match kind {
            StmtKind::StorageDead(_) | StmtKind::FakeRead(_) => false,
            StmtKind::Drop(_) | StmtKind::Print { .. } => true,
            StmtKind::Assign(dest, rv) => {
                let indexed = |pl: &Place| pl.proj.iter().any(|p| matches!(p, crate::ir::Proj::Index(_)));
                let op_indexed = |o: &Operand| matches!(o, Operand::Copy(pl) | Operand::Move(pl) if indexed(pl));
                if indexed(dest) || !dest.proj.is_empty() || self.needs_drop_ty(self.body.locals[dest.local as usize].ty) {
                    return true;
                }
                match rv {
                    Rvalue::Use(o) | Rvalue::Opt(_, Some(o)) | Rvalue::Res(_, _, o) => op_indexed(o),
                    Rvalue::Ref(_, pl) | Rvalue::Discriminant(pl) | Rvalue::SliceOf(pl) | Rvalue::LenOf(pl) => indexed(pl),
                    Rvalue::Aggregate(_, _, os) | Rvalue::TupleAgg(_, os) | Rvalue::ArrayAgg(_, os) => os.iter().any(op_indexed),
                    Rvalue::Opt(_, None) | Rvalue::StaticRef(_) | Rvalue::FnValue(..) | Rvalue::ItemShim(..) => false,
                    Rvalue::MakeDyn { ptr, .. } | Rvalue::DynUpcast { ptr, .. } | Rvalue::DynMeta { ptr, .. } | Rvalue::DynData { ptr, .. } => {
                        op_indexed(ptr)
                    }
                    _ => true,
                }
            }
        }
    }
    fn assign(&mut self, place: Place, rv: Rvalue, span: Span) {
        self.push(StmtKind::Assign(place, rv), span);
    }
    /// The mono instance for a call whose checked resolution
    /// names a template, through the zonked generic args the
    /// checker recorded for this expression (W-TRAITS-CORE through
    /// the lower owner). Plain fns answer themselves.
    /// The checker's regioned `let` annotations (W-BORROW) on the IR
    /// locals their bindings lowered to. In a closure body, a captured
    /// variable's shadow local takes none: the enclosing body's own `let`
    /// holds that annotation, and the capture's regions are the closure's
    /// captured ones, which its requirements relate there.
    fn map_annotations(&mut self) {
        for &(cl, t) in &self.ck.annotations {
            if let Some(&l) = self.local_map.get(cl as usize)
                && l != u32::MAX
                && !self.upvars.as_ref().is_some_and(|u| u.shadows(l))
            {
                self.body.annotations.push((l, t));
            }
        }
    }

    fn resolve_generic_fn(&self, e: ExprId, f: LocalDefId) -> LocalDefId {
        if self.p.gx.fn_templates.get(f.0 as usize).is_none_or(|t| t.is_none()) {
            return f;
        }
        match self.site_args(e, f) {
            Some(args) if !args.is_empty() => crate::check::generics::instance_for(self.p, &self.body.tys, f, args).unwrap_or(f),
            _ => f,
        }
    }

    /// The type args check recorded for template `f` called at `e`.
    fn site_args(&self, e: ExprId, f: LocalDefId) -> Option<&[GenericArg]> {
        let ei = (e.0 - self.ck.expr_base) as usize;
        // Two sites can share one expression (a `for` head call and
        // the loop's `next`): the per-template table wins there.
        if let Some((_, _, args)) = self.ck.generic_site_args.iter().find(|(i, t, _)| *i == ei && *t == f) {
            return Some(args);
        }
        self.ck.generic_args.get(ei).map(|a| a.as_slice())
    }

    /// The return type of template `template` called at `e` (`f` is
    /// `resolve_generic_fn(e, template)`), regions erased: with no
    /// instance yet (`lust check`), the site's type args go in, as check
    /// typed the call. The written regions are the callee's lifetimes,
    /// none of this body.
    fn site_ret_ty(&mut self, e: ExprId, template: LocalDefId, f: LocalDefId) -> Ty {
        let ret = self.p.fn_info(f).ret;
        let ret = match self.site_args(e, template) {
            Some(args) if f == template && !args.is_empty() => {
                let args = args.to_vec();
                subst(&mut self.body.tys, ret, &args)
            }
            _ => ret,
        };
        crate::borrowck::erase(&mut self.body.tys, ret)
    }

    /// Emits a call terminator that writes its result to `dest` and continues
    /// in a fresh block. The unwind successor is a cleanup path that drops
    /// every enclosing scope's locals, innermost first, through the same
    /// `emit_drops` order scope exit uses, then ends in `Unreachable`,
    /// where the wave C runtime resumes the exception (docs/ARCH.md
    /// section 7.2). The path comes from the shared ladder
    /// (`unwind_block`), never from a fresh copy per call.
    fn call_into(&mut self, target: CallTarget, args: Vec<Operand>, dest: Place, span: Span) {
        // A call owns its moved arguments from its start (codegen clears their flags there), so
        // reading an argument must not panic inside it: an argument read through an index (a
        // bounds check) is read into a temporary first, by a statement whose cleanup still drops
        // what the earlier arguments moved (`take(b, a[i])` drops `b`).
        let args = args.into_iter().map(|a| self.unindexed(a, span)).collect();
        let next = self.new_block();
        let unwind = Some(self.unwind_block(span));
        let b = &mut self.body.blocks[self.cur.0 as usize];
        b.term = Terminator::Call { target, args, dest, next, unwind };
        b.term_span = span;
        self.cur = next;
    }

    /// Call argument `a` (`call_into`), or, when it reads a place through an index, a
    /// temporary of the current scope that holds the value it reads.
    fn unindexed(&mut self, a: Operand, span: Span) -> Operand {
        let (Operand::Copy(pl) | Operand::Move(pl)) = &a else { return a };
        if !pl.proj.iter().any(|p| matches!(p, Proj::Index(_))) {
            return a;
        }
        let Some(ty) = self.place_ty(pl) else { return a };
        let t = self.temp(ty);
        // The read is one of the arguments, which run between a two-phase reservation and the
        // `FakeRead` and `&mut` pairs that end the block before the call (`call_arg_operands`;
        // borrowck's `two_phase_loans` finds them at the end): it goes before those pairs, and
        // their statement-unwind entries move up by one.
        let b = self.cur.0 as usize;
        let stmts = &self.body.blocks[b].stmts;
        let mut k = stmts.len();
        while k >= 2 && matches!((&stmts[k - 2].kind, &stmts[k - 1].kind), (StmtKind::FakeRead(_), StmtKind::Assign(_, Rvalue::Ref(true, _)))) {
            k -= 2;
        }
        let tail = self.body.blocks[b].stmts.split_off(k);
        let cur = self.cur;
        for e in self.body.stmt_unwind.iter_mut().filter(|e| e.0 == cur && e.1 >= k as u32) {
            e.1 += 1;
        }
        self.assign(Place::local(t), Rvalue::Use(a), span);
        self.body.blocks[b].stmts.extend(tail);
        self.operand_from(Place::local(t), ty)
    }

    /// The type of an operand place: its local's type through derefs, fields (of tuples,
    /// closures, Options, Results and Adts, substituted) and indexes. None for a shape it does
    /// not know.
    fn place_ty(&mut self, pl: &Place) -> Option<Ty> {
        let mut t = self.body.locals[pl.local as usize].ty;
        let mut variant: Option<u32> = None;
        for pr in &pl.proj {
            t = match *pr {
                Proj::Deref => match self.kind(t) {
                    TyKind::Ref(_, _, i) => i,
                    _ => self.body.tys.smart_elem(t)?,
                },
                Proj::Downcast(v) => {
                    variant = Some(v);
                    continue;
                }
                Proj::Field(i) => {
                    let v = variant.take();
                    if let Some(e) = self.body.tys.option_elem(t) {
                        e
                    } else if let Some((ok, err)) = self.body.tys.result_args(t) {
                        if v == Some(1) { err } else { ok }
                    } else if let TyKind::Tuple(ts) = self.kind(t) {
                        *self.body.tys.tys_of(ts).get(i as usize)?
                    } else if let TyKind::Closure(_, a) = self.kind(t) {
                        *crate::check::collect::closure_fields(&mut self.body.tys, a).get(i as usize)?
                    } else if let Some(a) = self.body.tys.local_adt(t) {
                        let args: Vec<GenericArg> = match self.kind(t) {
                            TyKind::Adt(_, g) => self.body.tys.args(g).to_vec(),
                            _ => Vec::new(),
                        };
                        let f = self.p.adt(a).variants.get(v.unwrap_or(0) as usize)?.fields.get(i as usize)?.ty;
                        subst(&mut self.body.tys, f, &args)
                    } else {
                        return None;
                    }
                }
                Proj::Index(_) => match self.kind(t) {
                    TyKind::Slice(e) | TyKind::Array(e, _) => e,
                    _ => self.body.tys.vec_elem(t)?,
                },
            };
        }
        Some(t)
    }

    /// The entry block of the cleanup path for a call at the current
    /// scopes (see `call_into`). Builds only the ladder steps this
    /// path needs that no earlier call built: the last path built,
    /// when it is a suffix of this one, serves as the suffix, and
    /// every step goes through the `(local, successor)` table.
    fn unwind_block(&mut self, span: Span) -> Bb {
        // The drop sequence: innermost scope first, reversed in scope.
        let mut seq: Vec<Local> = Vec::new();
        for scope in self.scopes.iter().rev() {
            seq.extend(scope.iter().rev().copied());
        }
        if self.unwind_end.is_none() {
            self.unwind_end = Some(self.new_block());
        }
        let suffix = match &self.unwind_last {
            Some((last, entry)) if seq.len() >= last.len() && seq[seq.len() - last.len()..] == last[..] => {
                Some((*entry, seq.len() - last.len()))
            }
            _ => None,
        };
        let (mut bb, wrap) = suffix.unwrap_or((self.unwind_end.unwrap(), seq.len()));
        for &l in seq[..wrap].iter().rev() {
            bb = self.unwind_step(l, bb, span);
        }
        self.unwind_last = Some((seq, bb));
        bb
    }

    /// One ladder step: the shared block that drops `l` (the same
    /// statements `emit_drops` makes for it at scope exit) and goes
    /// to `next`. A step is built once per (local, successor) pair;
    /// its statements keep the span of the call that built it.
    fn unwind_step(&mut self, l: Local, next: Bb, span: Span) -> Bb {
        if let Some(&bb) = self.unwind_steps.get(&(l, next)) {
            return bb;
        }
        let bb = self.new_block();
        let saved = (self.cur, self.in_cleanup);
        self.cur = bb;
        self.in_cleanup = true;
        self.emit_drops(&[l], span);
        self.goto(next, span);
        (self.cur, self.in_cleanup) = saved;
        self.unwind_steps.insert((l, next), bb);
        bb
    }
    /// The place a call result goes: the given destination, or a throwaway
    /// temporary for a call in statement position.
    fn call_dest(&mut self, dest: Option<&Place>, ty: Ty) -> Place {
        match dest {
            Some(d) => d.clone(),
            None => Place::local(self.temp(ty)),
        }
    }
    /// Ends the current block. Later code goes into a fresh block (unreachable if nothing jumps there).
    fn terminate(&mut self, term: Terminator, span: Span) {
        if self.p.unwind && matches!(term, Terminator::Panic(_)) {
            let n = self.body.blocks[self.cur.0 as usize].stmts.len() as u32;
            self.record_unwind(n, span);
        }
        let b = &mut self.body.blocks[self.cur.0 as usize];
        b.term = term;
        b.term_span = span;
        self.cur = self.new_block();
    }
    fn goto(&mut self, target: Bb, span: Span) {
        let b = &mut self.body.blocks[self.cur.0 as usize];
        b.term = Terminator::Goto(target);
        b.term_span = span;
        self.cur = target;
    }
    /// Fills `Body::opaque_locals` and `opaque_nodrop` from how each
    /// local holds `impl Trait` values in the opaque view: a binding by
    /// its own view type (`Checked::local_holds`), any other local by
    /// the type match (`type_hold`).
    fn mark_opaque_locals(&mut self) {
        // A view body (a template check) has no recorded holds: its
        // locals hold opaque values by their own types, which
        // `view_hold` reads directly (`type_hold` below then has no
        // view pairs to match, and answers None for them).
        if self.ck.opaque_holds.is_empty() {
            for l in 0..self.body.locals.len() {
                let ty = self.body.locals[l].ty;
                match crate::check::opaque::view_hold(self.p, &self.body.tys, ty) {
                    Hold::None => {}
                    Hold::Copy if !self.needs_drop_ty(ty) => {
                        self.body.opaque_locals.push(l as Local);
                        self.body.opaque_nodrop.push(l as Local);
                    }
                    _ => self.body.opaque_locals.push(l as Local),
                }
            }
            return;
        }
        let mut hold: Vec<Option<Hold>> = vec![None; self.body.locals.len()];
        if !self.ck.local_holds.is_empty() {
            for &(l, cl) in &self.bind_of {
                hold[l as usize] = Some(self.ck.local_holds[cl as usize]);
            }
        }
        for l in 0..self.body.locals.len() {
            let ty = self.body.locals[l].ty;
            match hold[l].unwrap_or_else(|| self.type_hold(ty)) {
                Hold::None => {}
                Hold::Copy if !self.needs_drop_ty(ty) => {
                    self.body.opaque_locals.push(l as Local);
                    self.body.opaque_nodrop.push(l as Local);
                }
                _ => self.body.opaque_locals.push(l as Local),
            }
        }
    }
    /// How a value of type `ty` may hold `impl Trait` values: the most
    /// of the view holds (`Checked::opaque_holds`) whose revealed types
    /// it owns. A plain value of the same type counts too, which can
    /// only make the borrow check stricter. A revealed type the check
    /// left unresolved (an inference var or a projection, which no
    /// local's type holds) counts for every local, so a missed match is
    /// a false reject, never a false accept.
    fn type_hold(&self, ty: Ty) -> Hold {
        let tys = &self.body.tys;
        let of = |&(r, h): &(Ty, Hold)| {
            let f = tys.flags(r);
            if f.contains_infer() || f.contains_projection() {
                Hold::Drop
            } else if crate::check::opaque::ty_contains(tys, ty, r) {
                h
            } else {
                Hold::None
            }
        };
        self.ck.opaque_holds.iter().map(of).max().unwrap_or_default()
    }
    fn emit_drops(&mut self, locals: &[Local], span: Span) {
        for &l in locals.iter().rev() {
            let ty = self.body.locals[l as usize].ty;
            if self.needs_drop_ty(ty) || self.type_hold(ty) == Hold::Drop {
                self.push(StmtKind::Drop(l), span);
            }
            self.push(StmtKind::StorageDead(l), span);
        }
    }
    /// Drops the innermost scope's locals, then pops it. The scope stays
    /// on the stack while its drops lower, so a drop that panics gets a
    /// cleanup entry that still drops the scope's other locals.
    fn pop_scope(&mut self, span: Span) {
        let s = self.scopes.last().unwrap().clone();
        self.emit_drops(&s, span);
        self.scopes.pop();
    }
    /// Emits drops for every scope deeper than `depth`, without popping them (for break/return).
    fn exit_to(&mut self, depth: usize, span: Span) {
        for i in (depth..self.scopes.len()).rev() {
            let ls = self.scopes[i].clone();
            self.emit_drops(&ls, span);
        }
    }

    fn span(&self, e: ExprId) -> Span {
        self.p.ast.expr_span(e)
    }
    /// The `[` of index expression `e`, where rustc reports `Index::index`
    /// panics. The AST keeps no span for it, so: right after a plain base
    /// (`v[ i ]` too); right before the index after a parenthesized base,
    /// as rustfmt writes `(v)[i]`; the macro call when the brackets come
    /// from a macro body (`e`'s span then covers the call, `Span::to`).
    /// For a plain base the span runs from the base's end to the index,
    /// so `v` and `[i]` on separate lines resolve to the `[`
    /// (`SourceMap::line_display_col`).
    fn bracket_span(&self, e: ExprId, base: ExprId, index: ExprId) -> Span {
        let (whole, b, s) = (self.span(e), self.span(base), self.span(index));
        if whole.lo == b.lo && whole.ctxt == b.ctxt {
            let hi = if s.ctxt == b.ctxt && s.file == b.file && s.lo > b.hi { s.lo } else { b.hi + 1 };
            return Span { lo: b.hi, hi, ..b };
        }
        let before = s.lo.saturating_sub(1);
        if before >= b.hi && s.ctxt == b.ctxt && s.file == b.file {
            return Span { lo: before, hi: s.lo, ..s };
        }
        whole
    }
    /// Gives the index local `i` its panic location `at` (see
    /// `Proj::Index`): re-spans its assignment when that is the last
    /// statement and cannot panic itself, else adds `i = copy i` at `at`.
    fn mark_index_loc(&mut self, i: Local, at: Span) {
        let blk = &mut self.body.blocks[self.cur.0 as usize];
        let plain = |o: &Operand| match o {
            Operand::Copy(q) | Operand::Move(q) => !q.proj.iter().any(|x| matches!(x, Proj::Index(_))),
            _ => true,
        };
        if let Some(st) = blk.stmts.last_mut()
            && let StmtKind::Assign(p, Rvalue::Use(o)) = &st.kind
            && plain(o)
            && p.local == i
            && p.proj.is_empty()
        {
            st.span = at;
            return;
        }
        self.assign(Place::local(i), Rvalue::Use(Operand::Copy(Place::local(i))), at);
    }
    fn ty(&self, e: ExprId) -> Ty {
        // A `CowRecv` expression lowers as its `&B` view (a method
        // receiver, a field or index base, a `*cow`): its type here
        // is the view's, except inside `cow_view_of` itself.
        if self.making_cow_view != Some(e)
            && let Coerce::CowRecv(_, view) = self.ck.coerce(e)
        {
            return view;
        }
        match self.cow_view {
            Some((x, _, t)) if x == e => t,
            _ => self.ck.ty(e),
        }
    }
    fn kind(&self, t: Ty) -> TyKind {
        self.body.tys.kind(t)
    }
    fn ref_ty(&mut self, m: bool, t: Ty) -> Ty {
        self.body.tys.mk_ref(m, t)
    }
    fn peel(&self, mut t: Ty, n: u8) -> Ty {
        for _ in 0..n {
            if let TyKind::Ref(_, _, inner) = self.kind(t) {
                t = inner;
            } else if let Some(inner) = self.body.tys.smart_elem(t) {
                t = inner;
            }
        }
        t
    }
    fn operand_from(&self, place: Place, ty: Ty) -> Operand {
        if is_copy(self.p, &self.body.tys, ty) { Operand::Copy(place) } else { Operand::Move(place) }
    }
    /// True when the value of `e` is `Copy` here but moves in rustc (an
    /// `impl Trait` whose hidden type is `Copy`, `Checked::expr_moves`).
    fn view_moved(&self, e: ExprId) -> bool {
        self.ck.expr_moves.get((e.0 - self.ck.expr_base) as usize).copied().unwrap_or(false)
    }
    /// `view_moved` for a checker local (a binding or a captured root).
    fn local_moved(&self, local: u32) -> bool {
        self.ck.local_moves.get(local as usize).copied().unwrap_or(false)
    }
    fn derefs(place: Place, n: u8) -> Place {
        let mut p = place;
        for _ in 0..n {
            p = p.deref();
        }
        p
    }

    // ---------- Places and operands ----------

    fn is_place_expr(&self, e: ExprId) -> bool {
        match self.p.ast.expr(e) {
            Expr::Path(_) | Expr::SelfValue => matches!(self.ck.res(e), Res::Local(_) | Res::Static(_)),
            Expr::Field { .. } | Expr::TupleField { .. } | Expr::Index { .. } | Expr::Deref(_) => true,
            _ => false,
        }
    }

    /// True when the place chain of `e` is rooted in a local variable:
    /// the parts of it a pattern does not move stay in that variable
    /// and drop with it. A chain rooted in a value (`make().pair`,
    /// `*make_box()`) holds the value in a temporary instead, and the
    /// temporary drops after the pattern's moves, as a match
    /// scrutinee temporary does in rustc.
    fn place_root_owned(&self, e: ExprId) -> bool {
        match self.p.ast.expr(e) {
            Expr::Path(_) | Expr::SelfValue => matches!(self.ck.res(e), Res::Local(_)),
            Expr::Field { base, .. } | Expr::TupleField { base, .. } | Expr::Index { base, .. } => self.place_root_owned(*base),
            Expr::Deref(inner) => self.place_root_owned(*inner),
            _ => false,
        }
    }

    /// True for a bare `..` element of an assignment target
    /// (`[a, .., b]`, `(a, ..)`, `Pair(a, ..)`). The parser reads it
    /// as an open range expression.
    fn is_rest_elem(&self, e: ExprId) -> bool {
        matches!(self.p.ast.expr(e), Expr::Range { lo: None, hi: None, inclusive: false })
    }

    /// Maps target elements to source indices, skipping the elements
    /// a `..` rest covers. The checker reports a bad count, so a
    /// mapping that does not fit just keeps the indices in range.
    fn map_assign_elems(&self, elems: &[ExprId], n: usize) -> Vec<(usize, ExprId)> {
        match elems.iter().position(|&e| self.is_rest_elem(e)) {
            None => elems.iter().enumerate().filter(|(i, _)| *i < n).map(|(i, &e)| (i, e)).collect(),
            Some(r) => {
                let suffix = elems.len() - r - 1;
                let mut out: Vec<(usize, ExprId)> = elems[..r].iter().enumerate().filter(|(i, _)| *i < n).map(|(i, &e)| (i, e)).collect();
                for (j, &e) in elems[r + 1..].iter().enumerate() {
                    if !self.is_rest_elem(e) && n >= suffix {
                        out.push((n - suffix + j, e));
                    }
                }
                out
            }
        }
    }

    /// True when `lhs` is a destructuring assignment target: a tuple,
    /// array, struct, or tuple-struct form, a `_` or `()` discard, or
    /// a unit variant path.
    fn is_destr_assign(&self, lhs: ExprId) -> bool {
        match self.p.ast.expr(lhs) {
            Expr::Tuple(_) | Expr::Array(_) | Expr::Underscore | Expr::StructLit { .. } | Expr::Unit => true,
            Expr::Call { .. } => matches!(self.ck.res(lhs), Res::Variant(..)),
            Expr::Path(_) => matches!(self.ck.res(lhs), Res::Variant(..)),
            _ => false,
        }
    }

    /// Evaluates `e` to a place that will be written or mutably borrowed. A `Vec` index in
    /// such a place is an `IndexMut` borrow in Rust: the mutable borrow of the container
    /// starts before the index expression runs, so `v[v.len()] = 1` and `&mut v[v.len()]`
    /// are errors. The `Index` case in `place` models that while `mut_index` is set: it
    /// takes a `&mut` temporary of the container first and indexes through it.
    fn place_for_mut(&mut self, e: ExprId) -> Place {
        self.mut_index += 1;
        let p = self.place(e);
        self.mut_index -= 1;
        p
    }

    /// Evaluates `e` to a place. A value expression goes into a new temporary.
    fn place(&mut self, e: ExprId) -> Place {
        if let Some((x, v, _)) = self.cow_view
            && x == e
        {
            return Place::local(v);
        }
        // A field or index base through a Cow's `Deref` (the method
        // receiver case is the `cow_view` above): the place is the
        // `&B` view local, and the recorded derefs count from it.
        if self.making_cow_view != Some(e)
            && let Coerce::CowRecv(n, view) = self.ck.coerce(e)
        {
            let v = self.cow_view_of(e, n, view);
            return Place::local(v);
        }
        if let Some(pl) = self.take_prelowered(e) {
            return pl;
        }
        match (self.p.ast.expr(e), self.ck.res(e)) {
            (Expr::Path(_) | Expr::SelfValue, Res::Local(l)) => match &self.guard_places[l as usize] {
                // A match guard reads its arm's bindings through a
                // shared reference (see `bind_pat_guard`).
                Some(p) => p.clone(),
                None => Place::local(self.local_map[l as usize]),
            },
            (Expr::Field { base, .. }, Res::Field { derefs, index }) => {
                // Through a user `Deref` impl, the field is on the target.
                let span = self.span(e);
                let b = match self.deref_steps(e, *base, span) {
                    Some(root) => root,
                    None => self.place(*base),
                };
                Self::derefs(b, derefs).project(Proj::Field(index))
            }
            (Expr::TupleField { base, .. }, Res::Field { derefs, index }) => {
                let span = self.span(e);
                let b = match self.deref_steps(e, *base, span) {
                    Some(root) => root,
                    None => self.place(*base),
                };
                // `SendError(pub T)` is the value itself in C: `.0` is the
                // same place (check/mod.rs `send_error_elem`).
                let bt = self.peel(self.ty(*base), derefs);
                if index == 0 && crate::check::send_error_elem(&self.body.tys, bt).is_some() {
                    return Self::derefs(b, derefs);
                }
                Self::derefs(b, derefs).project(Proj::Field(index))
            }
            (Expr::Index { base, index }, Res::SliceIndex { derefs }) => {
                let span = self.span(e);
                let (b, root_ty) = match self.deref_steps(e, *base, span) {
                    Some(root) => {
                        let t = self.body.locals[root.local as usize].ty;
                        (root, t)
                    }
                    None => (self.place(*base), self.ty(*base)),
                };
                let b = Self::derefs(b, derefs);
                // A range index is always `Index::index` (or `index_mut`
                // in a mutable use): the base is borrowed before the
                // range runs, so a range that reads (or writes) the base
                // conflicts as in rustc (E0502).
                let mutable = self.mut_index > 0;
                let bt = self.peel(root_ty, derefs);
                let rt = self.ref_ty(mutable, bt);
                let r = self.temp(rt);
                self.assign(Place::local(r), Rvalue::Ref(mutable, b), span);
                let b = Place::local(r).deref();
                // The bounds are values, not part of the mutable place.
                let saved = std::mem::take(&mut self.mut_index);
                let (lo, hi, inclusive) = if let Some(form) = self.ck.index_range(e) {
                    // A range value as the index (check/slice.rs):
                    // its fields are the bounds.
                    self.range_value_bounds(*index, form, span)
                } else {
                    let (lo_e, hi_e, inclusive) = match self.p.ast.expr(*index) {
                        Expr::Range { lo, hi, inclusive } => (*lo, *hi, *inclusive),
                        _ => (None, None, false),
                    };
                    let bound = |this: &mut Self, e: Option<ExprId>| -> Option<Operand> {
                        e.map(|e| {
                            let t = this.temp(USIZE);
                            this.expr_into(e, Some(&Place::local(t)));
                            Operand::Copy(Place::local(t))
                        })
                    };
                    let lo = bound(self, lo_e).unwrap_or(Operand::Const(Const::Int(0, IntTy::Usize)));
                    let hi = bound(self, hi_e);
                    (lo, hi, inclusive)
                };
                self.mut_index = saved;
                // The temporary holds the slice place itself (bare `[T]`
                // or `str` type, a fat value in codegen).
                let slice = match self.kind(self.ty(e)) {
                    TyKind::Slice(el) => self.body.tys.intern(TyKind::Slice(el)),
                    TyKind::Str => STR,
                    _ => ERROR,
                };
                let t = self.temp(slice);
                // Range indexing is `Index::index`: it panics at the brackets.
                let span = self.bracket_span(e, *base, *index);
                self.assign(Place::local(t), Rvalue::Subslice { base: b, lo, hi, inclusive, mutable }, span);
                Place::local(t)
            }
            (Expr::Index { base, index }, Res::Index { derefs }) => {
                let span = self.span(e);
                let (b, root_ty) = match self.deref_steps(e, *base, span) {
                    Some(root) => {
                        let t = self.body.locals[root.local as usize].ty;
                        (root, t)
                    }
                    None => (self.place(*base), self.ty(*base)),
                };
                let b = Self::derefs(b, derefs);
                // Mutable use: borrow the container before the index expression runs
                // (see `place_for_mut`), and index through that borrow.
                let b = if self.mut_index > 0 {
                    let bt = self.peel(root_ty, derefs);
                    let rt = self.ref_ty(true, bt);
                    let t = self.temp(rt);
                    let span = self.span(e);
                    self.assign(Place::local(t), Rvalue::Ref(true, b), span);
                    Place::local(t).deref()
                } else {
                    b
                };
                let i = self.temp(USIZE);
                self.body.index_exprs.push(i);
                // The index is a value, not part of the mutable place.
                let saved = std::mem::take(&mut self.mut_index);
                self.expr_into(*index, Some(&Place::local(i)));
                self.mut_index = saved;
                // The bounds check panics where rustc does: at the whole
                // `a[i]` for a built-in array or slice index, at the
                // brackets for `Index::index` (a Vec). See `Proj::Index`.
                let builtin = matches!(self.kind(self.peel(self.ty(*base), derefs)), TyKind::Array(..) | TyKind::Slice(_));
                let at = if builtin { self.span(e) } else { self.bracket_span(e, *base, *index) };
                self.mark_index_loc(i, at);
                b.project(Proj::Index(i))
            }
            // `map[&q]` (W-STD-B): std's `Index<&Q>` is
            // `self.get(key).expect("no entry found for key")`. The place is
            // behind that shared reference; with no `IndexMut`, a write or a
            // move out is the borrow checker's error, as rustc's.
            (Expr::Index { base, index }, Res::MapIndex { derefs }) => {
                let span = self.span(e);
                let (b, root_ty) = match self.deref_steps(e, *base, span) {
                    Some(root) => {
                        let t = self.body.locals[root.local as usize].ty;
                        (root, t)
                    }
                    None => (self.place(*base), self.ty(*base)),
                };
                let b = Self::derefs(b, derefs);
                let map_ref = self.ref_ty(false, self.peel(root_ty, derefs));
                let m = self.temp(map_ref);
                self.assign(Place::local(m), Rvalue::Ref(false, b), span);
                let q = self.temp(self.ty(*index));
                let saved = std::mem::take(&mut self.mut_index);
                self.expr_into(*index, Some(&Place::local(q)));
                self.mut_index = saved;
                let v_ref = self.ref_ty(false, self.ty(e));
                let opt_ty = self.body.tys.mk_option(v_ref);
                let opt = self.temp(opt_ty);
                let args = vec![Operand::Copy(Place::local(m)), Operand::Copy(Place::local(q))];
                self.call_into(CallTarget::Builtin(Builtin::MapGet), args, Place::local(opt), span);
                let d = self.temp(int(IntTy::U32));
                self.assign(Place::local(d), Rvalue::Discriminant(Place::local(opt)), span);
                let (some_b, none_b) = (self.new_block(), self.new_block());
                let blk = &mut self.body.blocks[self.cur.0 as usize];
                blk.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(1, some_b)], none_b);
                blk.term_span = span;
                self.cur = none_b;
                // rustc reports the `[`, as for any `Index::index` panic.
                let at = self.bracket_span(e, *base, *index);
                self.terminate(Terminator::Panic(vec![FmtPart::Lit("no entry found for key".into())]), at);
                self.cur = some_b;
                let r = self.temp(v_ref);
                let some = Place::local(opt).project(Proj::Downcast(1)).project(Proj::Field(0));
                self.assign(Place::local(r), Rvalue::Use(Operand::Copy(some)), span);
                Place::local(r).deref()
            }
            (Expr::Index { base, index }, Res::TraitIndex { derefs }) => {
                // `*Index::index(&base, idx)` (or `index_mut` under a
                // mutable place use), as a user `Deref` step with an
                // argument: borrow the container first (see
                // `place_for_mut`), evaluate the index outside that
                // place, call, and go on from the returned reference.
                let span = self.span(e);
                let Some(rec) = self.ck.index_recv(e).cloned() else {
                    return Place::local(self.temp(self.ty(e)));
                };
                let (b, root_ty) = match self.deref_steps(e, *base, span) {
                    Some(root) => {
                        let t = self.body.locals[root.local as usize].ty;
                        (root, t)
                    }
                    None => (self.place(*base), self.ty(*base)),
                };
                let b = Self::derefs(b, derefs);
                let bt = self.peel(root_ty, derefs);
                let mutable = rec.f_mut.is_some() && self.mut_index > 0;
                let rt = self.ref_ty(mutable, bt);
                let r = self.temp(rt);
                self.assign(Place::local(r), Rvalue::Ref(mutable, b), span);
                let idx_ty = self.ty(*index);
                let iv = self.temp(idx_ty);
                let saved = std::mem::take(&mut self.mut_index);
                self.expr_into(*index, Some(&Place::local(iv)));
                self.mut_index = saved;
                let idx_op = self.operand_from(Place::local(iv), idx_ty);
                let (f, args) = if mutable { (rec.f_mut.unwrap(), &rec.args_mut) } else { (rec.f, &rec.args) };
                let f = if args.is_empty() { f } else { crate::check::generics::instance_for(self.p, &self.body.tys, f, args).unwrap_or(f) };
                let out_ref = self.ref_ty(mutable, self.ty(e));
                let t = self.temp(out_ref);
                let self_arg = if mutable { Operand::Move(Place::local(r)) } else { Operand::Copy(Place::local(r)) };
                // `Index::index` is `#[track_caller]` in core: a panic
                // it passes on reports at the brackets, as a Vec's does.
                let at = self.bracket_span(e, *base, *index);
                self.call_into(CallTarget::Fn(f), vec![self_arg, idx_op], Place::local(t), at);
                Place::local(t).deref()
            }
            (Expr::Deref(inner), _) => match self.ck.coerce(*inner) {
                // `*cow` (W-STD-B): the place behind the Cow's `&B` view.
                Coerce::CowRecv(n, view) => {
                    let v = self.cow_view_of(*inner, n, view);
                    Place::local(v).deref()
                }
                _ => {
                    let span = self.span(e);
                    // `*s` for a `String` or `Vec` (their `Deref`
                    // to `str` / `[T]`): the place behind the
                    // fat view of the value, as for a Cow.
                    let inner_ty = self.ty(*inner);
                    if self.body.tys.is_string_ty(inner_ty) {
                        let m = self.mut_index > 0;
                        let pl = self.place(*inner);
                        let srt = self.ref_ty(m, STRING);
                        let sr = self.temp(srt);
                        self.assign(Place::local(sr), Rvalue::Ref(m, pl), span);
                        let vt = self.ref_ty(m, STR);
                        let t = self.temp(vt);
                        let b = if m { Builtin::StringAsMutStr } else { Builtin::StringAsStr };
                        self.call_into(CallTarget::Builtin(b), vec![Operand::Copy(Place::local(sr))], Place::local(t), span);
                        Place::local(t).deref()
                    } else if let Some(elem) = self.body.tys.vec_elem(inner_ty) {
                        let m = self.mut_index > 0;
                        let pl = self.place(*inner);
                        let slice = self.body.tys.intern(TyKind::Slice(elem));
                        let rt = self.ref_ty(m, slice);
                        let t = self.temp(rt);
                        self.assign(Place::local(t), Rvalue::SliceOf(pl), span);
                        Place::local(t).deref()
                    } else {
                        match self.deref_steps(e, *inner, span) {
                            Some(root) => root.deref(),
                            None => self.place(*inner).deref(),
                        }
                    }
                }
            },
            // A static is a place of its own (W-BORROW): reach it through
            // its address, as `&STATIC` does, never through a copy in a
            // temporary. A borrow of it is then `'static`, and a move out
            // of it is a move out of a reference (rustc E0507).
            (Expr::Path(_), Res::Static(idx)) => {
                let rt = self.ref_ty(false, self.ty(e));
                let t = self.temp(rt);
                let span = self.span(e);
                self.assign(Place::local(t), Rvalue::StaticRef(idx), span);
                Place::local(t).deref()
            }
            // A field, index, or deref the checker could not resolve (its base
            // type is an error type, so no `Res` was recorded): evaluating it
            // through `expr_into` would call `place` on this same expression
            // forever. The checker or borrow checker already reports the real
            // error; give lowering a dummy place and move on.
            (Expr::Field { .. } | Expr::TupleField { .. } | Expr::Index { .. }, _) => {
                let t = self.temp(self.ty(e));
                Place::local(t)
            }
            // A constant value used as a place in a shared context (the base
            // of `&[1, 2][..]`, `&[1, 2][i]` and `&(1, 2).1`, the receiver of
            // `[].as_slice()`) is promoted to `'static`, as rustc promotes the
            // auto-borrowed operand; an empty array of any element type too.
            // Never for a mutable use (`place_for_mut`).
            _ if self.mut_index == 0 && (matches!(self.p.ast.expr(e), Expr::Array(es) if es.is_empty()) || self.promotable(e)) => {
                let t = self.promoted_temp(self.ty(e));
                self.expr_into(e, Some(&Place::local(t)));
                Place::local(t)
            }
            // A value expression goes into a temporary, and the mutable use
            // is of that temporary: the places inside the value (`s[i..]`
            // in `s[i..].chars().next()`) are read as usual.
            _ => {
                let saved = std::mem::take(&mut self.mut_index);
                let t = self.materialize(e, self.ty(e), false);
                self.mut_index = saved;
                Place::local(t)
            }
        }
    }

    /// Evaluates `e` to an operand, applying the coercion recorded by the checker.
    fn operand(&mut self, e: ExprId) -> Operand {
        if let Some((x, v, t)) = self.cow_view
            && x == e
        {
            return self.operand_from(Place::local(v), t);
        }
        let op = self.operand_raw(e);
        let span = self.span(e);
        let ty = self.ty(e);
        match self.ck.coerce(e) {
            Coerce::None => op,
            Coerce::StrFromString => {
                // `&String` (possibly `&&String`, or through a
                // `Box<String>`, whose value is already the
                // `&String` the builtin wants) to `&str`.
                let mut place = self.op_place(op, ty, span);
                let mut t = ty;
                while let TyKind::Ref(_, _, inner) = self.kind(t) {
                    if self.body.tys.is_string_ty(inner) {
                        break;
                    }
                    place = place.deref();
                    t = inner;
                }
                // Through an `Rc<String>`, an `Arc<String>` or a guard
                // (`Ref`, `RefMut`, a lock guard) the builtin still
                // wants the `&String`: form it from the pointee place.
                // Check picks this coercion for every `smart_elem`.
                if self.body.tys.boxed_elem(t).is_none()
                    && let Some(elem) = self.body.tys.smart_elem(t)
                {
                    let sp = place.deref();
                    let rt = self.ref_ty(false, elem);
                    let sr = self.temp(rt);
                    self.assign(Place::local(sr), Rvalue::Ref(false, sp), span);
                    place = Place::local(sr);
                }
                let tmp = self.temp(REF_STR);
                self.call_into(CallTarget::Builtin(Builtin::StringAsStr), vec![Operand::Copy(place)], Place::local(tmp), span);
                Operand::Copy(Place::local(tmp))
            }
            Coerce::BoxToRef(n, m) => {
                let place = self.op_place(op, ty, span);
                let place = Self::derefs(place, n);
                let elem = self.peel(ty, n);
                let rt = self.ref_ty(m, elem);
                let tmp = self.temp(rt);
                self.assign(Place::local(tmp), Rvalue::Ref(m, place), span);
                if m { Operand::Move(Place::local(tmp)) } else { Operand::Copy(Place::local(tmp)) }
            }
            Coerce::Deref(n) => {
                let place = self.op_place(op, ty, span);
                Operand::Copy(Self::derefs(place, n))
            }
            Coerce::SliceFromArray(m) | Coerce::SliceFromVec(m) => {
                let place = self.op_place(op, ty, span);
                let mut inner = self.peel(ty, 1);
                let mut place = place.deref();
                // `&Box<Vec<T>>` and `&Rc<Vec<T>>` slice through
                // the smart pointer as well, and `&&Vec<T>` through
                // the inner reference.
                if let Some(b) = self.slice_source_inner(inner) {
                    place = place.deref();
                    inner = b;
                }
                let elem = match self.kind(inner) {
                    TyKind::Array(e, _) => e,
                    _ => self.body.tys.vec_elem(inner).unwrap_or(ERROR),
                };
                let slice = self.body.tys.intern(TyKind::Slice(elem));
                let rt = self.ref_ty(m, slice);
                let tmp = self.temp(rt);
                self.assign(Place::local(tmp), Rvalue::SliceOf(place), span);
                if m { Operand::Move(Place::local(tmp)) } else { Operand::Copy(Place::local(tmp)) }
            }
            Coerce::MutToShared | Coerce::Reborrow => {
                let m = self.ck.coerce(e) == Coerce::Reborrow;
                let place = self.op_place(op, ty, span);
                let inner = self.peel(ty, 1);
                let rt = self.ref_ty(m, inner);
                let tmp = self.temp(rt);
                self.assign(Place::local(tmp), Rvalue::Ref(m, place.deref()), span);
                if m { Operand::Move(Place::local(tmp)) } else { Operand::Copy(Place::local(tmp)) }
            }
            Coerce::Unsize(target) => self.unsize(op, ty, target, span),
            Coerce::ReifyFn(target) => self.reify_fn(op, ty, target, span),
            // A reference to a raw pointer (w-cinterop): the address
            // value at the pointer type.
            Coerce::RefToPtr(target) => {
                let tmp = self.temp(target);
                self.assign(Place::local(tmp), Rvalue::Use(op), span);
                Operand::Copy(Place::local(tmp))
            }
            // Through user `Deref` impls: the coerced reference's place,
            // then each impl's `deref` (or `deref_mut`).
            Coerce::UserDeref(target) => {
                let steps: Vec<crate::check::DerefRecv> = self.ck.deref_coerce(e).into_iter().cloned().collect();
                let place = self.op_place(op, ty, span);
                let root = self.apply_deref_steps(place, ty, steps, span);
                if matches!(self.kind(target), TyKind::Ref(_, m, _) if m.is_mut()) { Operand::Move(root) } else { Operand::Copy(root) }
            }
            // The user steps, then the `Vec`/`String` builtin deref.
            Coerce::UserDerefTail(target) => {
                let steps: Vec<crate::check::DerefRecv> = self.ck.deref_coerce(e).into_iter().cloned().collect();
                let m = matches!(self.kind(target), TyKind::Ref(_, m, _) if m.is_mut());
                let place = self.op_place(op, ty, span);
                let root = self.apply_deref_steps(place, ty, steps, span);
                let tmp = self.temp(target);
                if matches!(self.kind(self.peel(target, 1)), TyKind::Str) {
                    self.call_into(CallTarget::Builtin(Builtin::StringAsStr), vec![Operand::Copy(root)], Place::local(tmp), span);
                } else {
                    self.assign(Place::local(tmp), Rvalue::SliceOf(root.deref()), span);
                }
                if m { Operand::Move(Place::local(tmp)) } else { Operand::Copy(Place::local(tmp)) }
            }
            // Only a method receiver has it, and `method_into` lowers it.
            Coerce::CowRecv(..) => op,
            // An iterator moved into its `next` wrapper (W-STD-B): for a
            // receiver `method_into` does this first.
            Coerce::ByNext(w) => {
                let v = self.temp(w);
                self.assign(Place::local(v), Rvalue::TupleAgg(w, vec![op]), span);
                Operand::Move(Place::local(v))
            }
            // An `IntoIterator` argument through its `into_iter` call
            // (check/iter.rs `into_iterator_arg`): the call's result is
            // the iterator, wrapped in `ByNext` when the final type is.
            Coerce::IntoIterCall(w) => {
                let Some(local) = self.ck.into_iter_call(e) else { return op };
                let f = self.resolve_generic_fn(e, local);
                let iter_ty = self.p.fn_info(f).ret;
                let it = self.temp(iter_ty);
                self.call_into(CallTarget::Fn(f), vec![op], Place::local(it), span);
                let is_wrap = matches!(crate::ty::iter::iter_parts(&self.body.tys, w), Some((crate::ty::iter::IterKind::ByNext, _)));
                if is_wrap {
                    let v = self.temp(w);
                    self.assign(Place::local(v), Rvalue::TupleAgg(w, vec![Operand::Move(Place::local(it))]), span);
                    Operand::Move(Place::local(v))
                } else {
                    Operand::Move(Place::local(it))
                }
            }
            Coerce::CowDeref(n, target) => {
                // Down to the `&Cow`, then the Cow's `&B` view (W-STD-B).
                let place = self.op_place(op, ty, span);
                let place = Self::derefs(place, n - 1);
                let tmp = self.temp(target);
                self.call_into(CallTarget::Builtin(Builtin::CowDeref), vec![Operand::Copy(place)], Place::local(tmp), span);
                Operand::Copy(Place::local(tmp))
            }
            Coerce::CharPat => {
                // A char as a str pattern: encode it into a temporary
                // String (which drops at scope end) and take its &str.
                let s = self.temp(STRING);
                self.call_into(CallTarget::Builtin(Builtin::StringNew), Vec::new(), Place::local(s), span);
                let mt = self.ref_ty(true, STRING);
                let r = self.temp(mt);
                self.assign(Place::local(r), Rvalue::Ref(true, Place::local(s)), span);
                let u = self.temp(UNIT);
                self.call_into(CallTarget::Builtin(Builtin::StringPush), vec![Operand::Move(Place::local(r)), op], Place::local(u), span);
                let rt2 = self.ref_ty(false, STRING);
                let r2 = self.temp(rt2);
                self.assign(Place::local(r2), Rvalue::Ref(false, Place::local(s)), span);
                let v = self.temp(REF_STR);
                self.call_into(CallTarget::Builtin(Builtin::StringAsStr), vec![Operand::Copy(Place::local(r2))], Place::local(v), span);
                Operand::Copy(Place::local(v))
            }
        }
    }

    /// The type of `e` after its recorded coercion, for temporaries
    /// that hold the coerced operand: the type `operand` produces (a
    /// struct field `&[]` into `&[u8]` is a slice, not `&[u8; 0]`).
    /// What a slice coercion's source (behind its outer reference)
    /// derefs to on the way to the Vec or array: a smart pointer's
    /// value, or an inner reference's target.
    fn slice_source_inner(&self, inner: Ty) -> Option<Ty> {
        match self.kind(inner) {
            TyKind::Ref(_, _, b) => Some(b),
            _ => self.body.tys.smart_elem(inner),
        }
    }

    fn coerced_ty(&mut self, e: ExprId) -> Ty {
        let ty = self.ty(e);
        match self.ck.coerce(e) {
            Coerce::None => ty,
            Coerce::StrFromString | Coerce::CharPat => REF_STR,
            Coerce::Unsize(t) | Coerce::UserDeref(t) | Coerce::UserDerefTail(t) | Coerce::CowDeref(_, t) | Coerce::ReifyFn(t) | Coerce::RefToPtr(t) => t,
            // A receiver-only coercion: `operand` leaves the value as is.
            Coerce::CowRecv(..) => ty,
            Coerce::ByNext(w) | Coerce::IntoIterCall(w) => w,
            Coerce::Deref(n) => self.peel(ty, n),
            Coerce::BoxToRef(n, m) => {
                let elem = self.peel(ty, n);
                self.ref_ty(m, elem)
            }
            Coerce::MutToShared | Coerce::Reborrow => {
                let m = self.ck.coerce(e) == Coerce::Reborrow;
                let inner = self.peel(ty, 1);
                self.ref_ty(m, inner)
            }
            Coerce::SliceFromArray(m) | Coerce::SliceFromVec(m) => {
                let mut inner = self.peel(ty, 1);
                if let Some(b) = self.slice_source_inner(inner) {
                    inner = b;
                }
                let elem = match self.kind(inner) {
                    TyKind::Array(el, _) => el,
                    _ => self.body.tys.vec_elem(inner).unwrap_or(ERROR),
                };
                let slice = self.body.tys.intern(TyKind::Slice(elem));
                self.ref_ty(m, slice)
            }
        }
    }

    /// The fn pointer type of `dest`, when it is a whole local of one.
    fn fn_ptr_dest(&self, dest: Option<&Place>) -> Option<Ty> {
        let d = dest.filter(|d| d.proj.is_empty())?;
        let dt = self.body.locals[d.local as usize].ty;
        matches!(self.kind(dt), TyKind::FnPtr(_)).then_some(dt)
    }

    /// Lowers a fn item value, or a closure value that captures
    /// nothing, to the fn pointer `target`: the zero-sized operand is
    /// read (for its side effects), then the slot trampoline of the
    /// item `found` names (its mono instance for a generic fn), or of
    /// the closure's body fn, is the value.
    fn reify_fn(&mut self, op: Operand, found: Ty, target: Ty, span: Span) -> Operand {
        let zst = self.temp(found);
        self.assign(Place::local(zst), Rvalue::Use(op), span);
        if let TyKind::Closure(def, _) = self.kind(found) {
            let f = self.p.gx.closures.get(&def).expect("ReifyFn names a checked closure").body_fn;
            let t = self.temp(target);
            self.assign(Place::local(t), Rvalue::FnValue(f, target), span);
            return Operand::Copy(Place::local(t));
        }
        let TyKind::FnDef(def, args) = self.kind(found) else { unreachable!("ReifyFn on a non fn item type") };
        // A constructor or primitive builtin method has no fn: codegen
        // writes one (`ItemShim`).
        let b = self.body.tys.builtins();
        if self.p.adt_by_def(def).is_some() || def == b.option || def == b.result || def == crate::ty::prim_fn_def() {
            let t = self.temp(target);
            self.assign(Place::local(t), Rvalue::ItemShim(found, target), span);
            return Operand::Copy(Place::local(t));
        }
        let f = self.p.local_def(def.hash).expect("ReifyFn names a local fn");
        let args = self.body.tys.args(args).to_vec();
        let f = if args.is_empty() { f } else { crate::check::generics::instance_for(self.p, &self.body.tys, f, &args).unwrap_or(f) };
        let t = self.temp(target);
        self.assign(Place::local(t), Rvalue::FnValue(f, target), span);
        Operand::Copy(Place::local(t))
    }

    /// Lowers an unsizing coercion (ARCH 2.8) of the reference `op` (of
    /// type `found`) to `target`, a dyn reference: a reborrow of the
    /// source at the target's mutability (so a `&mut` source stays
    /// usable after, as in rustc), then a new fat pointer for a thin
    /// source, or an upcast (or a plain copy, when only auto traits
    /// drop) for a dyn source.
    fn unsize(&mut self, op: Operand, found: Ty, target: Ty, span: Span) -> Operand {
        use crate::check::object;
        // An owning unsizing (`Box<T>` to `Box<dyn Tr>`, `Rc<T>` to
        // `Rc<dyn Tr>`): the box or Rc moves into the fat pointer.
        // `Weak<T>` to `Weak<dyn Tr>` the same way (cgen keeps a dangling Weak dangling).
        let elem = |tys: &crate::ty::Tys<'_>, t: Ty| tys.smart_elem(t).or_else(|| tys.weak_elem(t)).or_else(|| tys.arc_weak_elem(t));
        if let (Some(mut src), Some(mut dyn_ty)) = (elem(&self.body.tys, found), elem(&self.body.tys, target)) {
            // `Rc<RefCell<S>>` to `Rc<RefCell<dyn Tr>>`: the vtable is
            // the value's; the data still points at the cell.
            if let (Some(s), Some(d)) = (self.body.tys.refcell_elem(src), self.body.tys.refcell_elem(dyn_ty)) {
                (src, dyn_ty) = (s, d);
            } else if let (Some((_, s)), Some((_, d))) = (self.body.tys.lock_elem(src), self.body.tys.lock_elem(dyn_ty)) {
                (src, dyn_ty) = (s, d);
            }
            let rv = match (object::principal_of(&self.body.tys, src), object::principal_of(&self.body.tys, dyn_ty)) {
                (Some(from), Some(to)) => {
                    let path = object::upcast_path(self.p, &mut self.body.tys, from, to).unwrap_or_default();
                    if path.is_empty() { Rvalue::Use(op) } else { Rvalue::DynUpcast { ptr: op, path } }
                }
                // A dyn source to a dyn with only auto traits: the same
                // object type (check/mod.rs `auto_only_unsize`), a copy.
                _ if matches!(self.body.tys.kind(src), TyKind::Dyn(..)) => Rvalue::Use(op),
                _ => Rvalue::MakeDyn { ptr: op, src, dyn_ty },
            };
            let out = self.temp(target);
            self.assign(Place::local(out), rv, span);
            return Operand::Move(Place::local(out));
        }
        // A reference or thin raw pointer to a fat raw pointer (tf-fatptr):
        // the address plus the array length or the vtable.
        if let TyKind::RawPtr(_, to) = self.kind(target) {
            let src = match self.kind(found) {
                TyKind::Ref(_, _, s) | TyKind::RawPtr(_, s) => s,
                _ => unreachable!(),
            };
            let rv = match (object::principal_of(&self.body.tys, src), object::principal_of(&self.body.tys, to)) {
                (Some(from), Some(dst)) => {
                    let path = object::upcast_path(self.p, &mut self.body.tys, from, dst).unwrap_or_default();
                    if path.is_empty() { Rvalue::Use(op) } else { Rvalue::DynUpcast { ptr: op, path } }
                }
                _ if matches!(self.body.tys.kind(src), TyKind::Dyn(..)) => Rvalue::Use(op),
                _ => Rvalue::MakeDyn { ptr: op, src, dyn_ty: to },
            };
            let out = self.temp(target);
            self.assign(Place::local(out), rv, span);
            return Operand::Copy(Place::local(out));
        }
        let TyKind::Ref(_, tm, dyn_ty) = self.kind(target) else { unreachable!() };
        let m = tm.is_mut();
        let place = self.op_place(op, found, span);
        let src = self.peel(found, 1);
        let rt = self.ref_ty(m, src);
        let r = self.temp(rt);
        self.assign(Place::local(r), Rvalue::Ref(m, place.deref()), span);
        let ptr = if m { Operand::Move(Place::local(r)) } else { Operand::Copy(Place::local(r)) };
        let rv = match (object::principal_of(&self.body.tys, src), object::principal_of(&self.body.tys, dyn_ty)) {
            (Some(from), Some(to)) => {
                let path = object::upcast_path(self.p, &mut self.body.tys, from, to).unwrap_or_default();
                if path.is_empty() { Rvalue::Use(ptr) } else { Rvalue::DynUpcast { ptr, path } }
            }
            _ if matches!(self.body.tys.kind(src), TyKind::Dyn(..)) => Rvalue::Use(ptr),
            _ => Rvalue::MakeDyn { ptr, src, dyn_ty },
        };
        let out = self.temp(target);
        if m && matches!(rv, Rvalue::Use(_)) {
            self.body.dyn_coerce.push(out);
        }
        self.assign(Place::local(out), rv, span);
        if m { Operand::Move(Place::local(out)) } else { Operand::Copy(Place::local(out)) }
    }

    /// Points a dyn method call's receiver at the vtable of the trait
    /// that declares the method: unchanged for a principal method, an
    /// upcast along the super slots for a supertrait method.
    #[allow(clippy::too_many_arguments)]
    fn dyn_receiver(
        &mut self,
        recv: Operand,
        recv_dyn: Ty,
        mutable: bool,
        owner: DefId,
        cand: u8,
        name: crate::intern::Sym,
        span: Span,
    ) -> Operand {
        use crate::check::object;
        let Some(principal) = object::principal_of(&self.body.tys, recv_dyn) else { return recv };
        if principal.def == owner {
            return recv;
        }
        let cands = object::object_cands(self.p, &mut self.body.tys, principal, name);
        // Check resolved the call to this candidate, so the supertrait
        // and its slot path exist; a miss here would call the wrong
        // vtable.
        let Some(c) = cands.into_iter().nth(cand as usize).filter(|c| c.owner.def == owner) else { unreachable!() };
        let Some(path) = object::upcast_path(self.p, &mut self.body.tys, principal, c.owner) else { unreachable!() };
        let bounds = self.body.tys.intern_dyn_bounds(DynBounds {
            principal: Some(Binder::plain(c.owner)),
            supertraits: Box::new([]),
            auto: AutoTraits::default(),
        });
        let owner_dyn = self.body.tys.intern(TyKind::Dyn(bounds, Region::Erased));
        let rt = self.ref_ty(mutable, owner_dyn);
        let t = self.temp(rt);
        self.assign(Place::local(t), Rvalue::DynUpcast { ptr: recv, path }, span);
        if mutable { Operand::Move(Place::local(t)) } else { Operand::Copy(Place::local(t)) }
    }

    /// The user `Deref` steps check recorded for `e` (a method call's
    /// receiver, a field access base, or an explicit `*x`), applied to
    /// the place of `input`. None when `e` has no step.
    fn deref_steps(&mut self, e: ExprId, input: ExprId, span: Span) -> Option<Place> {
        let steps: Vec<crate::check::DerefRecv> = self.ck.deref_recv(e).into_iter().cloned().collect();
        let first = steps.first()?;
        let mutable = first.mutable || (first.f_mut.is_some() && self.mut_index > 0);
        let pl = if mutable { self.place_for_mut(input) } else { self.place(input) };
        let ty = self.ty(input);
        Some(self.apply_deref_steps(pl, ty, steps, span))
    }

    /// Applies user `Deref` steps outermost first to `start` (of type
    /// `start_ty`): borrow the step's input, call the impl's `deref`
    /// (or `deref_mut`: a step check fixed as mutable, or a place step
    /// under `place_for_mut`), and go on from the `&Target` it returns.
    /// Returns that last reference's place.
    fn apply_deref_steps(&mut self, start: Place, start_ty: Ty, steps: Vec<crate::check::DerefRecv>, span: Span) -> Place {
        let (mut root, mut root_ty) = (start, start_ty);
        for dr in steps {
            let place_mut = dr.f_mut.is_some() && self.mut_index > 0;
            let mutable = dr.mutable || place_mut;
            let base = Self::derefs(root, dr.before);
            let base_ty = self.peel(root_ty, dr.before);
            let rt = self.ref_ty(mutable, base_ty);
            let r = self.temp(rt);
            self.assign(Place::local(r), Rvalue::Ref(mutable, base), span);
            let (f, args) = match dr.f_mut {
                Some(g) if place_mut => (g, dr.args_mut.clone()),
                _ => (dr.f, dr.args.clone()),
            };
            let f = if args.is_empty() { f } else { crate::check::generics::instance_for(self.p, &self.body.tys, f, &args).unwrap_or(f) };
            let target = self.peel(dr.target_ref, 1);
            let tt = self.ref_ty(mutable, target);
            let t = self.temp(tt);
            let arg = if mutable { Operand::Move(Place::local(r)) } else { Operand::Copy(Place::local(r)) };
            self.call_into(CallTarget::Fn(f), vec![arg], Place::local(t), span);
            (root, root_ty) = (Place::local(t), tt);
        }
        root
    }

    fn op_place(&mut self, op: Operand, ty: Ty, span: Span) -> Place {
        match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            Operand::Const(c) => {
                let t = self.temp(ty);
                self.assign(Place::local(t), Rvalue::Use(Operand::Const(c)), span);
                Place::local(t)
            }
        }
    }

    fn operand_raw(&mut self, e: ExprId) -> Operand {
        if let Some(pl) = self.take_prelowered(e) {
            return Operand::Move(pl);
        }
        let ty = self.ty(e);
        match self.p.ast.expr(e) {
            Expr::Int(v, _) => match self.kind(ty) {
                TyKind::Int(it) => Operand::Const(Const::Int(*v, it)),
                _ => Operand::Const(Const::Int(*v, IntTy::I32)),
            },
            Expr::Float(i) => {
                let text = &self.p.ast.strings[*i as usize];
                let ft = match self.kind(ty) {
                    TyKind::Float(f) => f,
                    _ => FloatTy::F64,
                };
                // Parse straight to the literal's type: one rounding.
                match crate::check::collect::parse_float_literal_as(text, ft) {
                    Some(bits) => Operand::Const(Const::Float(bits, ft)),
                    None => Operand::Const(Const::Unit),
                }
            }
            Expr::Bool(b) => Operand::Const(Const::Bool(*b)),
            Expr::Char(c) => Operand::Const(Const::Char(*c)),
            Expr::Str(s) => Operand::Const(Const::Str(*s)),
            Expr::ByteStr(i) => Operand::Const(Const::Bytes(
                self.p.ast.blobs.get(*i as usize).cloned().unwrap_or_else(|| crate::ast::ByteBlob::new(Vec::new())),
            )),
            Expr::Unit => Operand::Const(Const::Unit),
            _ if self.is_place_expr(e) => {
                let p = self.place(e);
                // An index expression reads through the `Index` trait in
                // Rust, so moving its (non-Copy) value out, or a field
                // below it, is moving out of a reference and an error
                // (E0507/E0508). Route the read through a shared borrow
                // temporary so the borrow checker reports exactly that.
                // Pattern bindings project indexes directly and are not
                // affected (they do not come through here).
                let moved = self.view_moved(e);
                if p.proj.iter().any(|x| matches!(x, Proj::Index(_))) && (moved || !is_copy(self.p, &self.body.tys, ty)) {
                    let span = self.span(e);
                    let rt = self.ref_ty(false, ty);
                    let tmp = self.temp(rt);
                    self.assign(Place::local(tmp), Rvalue::Ref(false, p), span);
                    if moved {
                        return Operand::Move(Place::local(tmp).deref());
                    }
                    return self.operand_from(Place::local(tmp).deref(), ty);
                }
                if moved { Operand::Move(p) } else { self.operand_from(p, ty) }
            }
            _ => {
                let t = self.materialize(e, ty, true);
                Operand::Move(Place::local(t))
            }
        }
    }

    /// An operand for `e` after `n` implicit derefs.
    fn operand_derefs(&mut self, e: ExprId, n: u8) -> Operand {
        if n == 0 {
            return self.operand(e);
        }
        let p = self.place(e);
        let t = self.peel(self.ty(e), n);
        self.operand_from(Self::derefs(p, n), t)
    }

    /// A shared reference to the value of `e` (after `n` derefs). Used for format arguments and `==`.
    fn borrow_of(&mut self, e: ExprId, n: u8) -> (Operand, Ty) {
        let span = self.span(e);
        let p = self.place(e);
        let p = Self::derefs(p, n);
        let t = self.peel(self.ty(e), n);
        let rt = self.ref_ty(false, t);
        let tmp = self.temp(rt);
        self.assign(Place::local(tmp), Rvalue::Ref(false, p), span);
        (Operand::Copy(Place::local(tmp)), t)
    }

    // ---------- Expressions ----------

    /// Evaluates `e` and stores the result in `dest` (or drops it when `dest` is None).
    fn expr_into(&mut self, e: ExprId, dest: Option<&Place>) {
        if self.ck.coerce(e) != Coerce::None {
            let op = self.operand(e);
            match (dest, &op) {
                (Some(d), _) => self.assign(d.clone(), Rvalue::Use(op), self.span(e)),
                // An unused coerced value is still read, as rustc's
                // coercion runs (`if c { &v[0] } else { &&G };` reborrows
                // through the dropped `&G`, E0716).
                (None, Operand::Copy(pl) | Operand::Move(pl)) => self.push(StmtKind::FakeRead(pl.local), self.span(e)),
                (None, _) => {}
            }
            return;
        }
        self.expr_into_raw(e, dest);
    }

    /// Takes out the temporary `prelower_binary_spine` made for `e`,
    /// if it made one and the value has not been consumed yet.
    fn take_prelowered(&mut self, e: ExprId) -> Option<Place> {
        let i = self.prelowered.iter().rposition(|&(x, _, _)| x == e)?;
        Some(self.prelowered.swap_remove(i).1)
    }

    /// Lowers every node below `top` on the left spine of a binary
    /// chain (`a + b + c + ...`) into its own temporary, deepest
    /// first, and records them in `prelowered`. Evaluating the spine
    /// this way emits the same statements in the same order as the
    /// recursive walk (the left operand of every node is ready before
    /// its right operand runs), but the walk itself is a loop, so a
    /// 2000-term chain uses constant stack here. A node the checker
    /// const-evaluated stops the spine: it materializes directly in
    /// `expr_into_here` and nothing below it must run.
    /// Returns the run's generation for cleanup of leftovers.
    fn prelower_binary_spine(&mut self, top: ExprId) -> u32 {
        self.spine_gen += 1;
        let run = self.spine_gen;
        let mut spine: Vec<ExprId> = Vec::new();
        let mut cur = top;
        while let Expr::Binary { lhs, .. } = self.p.ast.expr(cur) {
            if self.ck.const_value(cur).is_some() {
                break;
            }
            spine.push(cur);
            cur = *lhs;
        }
        for i in (1..spine.len()).rev() {
            let node = spine[i];
            let pl = Place::local(self.temp(self.ty(node)));
            // The left side of `&&` or `||` is a terminating scope, as in
            // rustc (and `binary_into`): its temporaries drop right after it.
            let term = matches!(self.p.ast.expr(spine[i - 1]), Expr::Binary { op: BinOp::And | BinOp::Or, .. });
            if term {
                self.scopes.push(Vec::new());
            }
            self.expr_into_here(node, Some(&pl));
            if term {
                let span = self.span(node);
                self.pop_scope(span);
            }
            self.prelowered.push((node, pl, run));
        }
        run
    }

    fn expr_into_raw(&mut self, e: ExprId, dest: Option<&Place>) {
        if let Some(pl) = self.take_prelowered(e) {
            if let Some(d) = dest {
                let d = d.clone();
                let span = self.span(e);
                self.assign(d, Rvalue::Use(Operand::Move(pl)), span);
            }
            return;
        }
        if matches!(self.p.ast.expr(e), Expr::Binary { .. }) && self.ck.const_value(e).is_none() {
            let run = self.prelower_binary_spine(e);
            self.expr_into_here(e, dest);
            // Not every spine value is always consumed (a node below
            // a const-evaluated one, an error path): drop this run's
            // leftovers so a later use of the same expression (a
            // match guard row lowers its guard once per row) always
            // evaluates it fresh.
            self.prelowered.retain(|&(_, _, g)| g != run);
            return;
        }
        self.expr_into_here(e, dest);
        // A call of type `!` (`fn die() -> !`, `resume_unwind`) does not
        // return: rustc's MIR call has no return edge, so code after it
        // is dead (a value moved into the call is not "used after move").
        if matches!(self.p.ast.expr(e), Expr::Call { .. } | Expr::MethodCall { .. }) && self.diverges(e) {
            let span = self.span(e);
            self.terminate(Terminator::Unreachable, span);
        }
    }

    fn expr_into_here(&mut self, e: ExprId, dest: Option<&Place>) {
        let span = self.span(e);
        let p = self.p;
        let ty = self.ty(e);
        // A value the checker const-evaluated materializes directly.
        if self.as_code != Some(e)
            && let Some(cv) = self.ck.const_value(e).cloned()
        {
            if let Some(d) = dest {
                self.const_into(&cv, ty, d, span);
            }
            return;
        }
        match p.ast.expr(e) {
            Expr::Int(..) | Expr::Float(_) | Expr::Bool(_) | Expr::Char(_) | Expr::Str(_) | Expr::ByteStr(_) | Expr::Unit => {
                if let Some(d) = dest {
                    let op = self.operand_raw(e);
                    self.assign(d.clone(), Rvalue::Use(op), span);
                }
            }
            Expr::Path(_) | Expr::SelfValue => match self.ck.res(e) {
                Res::Local(_) => {
                    if let Some(d) = dest {
                        let pl = self.place(e);
                        let op = if self.view_moved(e) { Operand::Move(pl) } else { self.operand_from(pl, ty) };
                        self.assign(d.clone(), Rvalue::Use(op), span);
                    }
                }
                // A constructor (or primitive builtin method) written straight into a fn pointer place
                // (the first arm of a `match` whose arms join as a fn
                // pointer): its codegen fn, as for the reify coercion.
                Res::Variant(..) | Res::OptSome | Res::ResOk | Res::ResErr | Res::PrimAssoc { .. }
                    if matches!(self.kind(ty), TyKind::FnDef(..)) && let Some(dt) = self.fn_ptr_dest(dest) =>
                {
                    self.set_or_temp(dest, Rvalue::ItemShim(ty, dt), ty, span)
                }
                Res::Variant(a, v) => {
                    if matches!(self.kind(ty), TyKind::FnDef(..)) {
                        // A constructor used as a value: the value itself
                        // is zero-sized; calls through it decode the
                        // constructor from the type.
                        self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Unit)), ty, span)
                    } else {
                        self.aggregate_into(e, Rvalue::Aggregate(a, v, Vec::new()), dest, ty, span)
                    }
                }
                Res::Fn(f) => {
                    // A fn item used as a value: zero-sized at its FnDef
                    // type, the slot trampoline where a fn pointer goes.
                    // A generic fn names its mono instance.
                    let f = self.resolve_generic_fn(e, f);
                    let want = match dest {
                        Some(d) if d.proj.is_empty() => {
                            let dt = self.body.locals[d.local as usize].ty;
                            if matches!(self.kind(dt), TyKind::FnPtr(_)) { dt } else { ty }
                        }
                        _ => ty,
                    };
                    self.set_or_temp(dest, Rvalue::FnValue(f, want), ty, span)
                }
                // A static's value of a non-Copy type moves out of a
                // place reached through its address (`place`), which the
                // borrow checker rejects as a move out of a reference
                // (rustc E0507); a copy loads it.
                Res::Static(_) if !is_copy(self.p, &self.body.tys, ty) => {
                    let pl = self.place(e);
                    let op = self.operand_from(pl, ty);
                    match dest {
                        Some(d) => self.assign(d.clone(), Rvalue::Use(op), span),
                        None => {
                            let t = self.temp(ty);
                            self.assign(Place::local(t), Rvalue::Use(op), span);
                        }
                    }
                }
                Res::Static(idx) => self.set_or_temp(dest, Rvalue::StaticLoad(idx), ty, span),
                Res::OptNone => self.set_or_temp(dest, Rvalue::Opt(ty, None), ty, span),
                // `Some`, `Ok`, `Err`, `Box::new`, `Rc::new`, or
                // `String::from` used as a value (W-CHECK-G): a
                // zero-sized item, as for a user constructor above.
                Res::OptSome | Res::ResOk | Res::ResErr | Res::Builtin(_) | Res::PrimAssoc { .. } if matches!(self.kind(ty), TyKind::FnDef(..)) => {
                    self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Unit)), ty, span)
                }
                _ if self.is_trait_marker_value(ty) => self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Unit)), ty, span),
                _ => {}
            },
            Expr::Field { .. } | Expr::TupleField { .. } | Expr::Index { .. } | Expr::Deref(_) => {
                let pl = self.place(e);
                if let Some(d) = dest {
                    // Index reads go through the `Index` trait (see
                    // `operand_raw`): a non-Copy move out of a place
                    // below one is a move out of a reference.
                    let moved = self.view_moved(e);
                    let op = if pl.proj.iter().any(|x| matches!(x, Proj::Index(_))) && (moved || !is_copy(self.p, &self.body.tys, ty)) {
                        let rt = self.ref_ty(false, ty);
                        let tmp = self.temp(rt);
                        self.assign(Place::local(tmp), Rvalue::Ref(false, pl), span);
                        if moved { Operand::Move(Place::local(tmp).deref()) } else { self.operand_from(Place::local(tmp).deref(), ty) }
                    } else if moved {
                        Operand::Move(pl)
                    } else {
                        self.operand_from(pl, ty)
                    };
                    self.assign(d.clone(), Rvalue::Use(op), span);
                }
            }
            Expr::Block(b) => self.block_into(*b, dest),
            Expr::If { cond, then, els } if self.is_let_chain(*cond) => {
                let (eb, end) = (self.new_block(), self.new_block());
                self.scopes.push(Vec::new());
                self.cond_chain(*cond, eb, span);
                self.block_into(*then, dest);
                self.pop_scope(span);
                self.goto(end, span);
                self.cur = eb;
                if let Some(els) = els {
                    let reborrow = self.reborrows_arms(ty) && !self.block_diverges(*then);
                    self.arm_into(*els, reborrow, dest);
                } else if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Use(Operand::Const(Const::Unit)), span);
                }
                self.goto(end, span);
                self.cur = end;
            }
            Expr::If { cond, then, els } => {
                let cl = self.cond(*cond, span);
                let (tb, eb, end) = (self.new_block(), self.new_block(), self.new_block());
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::If(Operand::Copy(Place::local(cl)), tb, eb);
                b.term_span = span;
                self.cur = tb;
                self.block_into(*then, dest);
                self.goto(end, span);
                self.cur = eb;
                if let Some(els) = els {
                    let reborrow = self.reborrows_arms(ty) && !self.block_diverges(*then);
                    self.arm_into(*els, reborrow, dest);
                } else if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Use(Operand::Const(Const::Unit)), span);
                }
                self.goto(end, span);
            }
            Expr::While { label, cond, body } if self.is_let_chain(*cond) => {
                let (head, exit) = (self.new_block(), self.new_block());
                self.goto(head, span);
                self.scopes.push(Vec::new());
                self.cond_chain(*cond, exit, span);
                self.loops.push(LoopInfo {
                    break_bb: exit,
                    continue_bb: head,
                    dest: None,
                    depth: self.scopes.len() - 1,
                    label: label.map(|l| (l.name, l.span)),
                    is_block: false,
                });
                self.block_into(*body, None);
                self.loops.pop();
                self.pop_scope(span);
                self.goto(head, span);
                self.cur = exit;
                if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Use(Operand::Const(Const::Unit)), span);
                }
            }
            Expr::While { label, cond, body } => {
                let (head, bodyb, exit) = (self.new_block(), self.new_block(), self.new_block());
                self.goto(head, span);
                let cl = self.cond(*cond, span);
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::If(Operand::Copy(Place::local(cl)), bodyb, exit);
                b.term_span = span;
                self.cur = bodyb;
                self.loops.push(LoopInfo {
                    break_bb: exit,
                    continue_bb: head,
                    dest: None,
                    depth: self.scopes.len(),
                    label: label.map(|l| (l.name, l.span)),
                    is_block: false,
                });
                self.block_into(*body, None);
                self.loops.pop();
                self.goto(head, span);
                self.cur = exit;
                if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Use(Operand::Const(Const::Unit)), span);
                }
            }
            Expr::Loop { label, body } => {
                let (head, exit) = (self.new_block(), self.new_block());
                self.goto(head, span);
                self.loops.push(LoopInfo {
                    break_bb: exit,
                    continue_bb: head,
                    dest: dest.cloned(),
                    depth: self.scopes.len(),
                    label: label.map(|l| (l.name, l.span)),
                    is_block: false,
                });
                self.block_into(*body, None);
                self.loops.pop();
                self.goto(head, span);
                self.cur = exit;
            }
            Expr::For { label, pat, iter, body } => self.for_loop(e, *label, *pat, *iter, *body, span, dest),
            Expr::Match { scrut, arms } => self.match_into(*scrut, arms, dest, span),
            Expr::Call { callee, args } => {
                let res = self.ck.res(e);
                // Through a fn item shim (`Checked::fn_shim_calls`).
                let span = self.ck.fn_shim_span(e).unwrap_or(span);
                // A call through an Fn-family bound of a type parameter
                // (template checks), or through a `dyn Fn` value's
                // vtable: a method call with the callee as its receiver.
                // (A qualified path call through a dyn receiver,
                // `Tr::m(d)`, passes its receiver as an argument.)
                let dyn_fn_call = matches!(res, Res::DynMethod { owner, .. } if self.p.gx.lang.is_fn_family(owner));
                // A builtin method by path (`Vec::len(&v)`, check/ufcs.rs):
                // the method form with the first argument as the receiver.
                // Its callee is a type path with no resolution of its own.
                let by_path = matches!(self.p.ast.expr(*callee), Expr::Path(segs) if segs.len() >= 2) && self.ck.res(*callee) == Res::None;
                if let (Res::BuiltinMethod { .. } | Res::Method { .. }, true, [recv, rest @ ..]) = (res, by_path, args.as_slice()) {
                    self.method_into(e, *recv, rest, dest, span);
                    return;
                }
                if matches!(res, Res::Method { .. }) || dyn_fn_call {
                    self.method_into(e, *callee, args, dest, span);
                    return;
                }
                if let Res::ClosureCall { kind, derefs } = res {
                    self.closure_call(e, *callee, args, kind, derefs, dest, span);
                    return;
                }
                // `PartialEq::eq(a, b)` and kin at a builtin comparison:
                // the method form with `a` as the receiver.
                if let Res::PrimCmp { kind, derefs } = res
                    && let [recv, rest @ ..] = args.as_slice()
                {
                    self.prim_cmp_into(e, *recv, rest, dest, span, kind, derefs);
                    return;
                }
                // `Ord::max(a, b)` and kin by structure: the method form.
                if let Res::OrdPick { kind, f, via } = res
                    && let [recv, rest @ ..] = args.as_slice()
                {
                    let f = f.map(|f| self.resolve_generic_fn(e, f));
                    self.ord_pick_into(e, *recv, rest, dest, span, kind, f, via);
                    return;
                }
                // An indirect call reads the callee value before the
                // arguments run, as Rust evaluates the callee first.
                let indirect_local = if res == Res::Indirect {
                    let ct = self.ty(*callee);
                    let op = self.operand(*callee);
                    match op {
                        Operand::Copy(pl) | Operand::Move(pl) if pl.proj.is_empty() && matches!(self.kind(ct), TyKind::FnPtr(_)) => {
                            Some(pl.local)
                        }
                        Operand::Copy(pl) | Operand::Move(pl) => {
                            // A callee behind references or smart pointers
                            // (`&&f`, `Box<fn()>`) loads through them first,
                            // so the call local holds the fn pointer itself.
                            let (mut vt, mut fp) = (ct, pl.clone());
                            while !matches!(self.kind(vt), TyKind::FnPtr(_)) {
                                match self.kind(vt) {
                                    TyKind::Ref(_, _, inner) => vt = inner,
                                    _ => match self.body.tys.smart_elem(vt) {
                                        Some(inner) => vt = inner,
                                        None => break,
                                    },
                                }
                                fp = fp.deref();
                            }
                            let t = self.temp(vt);
                            let op2 = self.operand_from(fp, vt);
                            self.assign(Place::local(t), Rvalue::Use(op2), span);
                            // A temporary smart pointer callee (`Box::new(f)()`)
                            // is dropped once the pointer is read.
                            if pl.proj.is_empty() && !self.is_place_expr(*callee) && needs_drop(self.p, &self.body.tys, ct) {
                                self.push(StmtKind::Drop(pl.local), span);
                            }
                            Some(t)
                        }
                        Operand::Const(_) => None,
                    }
                } else {
                    None
                };
                // A fn item called through a value behind references or
                // smart pointers (`(&mut f)()`, `w()` with `w: Box<&&F>`):
                // the call does not read it, but rustc borrows it to
                // autoderef, so borrowck must see that use. A temporary
                // callee drops at once (it holds no destructor of note).
                if matches!(res, Res::Fn(_) | Res::Variant(..) | Res::Builtin(_) | Res::Intrinsic(_)) {
                    let ct = self.ty(*callee);
                    if matches!(self.kind(ct), TyKind::Ref(..)) || self.body.tys.smart_elem(ct).is_some() {
                        if self.is_place_expr(*callee) {
                            // A `Copy` callee (`&&f`) is read, which a
                            // closure body can do to a captured reference;
                            // an owned one (`Box<&f>`, `&mut f`) is borrowed.
                            let pl = self.place(*callee);
                            if is_copy(self.p, &self.body.tys, ct) {
                                let t = self.temp(ct);
                                self.assign(Place::local(t), Rvalue::Use(Operand::Copy(pl)), span);
                            } else {
                                let rt = self.ref_ty(false, ct);
                                let t = self.temp(rt);
                                self.assign(Place::local(t), Rvalue::Ref(false, pl), span);
                            }
                        } else {
                            let op = self.operand(*callee);
                            let t = self.temp(ct);
                            self.assign(Place::local(t), Rvalue::Use(op), span);
                            if needs_drop(self.p, &self.body.tys, ct) {
                                self.push(StmtKind::Drop(t), span);
                            }
                        }
                    }
                }
                let ops: Vec<Operand> = match res {
                    Res::Fn(_) | Res::Indirect => self.call_arg_operands(args, span),
                    _ => self.ordered_operands(args),
                };
                match res {
                    Res::Fn(f) => {
                        let f = self.resolve_generic_fn(e, f);
                        let d = self.call_dest(dest, ty);
                        self.call_into(CallTarget::Fn(f), ops, d, span);
                    }
                    Res::Intrinsic(id) => {
                        let d = self.call_dest(dest, ty);
                        self.call_into(CallTarget::Intrinsic(id), ops, d, span);
                    }
                    Res::Builtin(Builtin::VecNew) => self.set_or_temp(dest, Rvalue::VecLit(self.peel_vec(ty), Vec::new()), ty, span),
                    // `Rc::new_uninit()` is `Rc::new(MaybeUninit::uninit())`
                    // (the same for `Arc`): the shared header comes from
                    // the plain form.
                    Res::Builtin(b @ (Builtin::RcNewUninit | Builtin::ArcNewUninit)) => {
                        let mu = self.body.tys.rc_elem(ty).expect("an Rc or Arc result");
                        let new = if b == Builtin::RcNewUninit { Builtin::RcNew } else { Builtin::Sync(crate::check::sync::SyncOp::ArcNew) };
                        let t = self.temp(mu);
                        self.call_into(CallTarget::Builtin(Builtin::MaybeUninitUninit), ops, Place::local(t), span);
                        let d = self.call_dest(dest, ty);
                        self.call_into(CallTarget::Builtin(new), vec![Operand::Move(Place::local(t))], d, span);
                    }
                    Res::Builtin(Builtin::VecWithCapacity) => {
                        // An empty Vec in a temporary, an exact
                        // reserve on it, then a move to the dest:
                        // the requested capacity is observable
                        // through `capacity()`, so it cannot be
                        // dropped, and the dest place itself need
                        // not be mutable.
                        let tv = self.temp(ty);
                        self.assign(Place::local(tv), Rvalue::VecLit(self.peel_vec(ty), Vec::new()), span);
                        let rt = self.ref_ty(true, ty);
                        let r = self.temp(rt);
                        self.assign(Place::local(r), Rvalue::Ref(true, Place::local(tv)), span);
                        let u = self.temp(UNIT);
                        self.call_into(
                            CallTarget::Builtin(Builtin::VecReserveExact),
                            vec![Operand::Move(Place::local(r)), ops.into_iter().next().unwrap()],
                            Place::local(u),
                            span,
                        );
                        self.set_or_temp(dest, Rvalue::Use(Operand::Move(Place::local(tv))), ty, span);
                    }
                    Res::Builtin(Builtin::MemTake) => {
                        // Check limited `take` to types whose `Default`
                        // value is one of the forms below (or the
                        // default glue): fill a slot with it, then
                        // byte-replace.
                        let slot = self.temp(ty);
                        match self.kind(ty) {
                            TyKind::Int(it) => self.assign(Place::local(slot), Rvalue::Use(Operand::Const(Const::Int(0, it))), span),
                            TyKind::Float(f) => self.assign(Place::local(slot), Rvalue::Use(Operand::Const(Const::Float(0, f))), span),
                            TyKind::Bool => self.assign(Place::local(slot), Rvalue::Use(Operand::Const(Const::Bool(false))), span),
                            TyKind::Char => self.assign(Place::local(slot), Rvalue::Use(Operand::Const(Const::Char('\0'))), span),
                            TyKind::Unit => self.assign(Place::local(slot), Rvalue::Use(Operand::Const(Const::Unit)), span),
                            _ if self.body.tys.is_string_ty(ty) => {
                                self.call_into(CallTarget::Builtin(Builtin::StringNew), Vec::new(), Place::local(slot), span)
                            }
                            _ if self.body.tys.vec_elem(ty).is_some() => {
                                self.assign(Place::local(slot), Rvalue::VecLit(self.peel_vec(ty), Vec::new()), span)
                            }
                            _ if self.body.tys.option_elem(ty).is_some() => self.assign(Place::local(slot), Rvalue::Opt(ty, None), span),
                            // Every other type the checker allowed has
                            // its value in the default glue.
                            _ => self.call_into(CallTarget::Builtin(Builtin::DefaultGlue), Vec::new(), Place::local(slot), span),
                        }
                        let fill = self.operand_from(Place::local(slot), ty);
                        let mut ops = ops;
                        ops.push(fill);
                        let d = self.call_dest(dest, ty);
                        self.call_into(CallTarget::Builtin(Builtin::MemReplace), ops, d, span);
                    }
                    Res::Builtin(Builtin::Sync(
                        op @ (crate::check::sync::SyncOp::CatchUnwind
                        | crate::check::sync::SyncOp::ResumeUnwind
                        | crate::check::sync::SyncOp::PanicAny),
                    )) => self.unwind_call(op, args, ops, dest, ty, span),
                    Res::Builtin(Builtin::NonZeroNew) => {
                        // `NonZero::new(x)` (TRIAGE T5): None for
                        // zero, else Some of the aggregate.
                        let nz_ty = self.body.tys.option_elem(ty).unwrap_or(ty);
                        match (self.body.tys.local_adt(nz_ty), ops.into_iter().next()) {
                            (Some(a), Some(op)) => {
                                let inner = self.body.tys.adt_first_ty_arg(nz_ty).unwrap_or(nz_ty);
                                let it = match self.kind(inner) {
                                    TyKind::Int(i) => i,
                                    _ => IntTy::U64,
                                };
                                let xv = self.temp(inner);
                                self.assign(Place::local(xv), Rvalue::Use(op), span);
                                let c = self.temp(BOOL);
                                self.assign(
                                    Place::local(c),
                                    Rvalue::Bin(crate::ast::BinOp::Ne, Operand::Copy(Place::local(xv)), Operand::Const(Const::Int(0, it))),
                                    span,
                                );
                                let out = self.temp(ty);
                                let (tb, eb, end) = (self.new_block(), self.new_block(), self.new_block());
                                let b = &mut self.body.blocks[self.cur.0 as usize];
                                b.term = Terminator::If(Operand::Copy(Place::local(c)), tb, eb);
                                b.term_span = span;
                                self.cur = tb;
                                let t = self.temp(nz_ty);
                                self.assign(Place::local(t), Rvalue::Aggregate(a, 0, vec![Operand::Move(Place::local(xv))]), span);
                                self.assign(Place::local(out), Rvalue::Opt(ty, Some(Operand::Move(Place::local(t)))), span);
                                self.goto(end, span);
                                self.cur = eb;
                                self.assign(Place::local(out), Rvalue::Opt(ty, None), span);
                                self.goto(end, span);
                                self.cur = end;
                                self.set_or_temp(dest, Rvalue::Use(Operand::Move(Place::local(out))), ty, span);
                            }
                            _ => {}
                        }
                    }
                    Res::Builtin(b) => {
                        let d = self.call_dest(dest, ty);
                        self.call_into(CallTarget::Builtin(b), ops, d, span);
                    }
                    Res::PrimAssoc { b: Builtin::PrimFromCast, .. } => {
                        // A primitive `T::from(x)` widening: the
                        // same cast as `x.into()` to a scalar.
                        match ops.into_iter().next() {
                            Some(op) => self.set_or_temp(dest, Rvalue::Cast(op, ty), ty, span),
                            None => {}
                        }
                    }
                    Res::PrimAssoc { b, .. } => {
                        let d = self.call_dest(dest, ty);
                        self.call_into(CallTarget::Builtin(b), ops, d, span);
                    }
                    Res::Variant(a, v) => self.aggregate_into(e, Rvalue::Aggregate(a, v, ops), dest, ty, span),
                    Res::ConstUsize(v) => {
                        self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Int(v as u128, IntTy::Usize))), ty, span)
                    }
                    Res::Any { op, .. } if op == crate::check::any::AnyOp::TypeName => self.type_name_into(e, dest, ty, span),
                    Res::Any { .. } => self.type_id_of_into(e, dest, ty, span),
                    Res::ConstBool(b) => self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Bool(b))), ty, span),
                    Res::SizeOfVal { len, elem } => {
                        if elem == 1 {
                            let d = self.call_dest(dest, ty);
                            self.call_into(CallTarget::Builtin(len), ops, d, span);
                        } else {
                            let t = self.temp(ty);
                            self.call_into(CallTarget::Builtin(len), ops, Place::local(t), span);
                            self.set_or_temp(
                                dest,
                                Rvalue::Bin(
                                    BinOp::Mul,
                                    Operand::Copy(Place::local(t)),
                                    Operand::Const(Const::Int(elem as u128, IntTy::Usize)),
                                ),
                                ty,
                                span,
                            );
                        }
                    }
                    // Only reads the vtable, so a `&mut dyn` argument is
                    // reborrowed, not moved, as rustc's `&mut` to `&` is.
                    Res::DynMeta(word) => {
                        let ptr = match ops.into_iter().next().unwrap() {
                            Operand::Move(pl) => Operand::Copy(pl),
                            o => o,
                        };
                        self.set_or_temp(dest, Rvalue::DynMeta { ptr, word }, ty, span)
                    }
                    Res::FromCast => self.set_or_temp(dest, Rvalue::Cast(ops.into_iter().next().unwrap(), ty), ty, span),
                    Res::TryFromCast => {
                        let src_ty = self.ty(args[0]);
                        self.try_cast_into(ops.into_iter().next().unwrap(), src_ty, ty, dest, span)
                    }
                    Res::TryFromOk(f) => {
                        // `Ok(From::from(x))`, or `Ok(x)` for identity.
                        let op = ops.into_iter().next().unwrap();
                        let (ok_ty, _) = self.body.tys.result_args(ty).unwrap_or((UNIT, UNIT));
                        let ok_op = match f {
                            Some(f) => {
                                let f = self.resolve_generic_fn(e, f);
                                let t = self.temp(ok_ty);
                                self.call_into(CallTarget::Fn(f), vec![op], Place::local(t), span);
                                Operand::Move(Place::local(t))
                            }
                            None => op,
                        };
                        self.set_or_temp(dest, Rvalue::Res(ty, true, ok_op), ty, span)
                    }
                    Res::DefaultVal => {
                        let zero = match self.kind(ty) {
                            TyKind::Int(it) => Const::Int(0, it),
                            TyKind::Bool => Const::Bool(false),
                            TyKind::Char => Const::Char('\0'),
                            TyKind::Unit => Const::Unit,
                            // Other types build their default value in
                            // the `default` glue, typed by the call's
                            // destination.
                            _ => {
                                let d = self.call_dest(dest, ty);
                                self.call_into(CallTarget::Builtin(Builtin::DefaultGlue), Vec::new(), d, span);
                                return;
                            }
                        };
                        self.set_or_temp(dest, Rvalue::Use(Operand::Const(zero)), ty, span)
                    }
                    Res::OptSome => self.set_or_temp(dest, Rvalue::Opt(ty, ops.into_iter().next()), ty, span),
                    Res::Indirect => {
                        if let Some(l) = indirect_local {
                            let d = self.call_dest(dest, ty);
                            self.call_into(CallTarget::Indirect(l), ops, d, span);
                        }
                    }
                    Res::ResOk => {
                        let op = ops.into_iter().next().unwrap_or(Operand::Const(crate::ir::Const::Unit));
                        self.set_or_temp(dest, Rvalue::Res(ty, true, op), ty, span)
                    }
                    Res::ResErr => {
                        let op = ops.into_iter().next().unwrap_or(Operand::Const(crate::ir::Const::Unit));
                        self.set_or_temp(dest, Rvalue::Res(ty, false, op), ty, span)
                    }
                    // `<dyn P as Tr>::m(d, ..)`, `<dyn P>::m(d, ..)`, and
                    // `Tr::m(d, ..)`: the receiver is the first argument,
                    // already a dyn reference.
                    Res::DynMethod { owner, cand, slot, .. } => {
                        let Expr::Call { callee, .. } = p.ast.expr(e) else { unreachable!() };
                        let name = match p.ast.expr(*callee) {
                            Expr::QPath { segs, .. } | Expr::Path(segs) => segs[segs.len() - 1].name,
                            _ => unreachable!(),
                        };
                        let mut ops = ops;
                        let recv_ty = self.coerced_ty(args[0]);
                        let (m, recv_dyn) = match self.kind(recv_ty) {
                            TyKind::Ref(_, m, inner) => (m.is_mut(), inner),
                            _ => unreachable!(),
                        };
                        let r = ops.remove(0);
                        let r = self.dyn_receiver(r, recv_dyn, m, owner, cand, name, span);
                        ops.insert(0, r);
                        let t = self.temp(ty);
                        self.call_into(CallTarget::Dyn(slot), ops, Place::local(t), span);
                        if let Some(d) = dest {
                            let o = self.operand_from(Place::local(t), ty);
                            self.assign(d.clone(), Rvalue::Use(o), span);
                        }
                    }
                    _ => return,
                }
            }
            Expr::MethodCall { recv, args, .. } => self.method_into(e, *recv, args, dest, span),
            Expr::Binary { op, lhs, rhs } => self.binary_into(e, *op, *lhs, *rhs, dest, span),
            Expr::Unary { op, expr } => {
                // A negated integer literal is one literal, not a runtime negate:
                // folding it is what makes `-128i8` (and the other MIN values) work.
                if *op == crate::ast::UnOp::Neg
                    && let Expr::Int(v, _) = p.ast.expr(*expr)
                    && let TyKind::Int(it) = self.kind(ty)
                {
                    if let Some(d) = dest {
                        self.assign(d.clone(), Rvalue::Use(Operand::Const(Const::Int(v.wrapping_neg(), it))), span);
                    }
                    return;
                }
                if let Res::TraitBin { f, ld, .. } = self.ck.res(e) {
                    let f = self.resolve_generic_fn(e, f);
                    let o = self.operand_derefs(*expr, ld);
                    let d = self.call_dest(dest, ty);
                    self.call_into(CallTarget::Fn(f), vec![o], d, span);
                    return;
                }
                let ld = match self.ck.res(e) {
                    Res::Bin { ld, .. } => ld,
                    _ => 0,
                };
                let o = self.operand_derefs(*expr, ld);
                // `-&x` runs core's `impl Neg for &i32` (forward_ref_unop!,
                // not track_caller): its overflow reports core's arith.rs.
                let span = if *op == crate::ast::UnOp::Neg && ld > 0 && matches!(self.kind(ty), TyKind::Int(_)) {
                    Span::std_site(11, 728, 1)
                } else {
                    span
                };
                if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Un(*op, o), span);
                } else {
                    let t = self.temp(ty);
                    self.assign(Place::local(t), Rvalue::Un(*op, o), span);
                }
            }
            Expr::Cast { expr, .. } => {
                let o = self.operand(*expr);
                // A target that names a lifetime: the value goes through a
                // temporary whose regions are the written ones (W-BORROW).
                if let Some(&(_, r)) = self.ck.cast_annotations.iter().find(|(c, _)| *c == e) {
                    let rv = if matches!(self.kind(ty), TyKind::FnPtr(_) | TyKind::Ref(..)) { Rvalue::Use(o) } else { Rvalue::Cast(o, ty) };
                    let t = self.temp(ty);
                    self.assign(Place::local(t), rv, span);
                    self.body.annotations.push((t, r));
                    if let Some(d) = dest {
                        self.assign(d.clone(), Rvalue::Use(Operand::Move(Place::local(t))), span);
                    }
                    return;
                }
                if let Some(d) = dest {
                    // A cast to a fn pointer already holds the pointer
                    // value (the coercion on the inner expression made
                    // the trampoline, or it was a fn pointer already).
                    // A reference cast is the same: the coercion on the
                    // inner expression already built the target value.
                    if matches!(self.kind(ty), TyKind::FnPtr(_) | TyKind::Ref(..)) {
                        self.assign(d.clone(), Rvalue::Use(o), span);
                    } else {
                        self.assign(d.clone(), Rvalue::Cast(o, ty), span);
                    }
                }
            }
            Expr::Ref { mutable, expr, .. } => {
                // `&[]` and `&mut []` are promoted to `'static`, as in rustc:
                // the empty array has no bytes, so a temporary that never
                // dies serves, and it makes no loan (`Body::promoted`).
                if match p.ast.expr(*expr) {
                    Expr::Array(elems) => elems.is_empty(),
                    Expr::ByteStr(i) => p.ast.blobs.get(*i as usize).is_some_and(|b| b.is_empty()),
                    _ => false,
                } {
                    let at = self.ty(*expr);
                    let t = self.promoted_temp(at);
                    self.assign(Place::local(t), Rvalue::ArrayAgg(at, Vec::new()), span);
                    if let Some(d) = dest {
                        self.assign(d.clone(), Rvalue::Ref(*mutable, Place::local(t)), span);
                    }
                    return;
                }
                // `&|n| n - 1`: a shared borrow of a closure that captures
                // nothing is promoted too (rustc promotes the constant
                // value; the env is empty).
                if !*mutable
                    && matches!(p.ast.expr(*expr), Expr::Closure { .. })
                    && self.ck.closures.iter().any(|c| c.expr == *expr && c.captures.is_empty())
                {
                    let ct = self.ty(*expr);
                    let t = self.promoted_temp(ct);
                    self.closure_value(*expr, Some(&Place::local(t)), span);
                    if let Some(d) = dest {
                        self.assign(d.clone(), Rvalue::Ref(false, Place::local(t)), span);
                    }
                    return;
                }
                if let Res::Static(idx) = self.ck.res(*expr) {
                    if let Some(d) = dest {
                        self.assign(d.clone(), Rvalue::StaticRef(idx), span);
                    }
                    return;
                }
                // Constant promotion (rustc's rvalue static promotion):
                // `&5`, `&CONST`, `&None`, `&(1, 'a')` borrow a value that
                // is `'static`. The temporary is promoted (no loan, static
                // storage in cgen) and holds the same constant each time.
                if !*mutable && self.promotable(*expr) {
                    let at = self.ty(*expr);
                    let t = self.promoted_temp(at);
                    self.expr_into(*expr, Some(&Place::local(t)));
                    if let Some(d) = dest {
                        self.assign(d.clone(), Rvalue::Ref(false, Place::local(t)), span);
                    }
                    return;
                }
                if matches!(self.ck.res(*expr), Res::SliceIndex { .. }) {
                    // A slice place is already a fat value in a temporary;
                    // taking its reference moves that value (with its loan),
                    // it does not borrow the temporary.
                    let pl = if *mutable { self.place_for_mut(*expr) } else { self.place(*expr) };
                    if let Some(d) = dest {
                        let op = self.operand_from(pl, ty);
                        self.assign(d.clone(), Rvalue::Use(op), span);
                    }
                    return;
                }
                let pl = if *mutable { self.place_for_mut(*expr) } else { self.place(*expr) };
                if let Some(d) = dest {
                    self.assign(d.clone(), Rvalue::Ref(*mutable, pl), span);
                }
            }
            Expr::Assign { lhs, rhs } => {
                if self.is_destr_assign(*lhs) {
                    // Destructuring assignment, in rustc's desugared
                    // order: evaluate the right-hand side once, move
                    // each written element into a binding temporary in
                    // target order, drop what remains of a temporary
                    // scrutinee, then write each target in order (its
                    // place evaluates just before its own write, so a
                    // swap reads both old values). A scrutinee that is
                    // a place rooted in a local binds out of that place
                    // as in a `let`: elements the target discards stay
                    // in it and drop with its owner, they do not drop
                    // here. Any other scrutinee (a value, or a place
                    // rooted in a value such as `make().pair`) holds
                    // its storage in a temporary local, and dropping
                    // that root after the moves drops exactly the
                    // discarded and rest elements, plus any ancestors
                    // outside the matched projection, before the first
                    // target place evaluates.
                    let rt = self.ty(*rhs);
                    let owned = self.ck.coerce(*rhs) == Coerce::None && self.is_place_expr(*rhs) && self.place_root_owned(*rhs);
                    let src = if self.ck.coerce(*rhs) == Coerce::None {
                        let pl = self.place(*rhs);
                        self.assign_pattern_place(pl, rt, *lhs, span)
                    } else {
                        let tmp = Place::local(self.temp(rt));
                        self.expr_into(*rhs, Some(&tmp));
                        tmp
                    };
                    let mut writes = Vec::new();
                    self.collect_assign_pattern(*lhs, src.clone(), rt, span, &mut writes);
                    if !owned {
                        let root_ty = self.body.locals[src.local as usize].ty;
                        if needs_drop(self.p, &self.body.tys, root_ty) {
                            self.push(StmtKind::Drop(src.local), span);
                        }
                    }
                    for (target, src, ety) in writes {
                        let pl = self.place_for_mut(target);
                        let op = self.operand_from(src, ety);
                        self.assign(pl, Rvalue::Use(op), span);
                    }
                    self.unit(dest, span);
                    return;
                }
                let o = self.operand(*rhs);
                let pl = self.place_for_mut(*lhs);
                self.assign(pl, Rvalue::Use(o), span);
                self.unit(dest, span);
            }
            Expr::AssignOp { op, lhs, rhs } => {
                let lt = self.ty(*lhs);
                if let Res::TraitBin { f, rd, .. } = self.ck.res(e) {
                    // Through the assignment trait: `add_assign(&mut place, rhs)`.
                    let f = self.resolve_generic_fn(e, f);
                    let r = self.operand_derefs(*rhs, rd);
                    let pl = self.place_for_mut(*lhs);
                    let mt = self.ref_ty(true, lt);
                    let t = self.temp(mt);
                    self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
                    let u = self.temp(UNIT);
                    self.call_into(CallTarget::Fn(f), vec![Operand::Move(Place::local(t)), r], Place::local(u), span);
                    self.unit(dest, span);
                    return;
                }
                if self.body.tys.is_string_ty(lt) {
                    let pl = self.place_for_mut(*lhs);
                    let r = self.operand(*rhs);
                    let mt = self.ref_ty(true, STRING);
                    let t = self.temp(mt);
                    self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
                    let u = self.temp(UNIT);
                    self.call_into(
                        CallTarget::Builtin(Builtin::StringPushStr),
                        vec![Operand::Move(Place::local(t)), r],
                        Place::local(u),
                        span,
                    );
                } else if crate::check::collect::cow_arg(&self.body.tys, lt).is_some() {
                    let pl = self.place_for_mut(*lhs);
                    let r = self.cow_add_rhs(*rhs, span);
                    let mt = self.ref_ty(true, lt);
                    let t = self.temp(mt);
                    self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
                    let u = self.temp(UNIT);
                    self.call_into(
                        CallTarget::Builtin(Builtin::CowAddAssignStr),
                        vec![Operand::Move(Place::local(t)), r],
                        Place::local(u),
                        span,
                    );
                } else {
                    let rd = match self.ck.res(e) {
                        Res::Bin { rd, .. } => rd,
                        _ => 0,
                    };
                    let r = self.operand_derefs(*rhs, rd);
                    let pl = self.place_for_mut(*lhs);
                    self.assign(pl.clone(), Rvalue::Bin(*op, Operand::Copy(pl), r), span);
                }
                self.unit(dest, span);
            }
            Expr::StructLit { fields, update, .. } => {
                let Res::Variant(a, v) = self.ck.res(e) else { return };
                let n = p.adt(a).variants[v as usize].fields.len();
                let mut ops: Vec<Option<Operand>> = vec![None; n];
                for &(fname, _, fe) in fields {
                    let i = p.adt(a).variants[v as usize].fields.iter().position(|f| f.name == fname).unwrap();
                    // Field values are evaluated in written order, then moved into the struct.
                    let o = self.operand(fe);
                    let fresh_temp =
                        matches!(&o, Operand::Move(p) if p.proj.is_empty() && self.body.locals[p.local as usize].name.is_none());
                    let o = match o {
                        Operand::Const(_) => o,
                        _ if fresh_temp => o,
                        _ => {
                            let ft = self.coerced_ty(fe);
                            let t = self.temp(ft);
                            self.assign(Place::local(t), Rvalue::Use(o), span);
                            self.operand_from(Place::local(t), ft)
                        }
                    };
                    ops[i] = Some(o);
                }
                if let Some(u) = update {
                    // The base is evaluated after the written fields, and the
                    // fields not written move out of it.
                    let base = self.place(*u);
                    for (i, slot) in ops.iter_mut().enumerate() {
                        if slot.is_none() {
                            let ft = p.adt(a).variants[v as usize].fields[i].ty;
                            *slot = Some(self.operand_from(base.project(Proj::Field(i as u32)), ft));
                        }
                    }
                }
                let ops = ops.into_iter().map(|o| o.unwrap()).collect();
                self.aggregate_into(e, Rvalue::Aggregate(a, v, ops), dest, ty, span);
            }
            // A range value (check/iter.rs): the std struct's fields,
            // `start`, `end`, and `exhausted` for the inclusive form;
            // the open-ended forms store their one bound (a dummy
            // `false` for `RangeFull`).
            Expr::Range { lo, hi, inclusive } => {
                let ty = self.ty(e);
                let ops = match (lo, hi) {
                    (Some(lo), Some(hi)) => {
                        let mut ops = vec![self.operand(*lo), self.operand(*hi)];
                        if *inclusive {
                            ops.push(Operand::Const(Const::Bool(false)));
                        }
                        ops
                    }
                    (Some(b), None) | (None, Some(b)) => vec![self.operand(*b)],
                    (None, None) => vec![Operand::Const(Const::Bool(false))],
                };
                self.set_or_temp(dest, Rvalue::TupleAgg(ty, ops), ty, span);
            }
            Expr::Break { label, value: val } => {
                let ti = match label {
                    None => self.loops.len() - 1,
                    Some(l) => self
                        .loops
                        .iter()
                        .rposition(|lp| lp.label.is_some_and(|(n, bs)| n == l.name && crate::diag::ctxt_can_see_local(l.span.ctxt, bs)))
                        .unwrap_or(self.loops.len() - 1),
                };
                let li = &self.loops[ti];
                let (bb, depth, ld) = (li.break_bb, li.depth, li.dest.clone());
                if let Some(v) = val {
                    self.expr_into(*v, ld.as_ref());
                }
                self.exit_to(depth, span);
                self.terminate(Terminator::Goto(bb), span);
            }
            Expr::Continue(label) => {
                let ti = match label {
                    None => self.loops.iter().rposition(|lp| !lp.is_block).unwrap_or(self.loops.len() - 1),
                    Some(l) => self
                        .loops
                        .iter()
                        .rposition(|lp| lp.label.is_some_and(|(n, bs)| n == l.name && crate::diag::ctxt_can_see_local(l.span.ctxt, bs)))
                        .unwrap_or(self.loops.len() - 1),
                };
                let li = &self.loops[ti];
                let (bb, depth) = (li.continue_bb, li.depth);
                self.exit_to(depth, span);
                self.terminate(Terminator::Goto(bb), span);
            }
            Expr::Return(val) => {
                match val {
                    Some(v) => self.expr_into(*v, Some(&Place::local(0))),
                    None => self.assign(Place::local(0), Rvalue::Use(Operand::Const(Const::Unit)), span),
                }
                self.exit_to(0, span);
                self.terminate(Terminator::Return, span);
            }
            Expr::LabeledBlock { label, body } => {
                let exit = self.new_block();
                self.loops.push(LoopInfo {
                    break_bb: exit,
                    continue_bb: exit,
                    dest: dest.cloned(),
                    depth: self.scopes.len(),
                    label: Some((label.name, label.span)),
                    is_block: true,
                });
                self.block_into(*body, dest);
                self.loops.pop();
                self.goto(exit, span);
            }
            Expr::Macro { kind, args, fmt, repeat } => self.macro_into(e, *kind, args, fmt, *repeat, dest, ty, span),
            Expr::Tuple(elems) => {
                let ops: Vec<Operand> = self.ordered_operands(elems);
                self.set_or_temp(dest, Rvalue::TupleAgg(ty, ops), ty, span);
            }
            Expr::Array(elems) => {
                let ops: Vec<Operand> = self.ordered_operands(elems);
                self.set_or_temp(dest, Rvalue::ArrayAgg(ty, ops), ty, span);
            }
            Expr::ArrayRepeat { value, .. } => {
                let n = match self.kind(ty) {
                    TyKind::Array(_, c) => match self.body.tys.const_kind(c) {
                        ConstKind::Int(n) => n as u64,
                        // A template's const param length: lower the element
                        // so the borrow checker sees it (templates get no code).
                        ConstKind::Param(_) => 2,
                        _ => 0,
                    },
                    _ => 0,
                };
                if let Some(cv) = self.ck.const_value(*value).cloned()
                    && self.check_only()
                    && n > 1
                {
                    // A body only borrowck reads (a const initializer):
                    // one element value stands for every slot, so a long
                    // table (`[const { OnceLock::new() }; 1 << 20]`)
                    // lowers in one statement.
                    let elem = match self.kind(ty) {
                        TyKind::Array(el, _) => el,
                        _ => self.ty(*value),
                    };
                    let t = self.temp(elem);
                    self.const_into(&cv, elem, &Place::local(t), span);
                    self.set_or_temp(dest, Rvalue::ArrayRepeat(ty, Operand::Move(Place::local(t)), n), ty, span);
                    return;
                }
                if let Some(cv) = self.ck.const_value(*value).cloned() {
                    // A const element (`[const { .. }; n]`) materializes per slot.
                    let rv = crate::ty::consteval::ConstValue::Repeat(Box::new(cv), n);
                    match dest {
                        Some(d) => self.const_into(&rv, ty, d, span),
                        None => {
                            let t = self.temp(ty);
                            self.const_into(&rv, ty, &Place::local(t), span);
                        }
                    }
                    return;
                }
                if n == 0 {
                    // A zero repeat still evaluates its operand once
                    // and drops it (and moves a local in): materialize
                    // it into a statement temporary, which the scope
                    // drops at the end of the statement.
                    let elem = match self.kind(ty) {
                        TyKind::Array(el, _) => el,
                        _ => self.ty(*value),
                    };
                    let _ = self.materialize(*value, elem, false);
                    self.set_or_temp(dest, Rvalue::ArrayAgg(ty, Vec::new()), ty, span);
                } else if n == 1 {
                    let o = self.operand(*value);
                    self.set_or_temp(dest, Rvalue::ArrayAgg(ty, vec![o]), ty, span);
                } else {
                    let o = self.operand(*value);
                    self.set_or_temp(dest, Rvalue::ArrayRepeat(ty, o, n), ty, span);
                }
            }
            Expr::OffsetOf { .. } => {
                if let Res::ConstUsize(v) = self.ck.res(e) {
                    self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Int(v as u128, IntTy::Usize))), ty, span);
                }
            }
            Expr::Closure { .. } => self.closure_value(e, dest, span),
            Expr::Try(inner) => self.try_into(e, *inner, dest, ty, span),
            // AST v2 expression forms the parser still rejects.
            // A qualified path fn value (`<S as Tr>::mk`), lowered as
            // the plain path's fn value; a qualified const lowered
            // above from its value.
            Expr::QPath { .. } => {
                if let Res::Fn(f) = self.ck.res(e) {
                    // A generic fn (an impl's or a trait default) names
                    // its mono instance, as on a plain path.
                    let f = self.resolve_generic_fn(e, f);
                    let want = match dest {
                        Some(d) if d.proj.is_empty() => {
                            let dt = self.body.locals[d.local as usize].ty;
                            if matches!(self.kind(dt), TyKind::FnPtr(_)) { dt } else { ty }
                        }
                        _ => ty,
                    };
                    self.set_or_temp(dest, Rvalue::FnValue(f, want), ty, span)
                } else if matches!(self.ck.res(e), Res::PrimAssoc { .. } | Res::OptSome | Res::ResOk | Res::ResErr)
                    && matches!(self.kind(ty), TyKind::FnDef(..))
                {
                    // A primitive builtin method or builtin constructor through
                    // a qualified path (`<[T]>::len`, `<Option<u8>>::Some`), as
                    // on a plain path: its codegen fn in a fn pointer place,
                    // else the zero-sized item.
                    match self.fn_ptr_dest(dest) {
                        Some(dt) => self.set_or_temp(dest, Rvalue::ItemShim(ty, dt), ty, span),
                        None => self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Unit)), ty, span),
                    }
                } else if matches!(self.ck.res(e), Res::Builtin(_)) && matches!(self.kind(ty), TyKind::FnDef(..)) || self.is_trait_marker_value(ty) {
                    // A builtin-marker trait fn value (`<i32 as
                    // Clone>::clone`): zero-sized, as on a plain path.
                    self.set_or_temp(dest, Rvalue::Use(Operand::Const(Const::Unit)), ty, span)
                }
            }
            Expr::Float(_)
            | Expr::Await(_)
            | Expr::AsyncBlock { .. }
            | Expr::UnsafeBlock(_)
            | Expr::Let { .. }
            | Expr::ConstBlock(_)
            | Expr::Underscore
            | Expr::MacroCall(_) => {}
        }
    }

    /// `expr?`: evaluate the scrutinee into a temporary, branch on
    /// its discriminant, move the success payload to `dest` on the
    /// good side, and on the empty side build the enclosing return
    /// value (converting the error as the checker recorded) and
    /// return it through the normal return path, drops included.
    fn try_into(&mut self, e: ExprId, inner: ExprId, dest: Option<&Place>, ty: Ty, span: Span) {
        let ity = self.ty(inner);
        let t = self.temp(ity);
        self.expr_into(inner, Some(&Place::local(t)));
        let tp = Place::local(t);
        let dsc = self.temp(int(IntTy::U32));
        self.assign(Place::local(dsc), Rvalue::Discriminant(tp.clone()), span);
        let is_result = self.body.tys.result_args(ity).is_some();
        // `core::ops::ControlFlow` (std source): `Continue` is 0, and a
        // `Break(b)` returns `ControlFlow::Break(b)` in the return type.
        let ret_ty = self.body.locals[0].ty;
        let flow = |t: Ty| {
            let a = self.body.tys.adt_parts(t).and_then(|(d, _)| self.body.tys.local_adt_of(d));
            a.is_some_and(|a| self.p.is_control_flow_adt(a))
        };
        // The `Break` aggregate names the return type's instance Adt.
        let control_flow = if flow(ity) && flow(ret_ty) { self.body.tys.local_adt(ret_ty) } else { None };
        // Variant index of the valued side: Ok and Continue are 0, Some is 1.
        let good: u32 = if is_result || control_flow.is_some() { 0 } else { 1 };
        let ok_bb = self.new_block();
        let err_bb = self.new_block();
        {
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(dsc)), vec![(good, ok_bb)], err_bb);
            b.term_span = span;
        }
        self.cur = err_bb;
        if let Some(adt) = control_flow {
            let b_ty = self.body.tys.adt_parts(ity).map(|(_, a)| self.body.tys.args(a)[0].as_ty().unwrap_or(ty)).unwrap_or(ty);
            let payload = tp.clone().project(Proj::Downcast(1)).project(Proj::Field(0));
            let op = self.operand_from(payload, b_ty);
            self.assign(Place::local(0), Rvalue::Aggregate(adt, 1, vec![op]), span);
        } else if let Some((_, err_ty)) = self.body.tys.result_args(ity) {
            let payload = tp.clone().project(Proj::Downcast(1)).project(Proj::Field(0));
            let ret_err = self.body.tys.result_args(ret_ty).map(|(_, e2)| e2).unwrap_or(err_ty);
            let err_op = match self.ck.res(e) {
                Res::TryCast => {
                    let ct = self.temp(ret_err);
                    let op = self.operand_from(payload, err_ty);
                    self.assign(Place::local(ct), Rvalue::Cast(op, ret_err), span);
                    Operand::Move(Place::local(ct))
                }
                Res::TryFrom(f) if f.0 != u32::MAX => {
                    let f = self.resolve_generic_fn(e, f);
                    let ct = self.temp(ret_err);
                    let op = self.operand_from(payload, err_ty);
                    self.call_into(CallTarget::Fn(f), vec![op], Place::local(ct), span);
                    Operand::Move(Place::local(ct))
                }
                Res::TryStringFrom => {
                    let mut op = self.operand_from(payload, err_ty);
                    // `From<&String>` first views the String as `&str`.
                    if matches!(self.body.tys.kind(err_ty), TyKind::Ref(_, _, i) if i == STRING) {
                        let st = self.temp(REF_STR);
                        self.call_into(CallTarget::Builtin(Builtin::StringAsStr), vec![op], Place::local(st), span);
                        op = Operand::Move(Place::local(st));
                    }
                    let ct = self.temp(ret_err);
                    self.call_into(CallTarget::Builtin(Builtin::StringFrom), vec![op], Place::local(ct), span);
                    Operand::Move(Place::local(ct))
                }
                _ => self.operand_from(payload, err_ty),
            };
            self.assign(Place::local(0), Rvalue::Res(ret_ty, false, err_op), span);
        } else {
            self.assign(Place::local(0), Rvalue::Opt(ret_ty, None), span);
        }
        self.exit_to(0, span);
        self.terminate(Terminator::Return, span);
        self.cur = ok_bb;
        let payload = tp.project(Proj::Downcast(good)).project(Proj::Field(0));
        let op = self.operand_from(payload, ty);
        self.set_or_temp(dest, Rvalue::Use(op), ty, span);
    }

    /// The `&&` elements of a condition, left to right.
    fn split_and(&self, e: ExprId, out: &mut Vec<ExprId>) {
        match self.p.ast.expr(e) {
            Expr::Binary { op: BinOp::And, lhs, rhs } => {
                self.split_and(*lhs, out);
                self.split_and(*rhs, out);
            }
            _ => out.push(e),
        }
    }

    fn is_let_chain(&self, cond: ExprId) -> bool {
        let mut elems = Vec::new();
        self.split_and(cond, &mut elems);
        elems.iter().any(|&e| matches!(self.p.ast.expr(e), Expr::Let { .. }))
    }

    /// Lowers a let-chain condition in the current (chain) scope: falls
    /// through on success; each failing element drops what the chain has
    /// bound so far and jumps to `els_bb`.
    fn cond_chain(&mut self, cond: ExprId, els_bb: Bb, span: Span) {
        let mut elems = Vec::new();
        self.split_and(cond, &mut elems);
        for el in elems {
            match self.p.ast.expr(el) {
                Expr::Let { pat, scrut } => {
                    let (pat, scrut) = (*pat, *scrut);
                    let es = self.span(el);
                    let sp = self.place(scrut);
                    let sp = self.pattern_place(sp, self.ty(scrut), &[pat], es);
                    let fail = self.new_block();
                    let live = self.scopes.last().cloned().unwrap_or_default();
                    self.test_pat(pat, sp.clone(), fail);
                    let cont = self.cur;
                    self.cur = fail;
                    self.emit_drops(&live, es);
                    self.goto(els_bb, es);
                    self.cur = cont;
                    self.bind_pat(pat, sp);
                }
                _ => {
                    let cl = self.cond(el, span);
                    let next = self.new_block();
                    let fail = self.new_block();
                    let live = self.scopes.last().cloned().unwrap_or_default();
                    let b = &mut self.body.blocks[self.cur.0 as usize];
                    b.term = Terminator::If(Operand::Copy(Place::local(cl)), next, fail);
                    b.term_span = span;
                    self.cur = fail;
                    self.emit_drops(&live, span);
                    self.goto(els_bb, span);
                    self.cur = next;
                }
            }
        }
    }

    /// Evaluates a condition into a fresh bool local. Its temporaries drop before the branch.
    fn cond(&mut self, cond: ExprId, span: Span) -> Local {
        let cl = self.new_local(BOOL, true, None);
        self.scopes.push(Vec::new());
        self.expr_into(cond, Some(&Place::local(cl)));
        self.pop_scope(span);
        cl
    }

    fn unit(&mut self, dest: Option<&Place>, span: Span) {
        if let Some(d) = dest {
            self.assign(d.clone(), Rvalue::Use(Operand::Const(Const::Unit)), span);
        }
    }

    fn peel_vec(&self, t: Ty) -> Ty {
        self.body.tys.vec_elem(t).unwrap_or(ERROR)
    }

    // ---------- Blocks ----------

    fn block_into(&mut self, b: ast::BlockId, dest: Option<&Place>) {
        let block = self.p.ast.block(b);
        self.scopes.push(Vec::new());
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let { pat, init, els, span, .. } => match els {
                    Some(els_b) => self.let_else_stmt(*pat, *init, *els_b, *span),
                    None => self.let_stmt(*pat, *init, *span),
                },
                // Body items and statement macros are rejected by the parser today.
                Stmt::Item(_) | Stmt::Macro { .. } => {}
                Stmt::Expr { expr, .. } => {
                    let span = self.span(*expr);
                    self.scopes.push(Vec::new());
                    self.stmt_expr(*expr);
                    self.pop_scope(span);
                }
            }
        }
        match block.tail {
            // A tail rustc coerces after the block (check `after_tail`):
            // its value goes to a temporary of the enclosing scope, and
            // the coercion reads it once the block's scopes are gone.
            Some(tail) if self.ck.is_after_tail(tail) => {
                let span = self.span(tail);
                let (ty, outer) = (self.ty(tail), self.scopes.len().saturating_sub(2));
                let t = self.new_local(ty, true, None);
                self.scopes.push(Vec::new());
                self.expr_into_raw(tail, Some(&Place::local(t)));
                self.pop_scope(span);
                self.pop_scope(block.span);
                self.scopes[outer].push(t);
                if dest.is_none() {
                    // rustc reborrows the value even when it is unused
                    // (`if c { &&G } else { &v[0] };`).
                    self.push(StmtKind::FakeRead(t), span);
                    return;
                }
                self.prelowered.push((tail, Place::local(t), self.spine_gen));
                self.expr_into(tail, dest);
                return;
            }
            Some(tail) => {
                // Edition 2024: temporaries in a block's tail drop before the block's locals.
                let span = self.span(tail);
                self.scopes.push(Vec::new());
                self.expr_into(tail, dest);
                self.pop_scope(span);
            }
            None => self.unit(dest, block.span),
        }
        self.pop_scope(block.span);
    }

    /// An expression statement, as rustc's `stmt_expr`: the value goes
    /// into a statement temporary that drops at the end of the
    /// statement. A place moves (or copies) into it (`s;` drops `s`
    /// here), and a block, `if`, `match`, or `loop` value drops after
    /// the locals of the block that made it. Other values already go to
    /// a temporary of this scope where the expression needs one.
    fn stmt_expr(&mut self, e: ExprId) {
        let value = matches!(
            self.p.ast.expr(e),
            Expr::Block(_) | Expr::LabeledBlock { .. } | Expr::If { .. } | Expr::Match { .. } | Expr::Loop { .. }
        );
        let ty = self.ty(e);
        // A const value (`CD;`, an inline const) is no place and
        // builds no temporary on its own, but the copy it makes is a
        // statement temporary like any other and drops here.
        let const_temp = self.ck.const_value(e).is_some() && self.needs_drop_ty(ty);
        if self.ck.coerce(e) == Coerce::None && (self.is_place_expr(e) || value && self.needs_drop_ty(ty) || const_temp) {
            self.materialize(e, ty, false);
        } else {
            self.expr_into(e, None);
        }
    }

    /// An `if` or `match` arm. rustc's LUB coercion reborrows (`&*arm`)
    /// each reference-typed arm after the first one that does not
    /// diverge (`reborrow`): the reborrow reads the arm's value after the
    /// arm's block has dropped its locals and tail temporaries, so a
    /// borrow of those is an error even when the result is unused (`if c
    /// { .. } else { &temp() };`). Such an arm goes into a temporary
    /// first; a coerced arm is already read through its coercion.
    fn arm_into(&mut self, e: ExprId, reborrow: bool, dest: Option<&Place>) {
        if !reborrow || self.ck.coerce(e) != Coerce::None {
            self.expr_into(e, dest);
            return;
        }
        let (ty, span) = (self.ty(e), self.span(e));
        let t = self.materialize(e, ty, false);
        match dest {
            Some(d) => {
                let op = self.operand_from(Place::local(t), ty);
                self.assign(d.clone(), Rvalue::Use(op), span);
            }
            None => self.push(StmtKind::FakeRead(t), span),
        }
    }

    /// True when an `if` or `match` result of type `ty` is a reference,
    /// whose later arms rustc reborrows (`arm_into`).
    fn reborrows_arms(&self, ty: Ty) -> bool {
        matches!(self.kind(ty), TyKind::Ref(..))
    }

    fn diverges(&self, e: ExprId) -> bool {
        matches!(self.kind(self.ty(e)), TyKind::Never)
    }

    /// True when block `b` has type `!`: its tail diverges, or it has no
    /// tail where a value is expected.
    fn block_diverges(&self, b: ast::BlockId) -> bool {
        self.p.ast.block(b).tail.is_none_or(|t| self.diverges(t))
    }

    /// Marks the temporaries a `let` initializer extends to the end of
    /// the enclosing block (scope `depth`), as rustc's
    /// `record_rvalue_scope_if_borrow_expr`: the operand of each
    /// extending borrow, found through the initializer itself and the
    /// operands of extending struct, tuple, array, and cast expressions,
    /// the arguments of tuple struct and variant constructors, block
    /// tails, and the arms of `if` and `match`.
    fn mark_extending(&mut self, e: ExprId, depth: usize) {
        let p = self.p;
        match p.ast.expr(e) {
            Expr::Ref { expr, .. } => {
                self.mark_extending(*expr, depth);
                self.mark_extended(*expr, depth);
            }
            Expr::StructLit { fields, .. } => {
                for &(_, _, f) in fields {
                    self.mark_extending(f, depth);
                }
            }
            Expr::Tuple(es) | Expr::Array(es) => {
                for &x in es {
                    self.mark_extending(x, depth);
                }
            }
            Expr::Cast { expr, .. } => self.mark_extending(*expr, depth),
            Expr::Block(b) | Expr::UnsafeBlock(b) | Expr::LabeledBlock { body: b, .. } => {
                if let Some(t) = p.ast.block(*b).tail {
                    self.mark_extending(t, depth);
                }
            }
            Expr::If { then, els, .. } => {
                if let Some(t) = p.ast.block(*then).tail {
                    self.mark_extending(t, depth);
                }
                if let Some(x) = els {
                    self.mark_extending(*x, depth);
                }
            }
            Expr::Match { arms, .. } => {
                for arm in arms {
                    self.mark_extending(arm.body, depth);
                }
            }
            Expr::Call { callee, args } if self.is_ctor_callee(e, *callee) => {
                for &a in args {
                    self.mark_extending(a, depth);
                }
            }
            // rustc's `format_args!` is a `super let` of its args array,
            // each argument under an extending `&`: the array (keyed by
            // the macro expression, see `format_args_into`) and each
            // argument's temporaries, also those of a nested
            // `format_args!`, live to the end of the block (R9).
            Expr::Macro { kind: MacroKind::FormatArgs, args, fmt, .. } => {
                self.extended.push((e, depth));
                for piece in fmt {
                    if let FmtPiece::Arg { index, spec, .. } = piece {
                        for i in [Some(*index as u32), spec.width_arg, spec.precision_arg].into_iter().flatten() {
                            self.mark_extending(args[i as usize], depth);
                            self.mark_extended(args[i as usize], depth);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// rustc's `record_rvalue_scope`: `e`, and the expressions it
    /// borrows, derefs, or projects a field or an index from, get the
    /// extended temporary scope (`&temp().field` extends `temp()`).
    fn mark_extended(&mut self, mut e: ExprId, depth: usize) {
        loop {
            self.extended.push((e, depth));
            match self.p.ast.expr(e) {
                Expr::Ref { expr, .. } | Expr::Deref(expr) => e = *expr,
                Expr::Field { base, .. } | Expr::TupleField { base, .. } | Expr::Index { base, .. } => e = *base,
                _ => return,
            }
        }
    }

    /// True for the callee of a tuple struct or tuple variant
    /// constructor call written as a resolved path (`W(..)`, `Some(..)`,
    /// `m::E::V(..)`, `Self(..)`), whose arguments extend like a
    /// struct literal's fields. A type-relative path (`Self::V(..)`, a
    /// variant through a type alias) does not extend, as in rustc.
    fn is_ctor_callee(&self, call: ExprId, callee: ExprId) -> bool {
        let p = self.p;
        let Expr::Path(segs) = p.ast.expr(callee) else { return false };
        if !matches!(self.ck.res(call), Res::Variant(..) | Res::OptSome | Res::ResOk | Res::ResErr) {
            return false;
        }
        match segs.len() {
            0 | 1 => true,
            n => {
                let head = segs[n - 2].name;
                head != p.known.self_type && !p.aliases.contains_key(&head)
            }
        }
    }

    /// rustc's `is_binding_pat`: a pattern with an explicit `ref` or
    /// `ref mut` binding (not one match ergonomics makes) extends its
    /// whole initializer to the end of the block.
    fn is_binding_pat(&self, pat: PatId) -> bool {
        match self.p.ast.pat(pat) {
            Pat::Binding { by_ref, .. } | Pat::At { by_ref, .. } => *by_ref,
            Pat::Struct { fields, .. } => fields.iter().any(|&(_, s)| self.is_binding_pat(s)),
            Pat::TupleStruct { elems, .. } | Pat::Tuple(elems) | Pat::Or(elems) => elems.iter().any(|&s| self.is_binding_pat(s)),
            Pat::Slice { prefix, middle, suffix } => {
                middle.is_some_and(|m| self.is_binding_pat(m)) || prefix.iter().chain(suffix.iter()).any(|&s| self.is_binding_pat(s))
            }
            Pat::Paren(i) => self.is_binding_pat(*i),
            _ => false,
        }
    }

    /// `let PAT = init;`, as rustc builds it: the initializer's
    /// temporaries drop at the end of the statement, except those a
    /// borrow extends to the end of the block (`mark_extending`). A
    /// plain binding takes the value directly and is used once it is
    /// set (rustc's `FakeRead(ForLet)`), so a borrow of something the
    /// initializer already dropped is an error. Any other pattern binds
    /// out of the initializer's place (see `pattern_init`).
    fn let_stmt(&mut self, pat: PatId, init: Option<ExprId>, span: Span) {
        let p = self.p;
        let Some(init) = init else {
            if let (Pat::Binding { .. }, PatRes::Binding { local, .. }) = (p.ast.pat(pat), self.ck.pat_res(pat)) {
                let l = self.binding_local(local);
                self.scopes.last_mut().unwrap().push(l);
            }
            return;
        };
        let block = self.scopes.len() - 1;
        let mark = self.extended.len();
        self.mark_extending(init, block);
        self.scopes.push(Vec::new());
        match (p.ast.pat(pat), self.ck.pat_res(pat)) {
            (Pat::Binding { by_ref: false, .. }, PatRes::Binding { local, mode: BindMode::Move }) => {
                let l = self.binding_local(local);
                self.expr_into(init, Some(&Place::local(l)));
                self.push(StmtKind::FakeRead(l), span);
                self.scopes[block].push(l);
            }
            (Pat::Wild, _) => {
                // `let _ = init;` binds nothing. A place initializer is
                // only mentioned (rustc `PlaceMention`): not read or
                // moved, but its root is live here; an index in it still
                // runs, through a shared borrow. A value goes into a
                // statement temporary that is mentioned the same way.
                if self.ck.coerce(init) == Coerce::None && self.is_place_expr(init) {
                    let pl = self.place(init);
                    if pl.proj.iter().any(|x| matches!(x, Proj::Index(_))) {
                        let rt = self.ref_ty(false, self.ty(init));
                        let t = self.temp(rt);
                        self.assign(Place::local(t), Rvalue::Ref(false, pl), span);
                    } else {
                        self.push(StmtKind::FakeRead(pl.local), span);
                    }
                } else if let Operand::Copy(pl) | Operand::Move(pl) = self.operand(init) {
                    self.push(StmtKind::FakeRead(pl.local), span);
                }
            }
            _ => {
                let src = self.pattern_init(pat, init, block, span);
                let stmt = self.scopes.pop().unwrap();
                self.bind_pat(pat, src);
                self.scopes.push(stmt);
            }
        }
        self.pop_scope(span);
        self.extended.truncate(mark);
    }

    /// The IR local for a `let` binding's checker local.
    fn binding_local(&mut self, local: u32) -> Local {
        let info = &self.ck.locals[local as usize];
        let (ty, m, name) = (info.ty, info.mutable, self.p.name(info.name).to_string());
        let l = self.new_local(ty, m, Some(name));
        self.local_map[local as usize] = l;
        self.bind_of.push((l, local));
        l
    }

    /// The place a destructuring `let` (or `let`-`else`) binds out of,
    /// evaluated in the statement scope (the innermost one): a place
    /// initializer itself, as in rustc (a binding that moves a part is
    /// a partial move of it; the rest stays and drops with its owner,
    /// `cgen::FnGen::elab_drop`); any other value moves into a
    /// temporary whose leftover parts drop at the end of the statement,
    /// or at the end of the block (scope `block`) when the pattern has
    /// an explicit `ref` binding, which extends the whole initializer.
    fn pattern_init(&mut self, pat: PatId, init: ExprId, block: usize, span: Span) -> Place {
        if self.is_binding_pat(pat) {
            self.mark_extended(init, block);
        }
        if self.ck.coerce(init) == Coerce::None && self.is_place_expr(init) {
            let pl = self.place(init);
            return self.pattern_place(pl, self.ty(init), &[pat], span);
        }
        let ty = self.coerced_ty(init);
        let t = self.materialize(init, ty, false);
        Place::local(t)
    }

    /// `let PAT = init else { ... };`: test the pattern against the
    /// initializer's place (`pattern_init`), bind on success, and run
    /// the diverging else block on failure. The statement's
    /// temporaries drop at its end on success and before the else
    /// block on failure, as in rustc.
    fn let_else_stmt(&mut self, pat: PatId, init: Option<ExprId>, els: ast::BlockId, span: Span) {
        let Some(init) = init else { return };
        let block = self.scopes.len() - 1;
        let mark = self.extended.len();
        self.mark_extending(init, block);
        self.scopes.push(Vec::new());
        let sp = self.pattern_init(pat, init, block, span);
        let fail = self.new_block();
        self.test_pat(pat, sp.clone(), fail);
        let stmt = self.scopes.pop().unwrap();
        self.bind_pat(pat, sp);
        self.emit_drops(&stmt, span);
        self.extended.truncate(mark);
        let cont = self.cur;
        self.cur = fail;
        self.emit_drops(&stmt, span);
        self.block_into(els, None);
        self.terminate(Terminator::Unreachable, span);
        self.cur = cont;
    }

    // ---------- Calls ----------

    /// A comparison trait method (`Res::PrimCmp`): the receiver is
    /// borrowed `&self` (so borrowck sees the loan a method call
    /// would make), and the result is the comparison, an
    /// `Ordering` value, or an `Option<Ordering>` (`None` only when
    /// the comparison is unordered). Scalars compare directly,
    /// `str` through the string comparison, and other types by
    /// structure through the `eq` and `cmp` glue.
    fn prim_cmp_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], dest: Option<&Place>, span: Span, kind: PrimCmpKind, derefs: u8) {
        use crate::check::PrimCmpKind as Ck;
        let out_ty = self.ty(e);
        let out = match dest {
            Some(d) => d.clone(),
            None => Place::local(self.temp(out_ty)),
        };
        if args.is_empty() {
            return;
        }
        let recv_ty = self.peel(self.ty(recv), derefs);
        let pl = Self::derefs(self.place(recv), derefs);
        let rt_ty = self.ref_ty(false, recv_ty);
        let rt = self.temp(rt_ty);
        self.assign(Place::local(rt), Rvalue::Ref(false, pl), span);
        let b_ref = self.operand(args[0]);
        let b_pl = self.op_place(b_ref, self.ty(args[0]), span);
        // One comparison of the two sides as a `bool` rvalue. The
        // eq test of `partial_cmp` asks `<=` after `<` failed: that
        // is "equal" exactly as the type's `partial_cmp` orders,
        // also for a structure whose `PartialEq` is not derived.
        let scalar = matches!(self.kind(recv_ty), TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char);
        let is_str = self.kind(recv_ty) == TyKind::Str;
        let (a_ref, b_ref) = (Operand::Copy(Place::local(rt)), Operand::Copy(b_pl.clone()));
        let (code_a, code_b) = (a_ref.clone(), b_ref.clone());
        let rv = move |op: BinOp| -> Rvalue {
            if scalar {
                Rvalue::Bin(op, Operand::Copy(Place::local(rt).deref()), Operand::Copy(b_pl.deref()))
            } else if is_str {
                Rvalue::StrCmp(op, a_ref.clone(), b_ref.clone())
            } else if matches!(op, BinOp::Eq | BinOp::Ne) {
                Rvalue::Eq { a: a_ref.clone(), b: b_ref.clone(), ty: recv_ty, ne: op == BinOp::Ne }
            } else {
                Rvalue::Cmp { op, a: a_ref.clone(), b: b_ref.clone(), ty: recv_ty }
            }
        };
        match kind {
            Ck::Op(op) => self.assign(out, rv(op), span),
            Ck::Total(adt) | Ck::Partial(adt) => {
                let partial = matches!(kind, Ck::Partial(_));
                // A structural type compares once, through the cmp
                // glue's code (-1, 0, 1, or 2 for unordered); the
                // tests below then read that code.
                let code = if scalar || is_str {
                    None
                } else {
                    let i8_ty = int(IntTy::I8);
                    let c = self.temp(i8_ty);
                    // `partial_cmp` on a type only the `PCmp` glue orders
                    // (check/mod.rs): that glue's code.
                    let b = if partial && !has_ord(self.p, &self.body.tys, recv_ty) { Builtin::PCmpCode } else { Builtin::CmpCode };
                    self.call_into(CallTarget::Builtin(b), vec![code_a, code_b], Place::local(c), span);
                    Some(c)
                };
                let cmp = |this: &mut Self, op: BinOp| {
                    let t = this.temp(BOOL);
                    let r = match code {
                        Some(c) => {
                            let want: i128 = match op {
                                BinOp::Lt => -1,
                                BinOp::Gt => 1,
                                _ => 0,
                            };
                            Rvalue::Bin(BinOp::Eq, Operand::Copy(Place::local(c)), Operand::Const(Const::Int(want as u128, IntTy::I8)))
                        }
                        None => rv(op),
                    };
                    this.assign(Place::local(t), r, span);
                    t
                };
                let lt = cmp(self, BinOp::Lt);
                let gt = cmp(self, BinOp::Gt);
                let eq = if partial { Some(cmp(self, BinOp::Eq)) } else { None };
                let (ord_ty, ord_pl) = if partial {
                    let t = self.body.tys.option_elem(out_ty).unwrap_or(out_ty);
                    (t, Place::local(self.temp(t)))
                } else {
                    (out_ty, out.clone())
                };
                let _ = ord_ty;
                let (less_b, gt_b, greater_b, eq_b, equal_b, none_b, wrap_b, end) = (
                    self.new_block(),
                    self.new_block(),
                    self.new_block(),
                    self.new_block(),
                    self.new_block(),
                    self.new_block(),
                    self.new_block(),
                    self.new_block(),
                );
                let branch = |this: &mut Self, cond: Local, t: Bb, f: Bb| {
                    let bb = &mut this.body.blocks[this.cur.0 as usize];
                    bb.term = Terminator::If(Operand::Copy(Place::local(cond)), t, f);
                    bb.term_span = span;
                };
                branch(self, lt, less_b, gt_b);
                self.cur = less_b;
                self.assign(ord_pl.clone(), Rvalue::Aggregate(adt, 0, Vec::new()), span);
                self.goto(wrap_b, span);
                self.cur = gt_b;
                branch(self, gt, greater_b, eq_b);
                self.cur = greater_b;
                self.assign(ord_pl.clone(), Rvalue::Aggregate(adt, 2, Vec::new()), span);
                self.goto(wrap_b, span);
                self.cur = eq_b;
                match eq {
                    // `Ord::cmp`: not less and not greater is Equal.
                    None => {
                        self.assign(ord_pl.clone(), Rvalue::Aggregate(adt, 1, Vec::new()), span);
                        self.goto(wrap_b, span);
                    }
                    Some(eq) => branch(self, eq, equal_b, none_b),
                }
                self.cur = equal_b;
                self.assign(ord_pl.clone(), Rvalue::Aggregate(adt, 1, Vec::new()), span);
                self.goto(wrap_b, span);
                self.cur = none_b;
                if partial {
                    self.assign(out.clone(), Rvalue::Opt(out_ty, None), span);
                }
                self.goto(end, span);
                self.cur = wrap_b;
                if partial {
                    self.assign(out, Rvalue::Opt(out_ty, Some(Operand::Copy(ord_pl))), span);
                }
                self.goto(end, span);
                self.cur = end;
            }
        }
    }

    /// Calls a written comparison method `f` on the borrowed sides `a`
    /// and `b` and writes the answer `via` asks for into `out`: the
    /// method's own `bool`, its negation (`ne` through `eq`), or a
    /// test of its `Option<Ordering>` (`lt` and kin through
    /// `partial_cmp`, as core's default bodies).
    fn trait_cmp_call(&mut self, f: LocalDefId, a: Operand, b: Operand, via: CmpVia, out: Place, span: Span) {
        match via {
            CmpVia::Direct => self.call_into(CallTarget::Fn(f), vec![a, b], out, span),
            CmpVia::NotEq => {
                let t = self.temp(BOOL);
                self.call_into(CallTarget::Fn(f), vec![a, b], Place::local(t), span);
                self.assign(out, Rvalue::Un(crate::ast::UnOp::Not, Operand::Copy(Place::local(t))), span);
            }
            CmpVia::Partial(op) => {
                let ret = self.p.fn_info(f).ret;
                let t = self.temp(ret);
                self.call_into(CallTarget::Fn(f), vec![a, b], Place::local(t), span);
                self.ordering_test(Place::local(t), op, out, span);
            }
        }
    }

    /// Writes `opt <op> Some(Equal)` for an `Option<Ordering>` place
    /// into `out`, as `PartialOrd::lt` and kin answer from
    /// `partial_cmp`: false on `None`, else the variant index of the
    /// `Ordering` (Less 0, Equal 1, Greater 2) against Equal's.
    fn ordering_test(&mut self, opt: Place, op: BinOp, out: Place, span: Span) {
        let u32_ty = int(IntTy::U32);
        let d = self.temp(u32_ty);
        self.assign(Place::local(d), Rvalue::Discriminant(opt.clone()), span);
        let (some_b, none_b, end) = (self.new_block(), self.new_block(), self.new_block());
        let b = &mut self.body.blocks[self.cur.0 as usize];
        b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(1, some_b)], none_b);
        b.term_span = span;
        self.cur = none_b;
        self.assign(out.clone(), Rvalue::Use(Operand::Const(Const::Bool(false))), span);
        self.goto(end, span);
        self.cur = some_b;
        let k = self.temp(u32_ty);
        self.assign(Place::local(k), Rvalue::Discriminant(opt.project(Proj::Downcast(1)).project(Proj::Field(0))), span);
        self.assign(out, Rvalue::Bin(op, Operand::Copy(Place::local(k)), Operand::Const(Const::Int(1, IntTy::U32))), span);
        self.goto(end, span);
    }

    /// A `core::cmp::Ordering` method (`Res::OrderingOp`): the
    /// receiver's variant index (Less 0, Equal 1, Greater 2) decides.
    /// `then` evaluates its argument after the receiver, as a call
    /// does, and keeps the receiver unless it is `Equal`.
    #[allow(clippy::too_many_arguments)]
    fn ordering_op_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], dest: Option<&Place>, span: Span, kind: OrderingOpKind, derefs: u8) {
        use OrderingOpKind as K;
        let ty = self.ty(e);
        let ord_ty = self.peel(self.ty(recv), derefs);
        let Some(adt) = self.body.tys.local_adt(ord_ty) else { return };
        let r = self.temp(ord_ty);
        let op = self.operand_derefs(recv, derefs);
        self.assign(Place::local(r), Rvalue::Use(op), span);
        let u32_ty = int(IntTy::U32);
        let d = self.temp(u32_ty);
        self.assign(Place::local(d), Rvalue::Discriminant(Place::local(r)), span);
        let out = self.call_dest(dest, ty);
        let test = |op: BinOp| Rvalue::Bin(op, Operand::Copy(Place::local(d)), Operand::Const(Const::Int(1, IntTy::U32)));
        match kind {
            K::IsEq => self.assign(out, test(BinOp::Eq), span),
            K::IsNe => self.assign(out, test(BinOp::Ne), span),
            K::IsLt => self.assign(out, test(BinOp::Lt), span),
            K::IsGt => self.assign(out, test(BinOp::Gt), span),
            K::IsLe => self.assign(out, test(BinOp::Le), span),
            K::IsGe => self.assign(out, test(BinOp::Ge), span),
            K::Reverse => {
                let (b0, b1, b2, end) = (self.new_block(), self.new_block(), self.new_block(), self.new_block());
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(0, b0), (1, b1)], b2);
                b.term_span = span;
                for (blk, v) in [(b0, 2u32), (b1, 1), (b2, 0)] {
                    self.cur = blk;
                    self.assign(out.clone(), Rvalue::Aggregate(adt, v, Vec::new()), span);
                    self.goto(end, span);
                }
            }
            K::ThenWith => {
                // The closure moves into a local; it runs only on Equal.
                let fty = self.ty(args[0]);
                let c = self.temp(fty);
                self.expr_into(args[0], Some(&Place::local(c)));
                let eq = self.temp(BOOL);
                self.assign(Place::local(eq), test(BinOp::Eq), span);
                let (t, f, end) = (self.new_block(), self.new_block(), self.new_block());
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::If(Operand::Copy(Place::local(eq)), t, f);
                b.term_span = span;
                self.cur = t;
                self.call_closure_once(Place::local(c), fty, out.clone(), span);
                self.goto(end, span);
                self.cur = f;
                self.assign(out, Rvalue::Use(Operand::Copy(Place::local(r))), span);
                if needs_drop(self.p, &self.body.tys, fty) {
                    self.push(StmtKind::Drop(c), span);
                }
                self.goto(end, span);
            }
            K::Then => {
                let o = self.temp(ord_ty);
                self.expr_into(args[0], Some(&Place::local(o)));
                let eq = self.temp(BOOL);
                self.assign(Place::local(eq), test(BinOp::Eq), span);
                let (t, f, end) = (self.new_block(), self.new_block(), self.new_block());
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::If(Operand::Copy(Place::local(eq)), t, f);
                b.term_span = span;
                self.cur = t;
                self.assign(out.clone(), Rvalue::Use(Operand::Copy(Place::local(o))), span);
                self.goto(end, span);
                self.cur = f;
                self.assign(out, Rvalue::Use(Operand::Copy(Place::local(r))), span);
                self.goto(end, span);
            }
        }
    }

    /// `Vec::drain` and `String::drain`: the receiver's `&mut` and
    /// the range bounds as four words (start tag and value, end tag
    /// and value; tags are the runtime's 0 Included, 1 Excluded,
    /// 2 Unbounded). The bounds run under the two-phase reservation
    /// of an inherent `&mut self` method, as in `method_into`.
    fn drain_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], derefs: u8, dest: Option<&Place>, span: Span) {
        let Res::BuiltinMethod { b, .. } = self.ck.res(e) else { return };
        let Some(form) = self.ck.drain_range(e) else { return };
        let root = self.deref_steps(e, recv, span);
        let root_ty = match &root {
            Some(pl) => self.body.locals[pl.local as usize].ty,
            None => self.ty(recv),
        };
        let recv_ty = self.peel(root_ty, derefs);
        let pl = Self::derefs(
            match &root {
                Some(pl) => pl.clone(),
                None => self.place_for_mut(recv),
            },
            derefs,
        );
        let mt = self.ref_ty(true, recv_ty);
        let t = self.temp(mt);
        // Through an `IndexMut` place or a user `Deref` step the
        // autoref is not two-phase (as in `method_into`).
        let two_phase = root.is_none() && !pl.proj.iter().any(|x| matches!(x, Proj::Index(_)));
        let bounds = if two_phase {
            let st = self.ref_ty(false, recv_ty);
            let reserve = self.temp(st);
            self.assign(Place::local(reserve), Rvalue::Ref(false, pl.clone()), span);
            let bounds = self.drain_bounds(e, args[0], form, span);
            self.push(StmtKind::FakeRead(reserve), span);
            self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
            bounds
        } else {
            self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
            self.drain_bounds(e, args[0], form, span)
        };
        let (stag, sval, etag, eval) = bounds;
        let d = self.call_dest(dest, self.ty(e));
        self.call_into(CallTarget::Builtin(b), vec![Operand::Move(Place::local(t)), stag, sval, etag, eval], d, span);
    }

    /// `v.splice(range, items);` (R4): like `drain_into`, the Vec's
    /// `&mut` (two-phase) and the range's four words, then the
    /// replacement value; the call expands in lower/iter/splice.rs.
    fn splice_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], derefs: u8, dest: Option<&Place>, span: Span) {
        let Some(form) = self.ck.drain_range(e) else { return };
        let root = self.deref_steps(e, recv, span);
        let root_ty = match &root {
            Some(pl) => self.body.locals[pl.local as usize].ty,
            None => self.ty(recv),
        };
        let recv_ty = self.peel(root_ty, derefs);
        let pl = Self::derefs(
            match &root {
                Some(pl) => pl.clone(),
                None => self.place_for_mut(recv),
            },
            derefs,
        );
        let mt = self.ref_ty(true, recv_ty);
        let t = self.temp(mt);
        let rw_ty = self.ty(args[1]);
        let rw = self.temp(rw_ty);
        let two_phase = root.is_none() && !pl.proj.iter().any(|x| matches!(x, Proj::Index(_)));
        let bounds = if two_phase {
            let st = self.ref_ty(false, recv_ty);
            let reserve = self.temp(st);
            self.assign(Place::local(reserve), Rvalue::Ref(false, pl.clone()), span);
            let bounds = self.drain_bounds(e, args[0], form, span);
            self.expr_into(args[1], Some(&Place::local(rw)));
            self.push(StmtKind::FakeRead(reserve), span);
            self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
            bounds
        } else {
            self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
            let bounds = self.drain_bounds(e, args[0], form, span);
            self.expr_into(args[1], Some(&Place::local(rw)));
            bounds
        };
        let (stag, sval, etag, eval) = bounds;
        let rw_op = self.operand_from(Place::local(rw), rw_ty);
        let d = self.call_dest(dest, self.ty(e));
        self.call_into(CallTarget::Builtin(Builtin::VecSplice), vec![Operand::Move(Place::local(t)), stag, sval, etag, eval, rw_op], d, span);
    }

    /// `[T]::copy_within`: like `drain_into`, the receiver's `&mut`
    /// and the range bounds as four words, then the destination
    /// index. The reservation is two-phase only on a slice place:
    /// on a Vec or array the method runs through `DerefMut` or an
    /// unsize, which is not two-phase (as in `method_into`).
    fn copy_within_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], derefs: u8, dest: Option<&Place>, span: Span) {
        let Res::BuiltinMethod { b, .. } = self.ck.res(e) else { return };
        let Some(form) = self.ck.drain_range(e) else { return };
        let root = self.deref_steps(e, recv, span);
        let root_ty = match &root {
            Some(pl) => self.body.locals[pl.local as usize].ty,
            None => self.ty(recv),
        };
        let recv_ty = self.peel(root_ty, derefs);
        let pl = Self::derefs(
            match &root {
                Some(pl) => pl.clone(),
                None => self.place_for_mut(recv),
            },
            derefs,
        );
        let mt = self.ref_ty(true, recv_ty);
        let t = self.temp(mt);
        // `Vec::extend_from_within` is a Vec method: its autoref is a
        // two-phase borrow, like a slice method on a slice place.
        let within = b == Builtin::VecExtendFromWithin;
        let two_phase = root.is_none()
            && (matches!(self.kind(recv_ty), TyKind::Slice(_)) || within)
            && !pl.proj.iter().any(|x| matches!(x, Proj::Index(_)));
        let mut dest_arg = |this: &mut Self| {
            (!within).then(|| {
                let d = this.temp(USIZE);
                this.expr_into(args[1], Some(&Place::local(d)));
                Operand::Copy(Place::local(d))
            })
        };
        let (bounds, dest_op) = if two_phase {
            let st = self.ref_ty(false, recv_ty);
            let reserve = self.temp(st);
            self.assign(Place::local(reserve), Rvalue::Ref(false, pl.clone()), span);
            let bounds = self.drain_bounds(e, args[0], form, span);
            let d = dest_arg(self);
            self.push(StmtKind::FakeRead(reserve), span);
            self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
            (bounds, d)
        } else {
            self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
            let bounds = self.drain_bounds(e, args[0], form, span);
            let d = dest_arg(self);
            (bounds, d)
        };
        let (stag, sval, etag, eval) = bounds;
        let d = self.call_dest(dest, self.ty(e));
        let mut call_args = vec![Operand::Move(Place::local(t)), stag, sval, etag, eval];
        call_args.extend(dest_op);
        self.call_into(CallTarget::Builtin(b), call_args, d, span);
    }

    /// `[T]::get` and `get_mut` with a range index: the receiver
    /// reference and the bounds as four words, like drain. The
    /// mutable form reserves two-phase only on a slice place, as
    /// in `copy_within_into`.
    fn get_range_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], derefs: u8, dest: Option<&Place>, span: Span, mutable: bool) {
        let Res::BuiltinMethod { b, .. } = self.ck.res(e) else { return };
        let Some(form) = self.ck.drain_range(e) else { return };
        let root = self.deref_steps(e, recv, span);
        let root_ty = match &root {
            Some(pl) => self.body.locals[pl.local as usize].ty,
            None => self.ty(recv),
        };
        let recv_ty = self.peel(root_ty, derefs);
        let pl = Self::derefs(
            match &root {
                Some(pl) => pl.clone(),
                None if mutable => self.place_for_mut(recv),
                None => self.place(recv),
            },
            derefs,
        );
        let rt = self.ref_ty(mutable, recv_ty);
        let t = self.temp(rt);
        let two_phase =
            mutable && root.is_none() && matches!(self.kind(recv_ty), TyKind::Slice(_)) && !pl.proj.iter().any(|x| matches!(x, Proj::Index(_)));
        let bounds = if two_phase {
            let st = self.ref_ty(false, recv_ty);
            let reserve = self.temp(st);
            self.assign(Place::local(reserve), Rvalue::Ref(false, pl.clone()), span);
            let bounds = self.slice_index_bounds(e, args[0], form, span);
            self.push(StmtKind::FakeRead(reserve), span);
            self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
            bounds
        } else {
            self.assign(Place::local(t), Rvalue::Ref(mutable, pl), span);
            self.slice_index_bounds(e, args[0], form, span)
        };
        let (stag, sval, etag, eval) = bounds;
        let d = self.call_dest(dest, self.ty(e));
        let recv_op = if mutable { Operand::Move(Place::local(t)) } else { Operand::Copy(Place::local(t)) };
        self.call_into(CallTarget::Builtin(b), vec![recv_op, stag, sval, etag, eval], d, span);
    }

    /// The four bound words of a `SliceIndex` range argument:
    /// drain's words, except a `RangeInclusive` value, whose
    /// exhausted flag moves the start to `end + 1` (core's
    /// `into_slice_range`), which drain's `RangeBounds` reading
    /// does not do.
    fn slice_index_bounds(
        &mut self,
        e: ExprId,
        arg: ExprId,
        form: crate::check::DrainRange,
        span: Span,
    ) -> (Operand, Operand, Operand, Operand) {
        if let crate::check::DrainRange::Value(crate::check::DrainForm::RangeInclusive) = form {
            let z = Operand::Const(Const::Int(0, IntTy::Usize));
            let aty = self.ty(arg);
            let t = self.temp(aty);
            self.expr_into(arg, Some(&Place::local(t)));
            let pl = Place::local(t);
            let lo = self.inclusive_lo(pl.clone(), span);
            return (z.clone(), lo, z, Operand::Copy(pl.project(Proj::Field(1))));
        }
        self.drain_bounds(e, arg, form, span)
    }

    /// The start of a `RangeInclusive` place as a slice range:
    /// `end + 1` (wrapping; the caller's length check rejects the
    /// wrapped case first) when exhausted, else `start`.
    fn inclusive_lo(&mut self, pl: Place, span: Span) -> Operand {
        let lo = self.temp(USIZE);
        let (tb, fb, join) = (self.new_block(), self.new_block(), self.new_block());
        let b = &mut self.body.blocks[self.cur.0 as usize];
        b.term = Terminator::If(Operand::Copy(pl.project(Proj::Field(2))), tb, fb);
        b.term_span = span;
        self.cur = tb;
        self.call_into(
            CallTarget::Builtin(Builtin::WrappingAdd),
            vec![Operand::Copy(pl.project(Proj::Field(1))), Operand::Const(Const::Int(1, IntTy::Usize))],
            Place::local(lo),
            span,
        );
        self.goto(join, span);
        self.cur = fb;
        self.assign(Place::local(lo), Rvalue::Use(Operand::Copy(pl.project(Proj::Field(0)))), span);
        self.goto(join, span);
        Operand::Copy(Place::local(lo))
    }

    /// The (lo, hi, inclusive) of a range value used as an index
    /// (`v[r]`, check/slice.rs): the value's fields, as a syntactic
    /// range's bounds. `(Bound, Bound)` pairs never reach here
    /// (rejected in check).
    fn range_value_bounds(&mut self, index: ExprId, form: crate::check::DrainForm, span: Span) -> (Operand, Option<Operand>, bool) {
        use crate::check::DrainForm as F;
        let z = Operand::Const(Const::Int(0, IntTy::Usize));
        let aty = self.ty(index);
        let t = self.temp(aty);
        self.expr_into(index, Some(&Place::local(t)));
        let pl = Place::local(t);
        let f = |i: u32| Operand::Copy(pl.project(Proj::Field(i)));
        match form {
            F::Range => (f(0), Some(f(1)), false),
            F::RangeInclusive => {
                let hi = f(1);
                (self.inclusive_lo(pl, span), Some(hi), true)
            }
            F::RangeFrom => (f(0), None, false),
            F::RangeTo => (z, Some(f(0)), false),
            F::RangeToInclusive => (z, Some(f(0)), true),
            F::RangeFull | F::Bounds | F::BoundsRef => (z, None, false),
        }
    }

    /// The four bound words of a `drain` argument, by its form
    /// (check/iter.rs `drain_range_form`).
    fn drain_bounds(&mut self, e: ExprId, arg: ExprId, form: crate::check::DrainRange, span: Span) -> (Operand, Operand, Operand, Operand) {
        use crate::check::{DrainForm as F, DrainRange as DR};
        let p = self.p;
        let z = |n: u64| Operand::Const(Const::Int(n as u128, IntTy::Usize));
        match form {
            DR::Syntactic => {
                let Expr::Range { lo, hi, inclusive } = p.ast.expr(arg) else { return (z(2), z(0), z(2), z(0)) };
                let (lo, hi, inclusive) = (*lo, *hi, *inclusive);
                let (stag, sval) = match lo {
                    Some(x) => (z(0), self.operand(x)),
                    None => (z(2), z(0)),
                };
                let (etag, eval) = match hi {
                    Some(x) => (z(if inclusive { 0 } else { 1 }), self.operand(x)),
                    None => (z(2), z(0)),
                };
                (stag, sval, etag, eval)
            }
            DR::Value(form) => {
                let aty = self.ty(arg);
                let t = self.temp(aty);
                self.expr_into(arg, Some(&Place::local(t)));
                let pl = Place::local(t);
                let f = |i: u32| Operand::Copy(pl.project(Proj::Field(i)));
                match form {
                    F::Range => (z(0), f(0), z(1), f(1)),
                    F::RangeInclusive => (z(0), f(0), z(0), f(1)),
                    F::RangeFrom => (z(0), f(0), z(2), z(0)),
                    F::RangeTo => (z(2), z(0), z(1), f(0)),
                    F::RangeToInclusive => (z(2), z(0), z(0), f(0)),
                    F::RangeFull => (z(2), z(0), z(2), z(0)),
                    F::Bounds | F::BoundsRef => {
                        let deref = form == F::BoundsRef;
                        let (stag, sval) = self.bound_side(pl.project(Proj::Field(0)), deref, span);
                        let (etag, eval) = self.bound_side(pl.project(Proj::Field(1)), deref, span);
                        (stag, sval, etag, eval)
                    }
                }
            }
            DR::Trait { start, end } => {
                let aty = self.ty(arg);
                let t = self.temp(aty);
                self.expr_into(arg, Some(&Place::local(t)));
                let mut side = |this: &mut Self, site: ExprId, f: LocalDefId| -> (Operand, Operand) {
                    let f = this.resolve_generic_fn(site, f);
                    let rt = this.ref_ty(false, aty);
                    let r = this.temp(rt);
                    this.assign(Place::local(r), Rvalue::Ref(false, Place::local(t)), span);
                    let bt = {
                        let rr = this.body.tys.mk_ref(false, USIZE);
                        crate::check::generics::bound_ty(&mut this.body.tys, rr)
                    };
                    let bt_l = this.temp(bt);
                    this.call_into(CallTarget::Fn(f), vec![Operand::Move(Place::local(r))], Place::local(bt_l), span);
                    this.bound_side(Place::local(bt_l), true, span)
                };
                let (stag, sval) = side(self, e, start);
                let (etag, eval) = side(self, arg, end);
                (stag, sval, etag, eval)
            }
            DR::Param => {
                let _ = self.operand(arg);
                (z(2), z(0), z(2), z(0))
            }
        }
    }

    /// The (tag, value) words of one `Bound<usize>` place, or of a
    /// `Bound<&usize>` place when `deref_payload` (the value is then
    /// read through the reference).
    fn bound_side(&mut self, pl: Place, deref_payload: bool, span: Span) -> (Operand, Operand) {
        let (tag, val) = (self.temp(USIZE), self.temp(USIZE));
        let z = |n: u64| Operand::Const(Const::Int(n as u128, IntTy::Usize));
        let d = self.temp(int(IntTy::U32));
        self.assign(Place::local(d), Rvalue::Discriminant(pl.clone()), span);
        let (inc_b, exc_b, unb_b, end) = (self.new_block(), self.new_block(), self.new_block(), self.new_block());
        let b = &mut self.body.blocks[self.cur.0 as usize];
        b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(0, inc_b), (1, exc_b)], unb_b);
        b.term_span = span;
        for (blk, variant) in [(inc_b, 0u32), (exc_b, 1u32)] {
            self.cur = blk;
            self.assign(Place::local(tag), Rvalue::Use(z(variant as u64)), span);
            let payload = pl.project(Proj::Downcast(variant)).project(Proj::Field(0));
            let payload = if deref_payload { payload.deref() } else { payload };
            self.assign(Place::local(val), Rvalue::Use(Operand::Copy(payload)), span);
            self.goto(end, span);
        }
        self.cur = unb_b;
        self.assign(Place::local(tag), Rvalue::Use(z(2)), span);
        self.assign(Place::local(val), Rvalue::Use(z(0)), span);
        self.goto(end, span);
        self.cur = end;
        (Operand::Copy(Place::local(tag)), Operand::Copy(Place::local(val)))
    }

    /// Calls the closure value at `place` (type `fty`) with no
    /// arguments through `FnOnce`, into `dest`: an `FnOnce` closure
    /// takes its env by value, the others by reference (the value
    /// itself then drops after the call, as the moved callee would).
    fn call_closure_once(&mut self, place: Place, fty: Ty, dest: Place, span: Span) {
        use crate::check::closure::ClosureKind;
        let TyKind::Closure(def, _) = self.kind(fty) else { return };
        let Some(entry) = self.p.gx.closures.get(&def) else { return };
        let (body_fn, kind) = (entry.body_fn, entry.kind);
        let env = match kind {
            ClosureKind::FnOnce => self.operand_from(place.clone(), fty),
            ClosureKind::Fn | ClosureKind::FnMut => {
                let mutable = kind == ClosureKind::FnMut;
                let rt = self.ref_ty(mutable, fty);
                let t = self.temp(rt);
                self.assign(Place::local(t), Rvalue::Ref(mutable, place.clone()), span);
                Operand::Move(Place::local(t))
            }
        };
        self.call_into(CallTarget::Fn(body_fn), vec![env], dest, span);
        if kind != ClosureKind::FnOnce && needs_drop(self.p, &self.body.tys, fty) {
            self.push(StmtKind::Drop(place.local), span);
        }
    }

    /// One `PartialOrd` test `a <op> b` between two places of type
    /// `ty` for `Res::OrdPick`, into a fresh `bool` local: through the
    /// written method `f` (`via`), or by structure.
    fn pick_cmp(&mut self, f: Option<LocalDefId>, via: CmpVia, op: BinOp, a: &Place, b: &Place, ty: Ty, span: Span) -> Local {
        let c = self.temp(BOOL);
        let rt = self.ref_ty(false, ty);
        let (ra, rb) = (self.temp(rt), self.temp(rt));
        self.assign(Place::local(ra), Rvalue::Ref(false, a.clone()), span);
        self.assign(Place::local(rb), Rvalue::Ref(false, b.clone()), span);
        let (ra, rb) = (Operand::Copy(Place::local(ra)), Operand::Copy(Place::local(rb)));
        match f {
            Some(f) => {
                // `max`/`min` may call the impl's own `lt`; every other
                // test goes through `partial_cmp`.
                let via = if op == BinOp::Lt { via } else { CmpVia::Partial(op) };
                self.trait_cmp_call(f, ra, rb, via, Place::local(c), span);
            }
            None => {
                // `Ord for &A` compares the pointees.
                let (mut a, mut b, mut ty, mut ra, mut rb) = (a.clone(), b.clone(), ty, ra, rb);
                while let TyKind::Ref(_, _, inner) = self.kind(ty) {
                    (ra, rb) = (Operand::Copy(a.clone()), Operand::Copy(b.clone()));
                    (a, b, ty) = (a.deref(), b.deref(), inner);
                }
                let rv = match self.kind(ty) {
                    TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char => Rvalue::Bin(op, Operand::Copy(a), Operand::Copy(b)),
                    // `ra`/`rb` are the `&str` views themselves.
                    TyKind::Str => Rvalue::StrCmp(op, ra, rb),
                    _ => Rvalue::Cmp { op, a: ra, b: rb, ty },
                };
                self.assign(Place::local(c), rv, span);
            }
        }
        c
    }

    /// `Ord::max`, `min`, and `clamp` (`Res::OrdPick`) by core's
    /// default bodies: the receiver and the arguments move into
    /// locals in order, the comparisons run as in core
    /// (`max`/`min`: `other < self`; `clamp`: `assert!(min <= max)`,
    /// then `self < min`, then `self > max`), the answer moves out,
    /// and the other values drop right there, in reverse parameter
    /// order, as the callee's parameters would.
    #[allow(clippy::too_many_arguments)]
    fn ord_pick_into(
        &mut self,
        e: ExprId,
        recv: ExprId,
        args: &[ExprId],
        dest: Option<&Place>,
        span: Span,
        kind: OrdPickKind,
        f: Option<LocalDefId>,
        via: CmpVia,
    ) {
        let ty = self.ty(e);
        let mut vals: Vec<Local> = Vec::with_capacity(args.len() + 1);
        for &x in std::iter::once(&recv).chain(args) {
            let l = self.temp(ty);
            self.expr_into(x, Some(&Place::local(l)));
            vals.push(l);
        }
        let out = self.call_dest(dest, ty);
        let pl = |l: Local| Place::local(l);
        // Moves value `win` into `out`, then drops the others in
        // reverse parameter order.
        let finish = |this: &mut Self, win: usize, vals: &[Local], end: Bb| {
            let op = this.operand_from(pl(vals[win]), ty);
            this.assign(out.clone(), Rvalue::Use(op), span);
            for (i, &l) in vals.iter().enumerate().rev() {
                if i != win && needs_drop(this.p, &this.body.tys, ty) {
                    this.push(StmtKind::Drop(l), span);
                }
            }
            this.goto(end, span);
        };
        let end = self.new_block();
        let branch = |this: &mut Self, c: Local| -> (Bb, Bb) {
            let (t, f) = (this.new_block(), this.new_block());
            let b = &mut this.body.blocks[this.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), t, f);
            b.term_span = span;
            (t, f)
        };
        match kind {
            OrdPickKind::Max | OrdPickKind::Min => {
                // `other < self`: Max keeps self, Min keeps other.
                let c = self.pick_cmp(f, via, BinOp::Lt, &pl(vals[1]), &pl(vals[0]), ty, span);
                let (t, el) = branch(self, c);
                let (on_true, on_false) = if kind == OrdPickKind::Max { (0, 1) } else { (1, 0) };
                self.cur = t;
                finish(self, on_true, &vals, end);
                self.cur = el;
                finish(self, on_false, &vals, end);
            }
            OrdPickKind::Clamp => {
                let ok = self.pick_cmp(f, via, BinOp::Le, &pl(vals[1]), &pl(vals[2]), ty, span);
                let (good, bad) = branch(self, ok);
                self.cur = bad;
                // Integer and char `clamp` panic at the caller with the
                // bounds in the text; `Ord::clamp` and bool's own `clamp`
                // assert inside core's cmp.rs.
                let prim = matches!(self.kind(ty), TyKind::Int(_) | TyKind::Char);
                let site = if prim { span } else if matches!(self.kind(ty), TyKind::Bool) { Span::std_site(4, 2303, 13) } else { Span::std_site(4, 1115, 9) };
                let parts = if prim {
                    // A format argument is a reference to the value.
                    let dbg = FmtSpec { kind: FmtKind::Debug, ..FmtSpec::default() };
                    let arg = |this: &mut Self, v: Local| {
                        let rt = this.ref_ty(false, ty);
                        let r = this.temp(rt);
                        this.assign(Place::local(r), Rvalue::Ref(false, Place::local(v)), span);
                        FmtPart::Arg { value: Operand::Copy(Place::local(r)), ty, debug: true, spec: dbg, width: None, prec: None }
                    };
                    let (lo, hi) = (arg(self, vals[1]), arg(self, vals[2]));
                    vec![FmtPart::Lit("min > max. min = ".into()), lo, FmtPart::Lit(", max = ".into()), hi]
                } else {
                    vec![FmtPart::Lit("assertion failed: min <= max".into())]
                };
                self.terminate(Terminator::Panic(parts), site);
                self.cur = good;
                let below = self.pick_cmp(f, via, BinOp::Lt, &pl(vals[0]), &pl(vals[1]), ty, span);
                let (t, el) = branch(self, below);
                self.cur = t;
                finish(self, 1, &vals, end);
                self.cur = el;
                let above = self.pick_cmp(f, via, BinOp::Gt, &pl(vals[0]), &pl(vals[2]), ty, span);
                let (t2, el2) = branch(self, above);
                self.cur = t2;
                finish(self, 2, &vals, end);
                self.cur = el2;
                finish(self, 0, &vals, end);
            }
        }
        self.cur = end;
    }

    /// A scalar operator trait method (`Res::PrimOp`): the
    /// One scalar `TryFrom` checked cast (check/tryfrom.rs):
    /// `Ok(cast)` when the value fits the target, else `Err` of
    /// the pair's error type. An `Infallible` pair is a plain cast
    /// in `Ok`. Integer ranges compare in `i128` (a `u128` source
    /// compares in `u128` against the target's max), so every
    /// pair takes the same shape.
    fn try_cast_into(&mut self, op: Operand, src_ty: Ty, result_ty: Ty, dest: Option<&Place>, span: Span) {
        use crate::check::generics as gdef;
        let Some((dst_ty, err_ty)) = self.body.tys.result_args(result_ty) else { return };
        let d = self.call_dest(dest, result_ty);
        let s = self.temp(src_ty);
        self.assign(Place::local(s), Rvalue::Use(op), span);
        let copy_s = Operand::Copy(Place::local(s));
        let err_def = self.body.tys.adt_parts(err_ty).map(|(x, _)| x);
        // In a template the error is still the `TryInto::Error`
        // projection; the destination shape tells the slice form.
        let dst_arrayish = match self.kind(dst_ty) {
            TyKind::Array(..) => true,
            TyKind::Ref(_, _, i) => matches!(self.kind(i), TyKind::Array(..)),
            _ => false,
        };
        if crate::check::tryfrom::owned_try_parts(&self.body.tys, src_ty, dst_ty).is_some() {
            // Alloc's `TryFrom<Vec<T>> for [T; N]` and the boxed-array
            // pairs: the source moves in.
            self.call_into(CallTarget::Builtin(Builtin::VecTryInto), vec![Operand::Move(Place::local(s))], d, span);
            return;
        }
        if err_def == Some(gdef::try_from_slice_error_def()) || (dst_arrayish && matches!(self.kind(src_ty), TyKind::Slice(_) | TyKind::Array(..) | TyKind::Ref(..))) {
            // A slice-to-array conversion (tf-slice): an array
            // source first becomes its slice; the destination type
            // tells cgen the length and form.
            let s_op = match self.kind(src_ty) {
                TyKind::Array(el, _) => {
                    let sl = self.body.tys.intern(TyKind::Slice(el));
                    let rt = self.ref_ty(false, sl);
                    let t = self.temp(rt);
                    self.assign(Place::local(t), Rvalue::SliceOf(Place::local(s)), span);
                    Operand::Move(Place::local(t))
                }
                _ => Operand::Move(Place::local(s)),
            };
            self.call_into(CallTarget::Builtin(Builtin::SliceTryInto), vec![s_op], d, span);
            return;
        }
        if err_def == Some(gdef::infallible_def()) {
            let c = self.temp(dst_ty);
            self.assign(Place::local(c), Rvalue::Cast(copy_s, dst_ty), span);
            self.assign(d, Rvalue::Res(result_ty, true, Operand::Move(Place::local(c))), span);
            return;
        }
        // (fits, too-large) as bool temps; `okval` precomputes the
        // `Ok` payload when it is not a cast (integer to `bool`).
        let bin = |cx: &mut Self, op: BinOp, a: Operand, b: Operand| -> Local {
            let t = cx.temp(BOOL);
            cx.assign(Place::local(t), Rvalue::Bin(op, a, b), span);
            t
        };
        let konst = |v: bool| Operand::Const(Const::Bool(v));
        let (ok, pos, okval): (Local, Operand, Option<Local>) = match (self.kind(src_ty), self.kind(dst_ty)) {
            (TyKind::Int(si), TyKind::Int(di)) => {
                let bits = di.bits();
                if si == IntTy::U128 {
                    let max: u128 = if di.signed() {
                        (1u128 << (bits - 1)) - 1
                    } else if bits >= 128 {
                        u128::MAX
                    } else {
                        (1u128 << bits) - 1
                    };
                    let ok = bin(self, BinOp::Le, copy_s, Operand::Const(Const::Int(max, IntTy::U128)));
                    (ok, konst(true), None)
                } else if si.bits() <= 64 {
                    // In i64 or u64, which hold every source value: the target's bounds
                    // clamp to that range (a bound outside it always holds).
                    let wt = if si.signed() { IntTy::I64 } else { IntTy::U64 };
                    let w = self.temp(int(wt));
                    self.assign(Place::local(w), Rvalue::Cast(copy_s, int(wt)), span);
                    let wc = Operand::Copy(Place::local(w));
                    let (lo, hi): (i128, i128) = if si.signed() { (i64::MIN.into(), i64::MAX.into()) } else { (0, u64::MAX.into()) };
                    let (min, max): (i128, i128) = if di.signed() {
                        (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
                    } else {
                        (0, if bits >= 128 { i128::MAX } else { (1i128 << bits) - 1 })
                    };
                    let (min, max) = (min.max(lo), max.min(hi));
                    let ge = bin(self, BinOp::Ge, wc.clone(), Operand::Const(Const::Int(min as u128, wt)));
                    let le = bin(self, BinOp::Le, wc.clone(), Operand::Const(Const::Int(max as u128, wt)));
                    let ok = bin(self, BinOp::BitAnd, Operand::Copy(Place::local(ge)), Operand::Copy(Place::local(le)));
                    let pos = bin(self, BinOp::Gt, wc, Operand::Const(Const::Int(max as u128, wt)));
                    (ok, Operand::Copy(Place::local(pos)), None)
                } else {
                    let i128t = int(IntTy::I128);
                    let w = self.temp(i128t);
                    self.assign(Place::local(w), Rvalue::Cast(copy_s, i128t), span);
                    let wc = Operand::Copy(Place::local(w));
                    if di == IntTy::U128 {
                        let ok = bin(self, BinOp::Ge, wc, Operand::Const(Const::Int(0, IntTy::I128)));
                        (ok, konst(false), None)
                    } else {
                        let (min, max): (i128, i128) = if di.signed() {
                            (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
                        } else {
                            (0, (1i128 << bits) - 1)
                        };
                        let ge = bin(self, BinOp::Ge, wc.clone(), Operand::Const(Const::Int(min as u128, IntTy::I128)));
                        let le = bin(self, BinOp::Le, wc.clone(), Operand::Const(Const::Int(max as u128, IntTy::I128)));
                        let ok = bin(self, BinOp::BitAnd, Operand::Copy(Place::local(ge)), Operand::Copy(Place::local(le)));
                        let pos = bin(self, BinOp::Gt, wc, Operand::Const(Const::Int(max as u128, IntTy::I128)));
                        (ok, Operand::Copy(Place::local(pos)), None)
                    }
                }
            }
            (TyKind::Int(si), TyKind::Bool) => {
                let (z, o) = (Operand::Const(Const::Int(0, si)), Operand::Const(Const::Int(1, si)));
                let e0 = bin(self, BinOp::Eq, copy_s.clone(), z.clone());
                let e1 = bin(self, BinOp::Eq, copy_s.clone(), o.clone());
                let ok = bin(self, BinOp::BitOr, Operand::Copy(Place::local(e0)), Operand::Copy(Place::local(e1)));
                let val = bin(self, BinOp::Ne, copy_s.clone(), z);
                let pos = bin(self, BinOp::Gt, copy_s, o);
                (ok, Operand::Copy(Place::local(pos)), Some(val))
            }
            (TyKind::Int(IntTy::U32), TyKind::Char) => {
                let c = |v: u128| Operand::Const(Const::Int(v, IntTy::U32));
                let le = bin(self, BinOp::Le, copy_s.clone(), c(0x10FFFF));
                let lo = bin(self, BinOp::Lt, copy_s.clone(), c(0xD800));
                let hi = bin(self, BinOp::Gt, copy_s, c(0xDFFF));
                let mid = bin(self, BinOp::BitOr, Operand::Copy(Place::local(lo)), Operand::Copy(Place::local(hi)));
                let ok = bin(self, BinOp::BitAnd, Operand::Copy(Place::local(le)), Operand::Copy(Place::local(mid)));
                (ok, konst(true), None)
            }
            (TyKind::Char, TyKind::Int(di)) => {
                let u32t = int(IntTy::U32);
                let w = self.temp(u32t);
                self.assign(Place::local(w), Rvalue::Cast(copy_s, u32t), span);
                let max: u128 = match di {
                    IntTy::U8 => 0xFF,
                    IntTy::U16 => 0xFFFF,
                    _ => 0xFFFF_FFFF,
                };
                let ok = bin(self, BinOp::Le, Operand::Copy(Place::local(w)), Operand::Const(Const::Int(max, IntTy::U32)));
                (ok, konst(true), None)
            }
            // The checker gates the pairs; a pair that still
            // reaches here widens (its error is `Infallible`,
            // handled above), so it always fits.
            _ => {
                let t = self.temp(BOOL);
                self.assign(Place::local(t), Rvalue::Use(konst(true)), span);
                (t, konst(true), None)
            }
        };
        let ok_bb = self.new_block();
        let err_bb = self.new_block();
        let join = self.new_block();
        {
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(ok)), vec![(1, ok_bb)], err_bb);
            b.term_span = span;
        }
        self.cur = ok_bb;
        let oval = match okval {
            Some(v) => Operand::Copy(Place::local(v)),
            None => {
                let c = self.temp(dst_ty);
                self.assign(Place::local(c), Rvalue::Cast(Operand::Copy(Place::local(s)), dst_ty), span);
                Operand::Move(Place::local(c))
            }
        };
        self.assign(d.clone(), Rvalue::Res(result_ty, true, oval), span);
        self.goto(join, span);
        self.cur = err_bb;
        // The error value: a kinded `TryFromIntError`, or a char
        // error over `()`.
        let is_int_err = err_def == Some(gdef::try_from_int_error_def());
        let err_adt = self.body.tys.local_adt(err_ty);
        if is_int_err && let (Some(ea), Some(ka)) = (err_adt, self.body.tys.local_adt_of(gdef::int_error_kind_def())) {
            let variant = |cx: &Self, name: &str| -> u32 {
                cx.p.adt(ka).variants.iter().position(|v| cx.p.interner.get(v.name) == name).unwrap_or(0) as u32
            };
            let (pos_v, neg_v) = (variant(self, "PosOverflow"), variant(self, "NegOverflow"));
            let kind_ty = self.body.tys.intern(TyKind::Adt(gdef::int_error_kind_def(), EMPTY_ARGS));
            let pos_bb = self.new_block();
            let neg_bb = self.new_block();
            {
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::Switch(pos, vec![(1, pos_bb)], neg_bb);
                b.term_span = span;
            }
            for (bb, v) in [(pos_bb, pos_v), (neg_bb, neg_v)] {
                self.cur = bb;
                let k = self.temp(kind_ty);
                self.assign(Place::local(k), Rvalue::Aggregate(ka, v, Vec::new()), span);
                let et = self.temp(err_ty);
                self.assign(Place::local(et), Rvalue::Aggregate(ea, 0, vec![Operand::Move(Place::local(k))]), span);
                self.assign(d.clone(), Rvalue::Res(result_ty, false, Operand::Move(Place::local(et))), span);
                self.goto(join, span);
            }
        } else if let Some(ea) = err_adt {
            let et = self.temp(err_ty);
            self.assign(Place::local(et), Rvalue::Aggregate(ea, 0, vec![Operand::Const(Const::Unit)]), span);
            self.assign(d.clone(), Rvalue::Res(result_ty, false, Operand::Move(Place::local(et))), span);
            self.goto(join, span);
        } else {
            self.goto(join, span);
        }
        self.cur = join;
    }

    /// operation itself on the receiver value (by-value `self`),
    /// a unary operation, or a compound assignment into the
    /// receiver place, exactly as the operators lower.
    fn prim_op_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], dest: Option<&Place>, span: Span, kind: PrimOpKind, derefs: u8) {
        use PrimOpKind as K;
        match kind {
            K::Bin(op) => {
                if args.is_empty() {
                    return;
                }
                let a = self.operand_derefs(recv, derefs);
                let b = self.operand(args[0]);
                let recv_ty = self.peel(self.ty(recv), derefs);
                if op == BinOp::Add && self.body.tys.is_string_ty(recv_ty) {
                    self.set_or_temp(dest, Rvalue::StringAdd(a, b), self.ty(e), span);
                } else {
                    self.set_or_temp(dest, Rvalue::Bin(op, a, b), self.ty(e), span);
                }
            }
            K::Un(op) => {
                let a = self.operand_derefs(recv, derefs);
                // `(&x).neg()` runs `impl Neg for &i32`, as `-&x` does.
                let ty = self.ty(e);
                let span = if op == crate::ast::UnOp::Neg && derefs > 0 && matches!(self.kind(ty), TyKind::Int(_)) {
                    Span::std_site(11, 728, 1)
                } else {
                    span
                };
                self.set_or_temp(dest, Rvalue::Un(op, a), ty, span);
            }
            K::IntoCast => {
                let a = self.operand_derefs(recv, derefs);
                self.set_or_temp(dest, Rvalue::Cast(a, self.ty(e)), self.ty(e), span);
            }
            K::TryIntoCast => {
                // A slice-to-array cast (tf-slice) reads the
                // receiver value itself (the fat slice, Copy for
                // `&[T]`), not a move out of its deref.
                let result_ty = self.ty(e);
                let is_slice_try = self.body.tys.result_args(result_ty).is_some_and(|(_, err)| {
                    self.body.tys.adt_parts(err).map(|(d, _)| d) == Some(crate::check::generics::try_from_slice_error_def())
                }) || matches!(self.kind(self.peel(self.ty(recv), derefs)), TyKind::Slice(_));
                if is_slice_try {
                    let a = self.operand(recv);
                    let src_ty = self.ty(recv);
                    self.try_cast_into(a, src_ty, result_ty, dest, span);
                } else {
                    let a = self.operand_derefs(recv, derefs);
                    let src_ty = self.peel(self.ty(recv), derefs);
                    self.try_cast_into(a, src_ty, result_ty, dest, span);
                }
            }
            // core's blanket `IntoIterator for I: Iterator`: the receiver moves through.
            K::IntoIterSelf => {
                let a = self.operand_derefs(recv, derefs);
                self.set_or_temp(dest, Rvalue::Use(a), self.ty(e), span);
            }
            K::Assign(op) => {
                if args.is_empty() {
                    return;
                }
                let r = self.operand(args[0]);
                let pl = Self::derefs(self.place_for_mut(recv), derefs);
                self.assign(pl.clone(), Rvalue::Bin(op, Operand::Copy(pl), r), span);
                self.unit(dest, span);
            }
        }
    }

    /// The `&str` operand a Cow addition reads: the operand itself
    /// for a `&str` right side, or the view of a Cow right side
    /// (moved into a temp that drops at scope end, as the consumed
    /// `Add<Cow>` argument does).
    fn cow_add_rhs(&mut self, rhs: ExprId, span: Span) -> Operand {
        let rt = self.ty(rhs);
        if crate::check::collect::cow_arg(&self.body.tys, rt).is_none() {
            return self.operand(rhs);
        }
        let a = self.operand(rhs);
        let t = self.temp(rt);
        self.assign(Place::local(t), Rvalue::Use(a), span);
        let rt_ref = self.ref_ty(false, rt);
        let r = self.temp(rt_ref);
        self.assign(Place::local(r), Rvalue::Ref(false, Place::local(t)), span);
        let v = self.temp(REF_STR);
        self.call_into(CallTarget::Builtin(Builtin::CowDeref), vec![Operand::Copy(Place::local(r))], Place::local(v), span);
        Operand::Copy(Place::local(v))
    }

    /// The `&B` view of the `Cow<B>` that `n` derefs of `e` reach
    /// (W-STD-B): a shared borrow of the Cow, then its `Deref` builtin.
    fn cow_view_of(&mut self, e: ExprId, n: u8, view: Ty) -> Local {
        let span = self.span(e);
        // Lower the Cow expression itself, not its view (the guard
        // also stops `place(e)` here from recursing into this fn).
        let saved = std::mem::replace(&mut self.making_cow_view, Some(e));
        let pl = Self::derefs(self.place(e), n);
        let cow = self.peel(self.ty(e), n);
        self.making_cow_view = saved;
        let rt = self.ref_ty(false, cow);
        let r = self.temp(rt);
        self.assign(Place::local(r), Rvalue::Ref(false, pl), span);
        let v = self.temp(view);
        self.call_into(CallTarget::Builtin(Builtin::CowDeref), vec![Operand::Copy(Place::local(r))], Place::local(v), span);
        v
    }

    /// The operands of a list of expressions evaluated left to right (call
    /// arguments, tuple and array elements, `vec!`): a place operand is
    /// copied or moved into a temporary where it is evaluated when a later
    /// operand can write or move it (`(x, { x += 1; x })` is `(1, 2)`, and
    /// `f(r, r.len())` uses `r` after the move: rustc E0382). Struct
    /// literals do the same for their fields.
    pub(super) fn ordered_operands(&mut self, es: &[ExprId]) -> Vec<Operand> {
        (0..es.len()).map(|i| self.ordered_operand(es, i)).collect()
    }

    /// Operand `i` of `es` under the `ordered_operands` rule.
    fn ordered_operand(&mut self, es: &[ExprId], i: usize) -> Operand {
        let e = es[i];
        let o = self.operand(e);
        // A later `&mut` path argument is a reborrow (or a move) of its
        // place at that argument (`f(c.p, c)` with `c: &mut S`): this one's
        // value is read before it, as in rustc.
        let later_effects = es[i + 1..].iter().any(|&x| !self.inert_expr(x) || self.mut_ref_path(x));
        match o {
            Operand::Copy(ref pl) | Operand::Move(ref pl)
                if later_effects && !(pl.proj.is_empty() && self.body.locals[pl.local as usize].name.is_none()) =>
            {
                let ft = self.coerced_ty(e);
                let t = self.temp(ft);
                let span = self.span(e);
                self.assign(Place::local(t), Rvalue::Use(o), span);
                self.operand_from(Place::local(t), ft)
            }
            o => o,
        }
    }

    /// True when `e` is a path or `self` of `&mut` type: as an argument it
    /// is reborrowed or moved (`ordered_operand`).
    fn mut_ref_path(&self, e: ExprId) -> bool {
        matches!(self.p.ast.expr(e), Expr::Path(_) | Expr::SelfValue) && matches!(self.kind(self.ty(e)), TyKind::Ref(_, Mut::Mut, _))
    }

    /// True when evaluating `e` cannot write or move a place: a literal or
    /// a plain path (`ordered_operands`).
    fn inert_expr(&self, e: ExprId) -> bool {
        matches!(
            self.p.ast.expr(e),
            Expr::Int(..) | Expr::Float(_) | Expr::Bool(_) | Expr::Char(_) | Expr::Str(_) | Expr::ByteStr(_) | Expr::Unit | Expr::Path(_) | Expr::SelfValue
        )
    }

    /// The operands of call arguments `args` (after any receiver or
    /// closure env) in the `ordered_operands` order, where each `&mut`
    /// place that argument coercion reborrows and a later argument follows
    /// (`f(nodes, nodes.len())`, `cb(1, self, id(&self.syms))`, `g(a, b,
    /// a.len() + b.len())`) is two-phase, as rustc's argument coercion
    /// reborrow is: lowered as a method receiver's (a shared reservation
    /// while the later arguments run, `FakeRead`, then the `&mut`;
    /// `two_phase_loans` in borrowck). A place through an index (`v[0]` is
    /// an `IndexMut` borrow in rustc, not two-phase) takes its `&mut` at
    /// once.
    pub(super) fn call_arg_operands(&mut self, args: &[ExprId], span: Span) -> Vec<Operand> {
        let (mut ops, pending) = self.call_arg_reserved(args, span);
        self.activate_two_phase(&mut ops, pending, span);
        ops
    }

    /// `call_arg_operands` without the activations: the operands, with a
    /// placeholder at each two-phase argument, and per such argument its
    /// operand index, reservation local and place (`activate_two_phase`
    /// makes the `&mut`s, after a two-phase receiver's own).
    fn call_arg_reserved(&mut self, args: &[ExprId], span: Span) -> (Vec<Operand>, Vec<(usize, Local, Place)>) {
        let mut ops = Vec::with_capacity(args.len());
        let mut pending = Vec::new();
        for i in 0..args.len() {
            if i + 1 == args.len() || self.ck.coerce(args[i]) != Coerce::Reborrow || !self.is_place_expr(args[i]) {
                let o = self.ordered_operand(args, i);
                ops.push(o);
                continue;
            }
            let pl = self.place(args[i]).deref();
            let inner = self.peel(self.ty(args[i]), 1);
            if pl.proj.iter().any(|x| matches!(x, Proj::Index(_))) {
                let mt = self.ref_ty(true, inner);
                let t = self.temp(mt);
                self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
                ops.push(Operand::Move(Place::local(t)));
                continue;
            }
            let st = self.ref_ty(false, inner);
            let reserve = self.temp(st);
            self.assign(Place::local(reserve), Rvalue::Ref(false, pl.clone()), span);
            pending.push((ops.len(), reserve, pl));
            ops.push(Operand::Copy(Place::local(reserve)));
        }
        (ops, pending)
    }

    /// The activations of `call_arg_reserved`'s two-phase arguments, in
    /// order: `FakeRead` of the reservation, then the `&mut`, which
    /// replaces the placeholder operand.
    fn activate_two_phase(&mut self, ops: &mut [Operand], pending: Vec<(usize, Local, Place)>, span: Span) {
        for (at, reserve, pl) in pending {
            let inner = self.peel(self.body.locals[reserve as usize].ty, 1);
            let mt = self.ref_ty(true, inner);
            self.push(StmtKind::FakeRead(reserve), span);
            let t = self.temp(mt);
            self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
            ops[at] = Operand::Move(Place::local(t));
        }
    }

    /// The autoref of a range-indexed receiver (`v[1..].iter()`,
    /// `s[2..].into()`, `v[1..].sort()`) when `direct` (no derefs, no
    /// user `Deref`): a local holding the `&[T]`/`&str` (or `&mut`).
    /// The slice place is already a fat value in a temporary with its
    /// loan on the base, so the reference moves that value, as
    /// `&v[1..]` does; a borrow of the temporary would end at the
    /// statement. None for every other receiver.
    fn slice_index_recv_ref(&mut self, recv: ExprId, direct: bool, m: bool, recv_ty: Ty, span: Span) -> Option<Local> {
        if !direct || !matches!(self.ck.res(recv), Res::SliceIndex { .. }) {
            return None;
        }
        let pl = if m { self.place_for_mut(recv) } else { self.place(recv) };
        let rt = self.ref_ty(m, recv_ty);
        let op = self.operand_from(pl, rt);
        let t = self.temp(rt);
        self.assign(Place::local(t), Rvalue::Use(op), span);
        Some(t)
    }

    fn method_into(&mut self, e: ExprId, recv: ExprId, args: &[ExprId], dest: Option<&Place>, span: Span) {
        // A method call reports caller locations (track_caller builtins
        // such as unwrap and pow) at the method name, as rustc does, not
        // at the receiver. A qualified-path call (`Type::name(..)`) is a
        // plain call here and keeps the whole-expression span.
        let span = match self.p.ast.expr(e) {
            Expr::MethodCall { name_span, .. } => *name_span,
            _ => span,
        };
        // A receiver through a Cow's `Deref` (W-STD-B): borrow the Cow,
        // make its `&B` view (before the arguments, as rustc adjusts the
        // receiver first), then lower the call on the view.
        // An iterator receiver moved into its `ByNext` wrapper (W-STD-B).
        if let Coerce::ByNext(w) = self.ck.coerce(recv)
            && self.cow_view.is_none_or(|(x, ..)| x != recv)
        {
            // A `&mut I` place receiver is reborrowed (`&mut *r`), as rustc
            // adjusts a `&mut` method receiver; it is not moved.
            let held = crate::ty::iter::iter_parts(&self.body.tys, w).and_then(|(_, a)| a.first().copied());
            let o = match held {
                Some(h) if matches!(self.kind(h), TyKind::Ref(_, Mut::Mut, _)) && self.is_place_expr(recv) => {
                    let pl = self.place_for_mut(recv);
                    let t = self.temp(h);
                    self.assign(Place::local(t), Rvalue::Ref(true, pl.deref()), span);
                    Operand::Move(Place::local(t))
                }
                _ => self.operand_raw(recv),
            };
            let v = self.temp(w);
            self.assign(Place::local(v), Rvalue::TupleAgg(w, vec![o]), span);
            let saved = self.cow_view.replace((recv, v, w));
            self.method_into(e, recv, args, dest, span);
            self.cow_view = saved;
            return;
        }
        if let Coerce::CowRecv(n, view) = self.ck.coerce(recv)
            && self.cow_view.is_none_or(|(x, ..)| x != recv)
        {
            let v = self.cow_view_of(recv, n, view);
            let saved = self.cow_view.replace((recv, v, view));
            self.method_into(e, recv, args, dest, span);
            self.cow_view = saved;
            return;
        }
        if let Res::BuiltinMethod { b: Builtin::FmtWriteFmt, derefs, .. } = self.ck.res(e) {
            self.write_fmt_into(e, recv, args, derefs, dest, span, None);
            return;
        }
        // `io::Write::write_fmt` on std's stdout or stderr types (and
        // their locks): stream the parts through the locked stream as
        // they format, like `print!`, instead of calling the platform
        // default with an already formatted `Arguments` text. A print
        // inside a fmt impl then comes out between the parts around
        // it, as in rustc. Other writers keep the platform call.
        if let Res::Method { f, derefs, .. } = self.ck.res(e)
            && crate::check::platform::is_platform_write_fmt(self.p, f)
            && let Some(stderr) = self.stream_kind(self.ty(recv))
            && matches!(args.first().map(|&a| self.p.ast.expr(a)), Some(Expr::Macro { kind: MacroKind::FormatArgs, .. }))
        {
            self.write_fmt_into(e, recv, args, derefs, dest, span, Some(stderr));
            return;
        }
        if let Res::BuiltinMethod { b: Builtin::VecDrain | Builtin::StringDrain, derefs, .. } = self.ck.res(e) {
            self.drain_into(e, recv, args, derefs, dest, span);
            return;
        }
        if let Res::BuiltinMethod { b: Builtin::VecSplice, derefs, .. } = self.ck.res(e) {
            self.splice_into(e, recv, args, derefs, dest, span);
            return;
        }
        if let Res::BuiltinMethod { b: Builtin::SliceCopyWithin | Builtin::VecExtendFromWithin, derefs, .. } = self.ck.res(e) {
            self.copy_within_into(e, recv, args, derefs, dest, span);
            return;
        }
        if let Res::BuiltinMethod { b, derefs, .. } = self.ck.res(e)
            && matches!(b, Builtin::SliceGetRange | Builtin::SliceGetRangeMut | Builtin::StrGetRange)
        {
            let mutable = b == Builtin::SliceGetRangeMut;
            self.get_range_into(e, recv, args, derefs, dest, span, mutable);
            return;
        }
        // `x.eq(y)` / `x.ne(y)` across std types (check's `cmp_cross_eq`):
        // the operator `Self == R`, with depths from `recv` and the arg.
        if let Res::Bin { .. } = self.ck.res(e)
            && let Expr::MethodCall { name, .. } = self.p.ast.expr(e)
            && let [arg] = args
        {
            let op = if self.p.name(*name) == "ne" { BinOp::Ne } else { BinOp::Eq };
            self.binary_into(e, op, recv, *arg, dest, span);
            return;
        }
        if let Res::PrimCmp { kind, derefs } = self.ck.res(e) {
            self.prim_cmp_into(e, recv, args, dest, span, kind, derefs);
            return;
        }
        if let Res::TraitCmpMethod { f, derefs, via } = self.ck.res(e) {
            let f = self.resolve_generic_fn(e, f);
            let recv_ty = self.peel(self.ty(recv), derefs);
            let pl = Self::derefs(self.place(recv), derefs);
            let rt_ty = self.ref_ty(false, recv_ty);
            let rt = self.temp(rt_ty);
            self.assign(Place::local(rt), Rvalue::Ref(false, pl), span);
            let b = self.operand(args[0]);
            let out = self.call_dest(dest, BOOL);
            self.trait_cmp_call(f, Operand::Copy(Place::local(rt)), b, via, out, span);
            return;
        }
        if let Res::OrderingOp { kind, derefs } = self.ck.res(e) {
            self.ordering_op_into(e, recv, args, dest, span, kind, derefs);
            return;
        }
        if let Res::Any { op, derefs, autoref } = self.ck.res(e) {
            self.any_op_into(e, recv, dest, span, op, derefs, autoref);
            return;
        }
        if let Res::OrdPick { kind, f, via } = self.ck.res(e) {
            let f = f.map(|f| self.resolve_generic_fn(e, f));
            self.ord_pick_into(e, recv, args, dest, span, kind, f, via);
            return;
        }
        if let Res::PrimOp { kind, derefs } = self.ck.res(e) {
            self.prim_op_into(e, recv, args, dest, span, kind, derefs);
            return;
        }
        // `guard.deref()` / `guard.deref_mut()` on a `RefCell` or lock
        // guard (check/convert.rs `deref_call`): a reborrow of the
        // guard's target place, as `&*guard` lowers.
        if let Res::BuiltinMethod { b: Builtin::ConvDeref, derefs, autoref } = self.ck.res(e)
            && args.is_empty()
            && self.body.tys.guard_elem(self.peel(self.ty(recv), derefs)).is_some()
        {
            let m = autoref == Autoref::RefMut;
            let pl = if m { self.place_for_mut(recv) } else { self.place(recv) };
            let target = self.peel(self.ty(recv), derefs + 1);
            let rt = self.ref_ty(m, target);
            let out = self.call_dest(dest, rt);
            self.assign(out, Rvalue::Ref(m, Self::derefs(pl, derefs + 1)), span);
            return;
        }
        /// What a method call calls once its receiver is in place.
        enum Callee {
            Fn(LocalDefId),
            Builtin(Builtin),
            /// Through the vtable: the declaring trait, its object
            /// candidate index, and the slot.
            Dyn(DefId, u8, u32),
        }
        let (callee, derefs, autoref) = match self.ck.res(e) {
            Res::Method { f, derefs, autoref } => (Callee::Fn(f), derefs, autoref),
            Res::BuiltinMethod { b, derefs, autoref } => (Callee::Builtin(b), derefs, autoref),
            Res::DynMethod { owner, cand, slot, derefs, autoref } => (Callee::Dyn(owner, cand, slot), derefs, autoref),
            _ => return,
        };
        // Through a user `Deref` impl (check's `DerefRecv`): borrow the
        // receiver, call the impl's `deref` (or `deref_mut`), and apply
        // the call's derefs and autoref to the `&Target` it returns.
        let root = self.deref_steps(e, recv, span);
        let root_ty = match &root {
            Some(pl) => self.body.locals[pl.local as usize].ty,
            None => self.ty(recv),
        };
        let recv_ty = self.peel(root_ty, derefs);
        // `KEY.with(Cell::get)`: the std fn path is no operand (lower/tls.rs).
        let args = match callee {
            Callee::Builtin(b) if tls::takes_no_args(b) => &[][..],
            _ => args,
        };
        let mut ops = Vec::with_capacity(args.len() + 1);
        match autoref {
            Autoref::None => {
                let o = match &root {
                    Some(pl) if derefs == 0 && self.view_moved(recv) => Operand::Move(pl.clone()),
                    Some(pl) => self.operand_from(Self::derefs(pl.clone(), derefs), recv_ty),
                    None => self.operand_derefs(recv, derefs),
                };
                // A by-value receiver place is read before the arguments
                // run, as each argument is (`ordered_operands`): rustc
                // copies `self.tracer` in `self.tracer.map(|t| self.bump())`
                // to a temporary first.
                let o = match o {
                    Operand::Copy(ref pl) | Operand::Move(ref pl)
                        if args.iter().any(|&x| !self.inert_expr(x)) && !(pl.proj.is_empty() && self.body.locals[pl.local as usize].name.is_none()) =>
                    {
                        let t = self.temp(recv_ty);
                        self.assign(Place::local(t), Rvalue::Use(o), span);
                        self.operand_from(Place::local(t), recv_ty)
                    }
                    o => o,
                };
                ops.push(o);
                ops.extend(self.call_arg_operands(args, span));
            }
            Autoref::Ref => {
                let t = match self.slice_index_recv_ref(recv, root.is_none() && derefs == 0, false, recv_ty, span) {
                    Some(t) => t,
                    None => {
                        let pl = match &root {
                            Some(pl) => pl.clone(),
                            None => self.place(recv),
                        };
                        let pl = Self::derefs(pl, derefs);
                        let rt = self.ref_ty(false, recv_ty);
                        let t = self.temp(rt);
                        self.assign(Place::local(t), Rvalue::Ref(false, pl), span);
                        t
                    }
                };
                ops.push(Operand::Copy(Place::local(t)));
                ops.extend(self.call_arg_operands(args, span));
            }
            Autoref::SliceRef | Autoref::SliceRefMut => {
                // The array-to-slice autoderef step: `derefs` peels
                // to the array place and the receiver is its slice
                // reference. An unsize autoref is not two-phase, so
                // the slice is made before the arguments run.
                let m = autoref == Autoref::SliceRefMut;
                let pl = match &root {
                    Some(pl) => pl.clone(),
                    None if m => self.place_for_mut(recv),
                    None => self.place(recv),
                };
                let pl = Self::derefs(pl, derefs);
                let t = if recv_ty == STRING {
                    // `String` to `str` (shared only): `as_str` of the place.
                    let srt = self.ref_ty(false, STRING);
                    let sr = self.temp(srt);
                    self.assign(Place::local(sr), Rvalue::Ref(false, pl), span);
                    let t = self.temp(REF_STR);
                    self.call_into(CallTarget::Builtin(Builtin::StringAsStr), vec![Operand::Copy(Place::local(sr))], Place::local(t), span);
                    t
                } else {
                    let elem = match self.kind(recv_ty) {
                        TyKind::Array(e, _) => e,
                        _ => self.body.tys.vec_elem(recv_ty).unwrap_or(recv_ty),
                    };
                    let slice = self.body.tys.intern(TyKind::Slice(elem));
                    let rt = self.ref_ty(m, slice);
                    let t = self.temp(rt);
                    self.assign(Place::local(t), Rvalue::SliceOf(pl), span);
                    t
                };
                ops.push(if m { Operand::Move(Place::local(t)) } else { Operand::Copy(Place::local(t)) });
                for (ai, &a) in args.iter().enumerate() {
                    let o = self.ordered_operand(args, ai);
                    // As in the `RefMut` unsize path: a direct place
                    // read in an argument has no statement of its
                    // own, so read it into a temporary first when
                    // the slice borrow is mutable.
                    let o = match o {
                        Operand::Copy(pl) if m && !pl.proj.is_empty() => {
                            let aty = match self.ck.coerce(a) {
                                Coerce::Deref(n) => self.peel(self.ty(a), n),
                                Coerce::Unsize(t) => t,
                                _ => self.ty(a),
                            };
                            let tt = self.temp(aty);
                            self.assign(Place::local(tt), Rvalue::Use(Operand::Copy(pl)), span);
                            self.operand_from(Place::local(tt), aty)
                        }
                        Operand::Move(pl) if m && !pl.proj.is_empty() => {
                            let aty = self.ty(a);
                            let tt = self.temp(aty);
                            self.assign(Place::local(tt), Rvalue::Use(Operand::Move(pl)), span);
                            self.operand_from(Place::local(tt), aty)
                        }
                        o => o,
                    };
                    ops.push(o);
                }
            }
            Autoref::RefMut if let Some(t) = self.slice_index_recv_ref(recv, root.is_none() && derefs == 0, true, recv_ty, span) => {
                ops.push(Operand::Move(Place::local(t)));
                for (ai, &a) in args.iter().enumerate() {
                    let o = self.ordered_operand(args, ai);
                    ops.push(o);
                }
            }
            Autoref::RefMut => {
                let pl = match &root {
                    Some(pl) => pl.clone(),
                    None => self.place_for_mut(recv),
                };
                let pl = Self::derefs(pl, derefs);
                let mt = self.ref_ty(true, recv_ty);
                let via_deref = matches!(callee, Callee::Builtin(b) if self.slice_method_via_deref(b, recv_ty));
                // An overloaded call (`cb(..)` through `FnMut`): rustc's
                // autoref of the callee is not two-phase; its arguments'
                // reborrows are (`call_arg_operands`).
                if matches!(self.p.ast.expr(e), Expr::Call { callee, .. } if *callee == recv) {
                    let t = self.temp(mt);
                    self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
                    ops.push(Operand::Move(Place::local(t)));
                    ops.extend(self.call_arg_operands(args, span));
                } else if via_deref || pl.proj.iter().any(|x| matches!(x, Proj::Index(_))) {
                    // The receiver is reached through an `IndexMut` borrow or a slice
                    // method's `DerefMut`/unsize, which is not two-phase: take the `&mut`
                    // before the arguments run, so an argument that borrows the container
                    // again is an error, as in rustc.
                    let t = self.temp(mt);
                    self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
                    ops.push(Operand::Move(Place::local(t)));
                    for (ai, &a) in args.iter().enumerate() {
                        let o = self.ordered_operand(args, ai);
                        // A direct place read in an argument (`v[0][0]`) has no statement
                        // of its own, so the borrow checker would only see it at the call,
                        // after the `&mut` above is dead. Read it into a temporary first.
                        let o = match o {
                            Operand::Copy(pl) if !pl.proj.is_empty() => {
                                let aty = match self.ck.coerce(a) {
                                    Coerce::Deref(n) => self.peel(self.ty(a), n),
                                    Coerce::Unsize(t) => t,
                                    _ => self.ty(a),
                                };
                                let tt = self.temp(aty);
                                self.assign(Place::local(tt), Rvalue::Use(Operand::Copy(pl)), span);
                                self.operand_from(Place::local(tt), aty)
                            }
                            Operand::Move(pl) if !pl.proj.is_empty() => {
                                let aty = self.ty(a);
                                let tt = self.temp(aty);
                                self.assign(Place::local(tt), Rvalue::Use(Operand::Move(pl)), span);
                                self.operand_from(Place::local(tt), aty)
                            }
                            o => o,
                        };
                        ops.push(o);
                    }
                } else {
                    // Two-phase borrow: a shared reservation while the arguments run, then `&mut`.
                    let st = self.ref_ty(false, recv_ty);
                    let reserve = self.temp(st);
                    self.assign(Place::local(reserve), Rvalue::Ref(false, pl.clone()), span);
                    // Reborrowed `&mut` arguments are two-phase too; all
                    // activate after the arguments run, the receiver first.
                    let (mut arg_ops, pending) = self.call_arg_reserved(args, span);
                    self.push(StmtKind::FakeRead(reserve), span);
                    let t = self.temp(mt);
                    self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
                    self.activate_two_phase(&mut arg_ops, pending, span);
                    ops.push(Operand::Move(Place::local(t)));
                    ops.extend(arg_ops);
                }
            }
        }
        // A `LocalKey` method also takes its static's init fn (lower/tls.rs).
        if let Callee::Builtin(b) = callee
            && tls::is_key_method(b)
        {
            ops.extend(self.tls_operands(recv, span));
        }
        // `[S]::join`/`concat` over a written `Borrow<str>` element also
        // takes that impl's `borrow` fn (lower/iter.rs `join_borrow`);
        // `clone_from_slice` on a Copy type with a written Clone, the
        // impl's `clone_from` or `clone` fn.
        if let Callee::Builtin(Builtin::SliceJoinBorrow | Builtin::SliceConcatBorrow | Builtin::SliceCloneFromWritten) = callee
            && let Some(rec) = self.ck.index_recv(e).cloned()
        {
            let f = if rec.args.is_empty() { rec.f } else { crate::check::generics::instance_for(self.p, &self.body.tys, rec.f, &rec.args).unwrap_or(rec.f) };
            let info = self.p.fn_info(f);
            let (params, ret) = (info.params.clone(), info.ret);
            let inputs = self.body.tys.intern_tys(&params);
            let sig = self.body.tys.intern_sig(Binder::plain(FnSig::plain(inputs, ret)));
            let fp = self.body.tys.intern(TyKind::FnPtr(sig));
            let l = self.temp(fp);
            self.assign(Place::local(l), Rvalue::FnValue(f, fp), span);
            ops.push(Operand::Copy(Place::local(l)));
        }
        let target = match callee {
            Callee::Fn(f) => CallTarget::Fn(self.resolve_generic_fn(e, f)),
            Callee::Builtin(b) => CallTarget::Builtin(b),
            Callee::Dyn(owner, cand, slot) => {
                let r = ops.remove(0);
                // A `dyn Fn` value called as a function uses its own
                // principal's call entry: no upcast.
                let r = match self.p.ast.expr(e) {
                    Expr::MethodCall { name, .. } => self.dyn_receiver(r, recv_ty, autoref == Autoref::RefMut, owner, cand, *name, span),
                    _ => r,
                };
                ops.insert(0, r);
                // The call writes a temporary of the method's own return
                // type: codegen reads the vtable entry's C signature from
                // its destination, and a `!` method's destination may
                // have any type.
                let rt = self.ty(e);
                let t = self.temp(rt);
                self.call_into(CallTarget::Dyn(slot), ops, Place::local(t), span);
                if let Some(d) = dest {
                    let o = self.operand_from(Place::local(t), rt);
                    self.assign(d.clone(), Rvalue::Use(o), span);
                }
                return;
            }
        };
        let d = self.call_dest(dest, self.ty(e));
        // `by_ref()`: the `&mut Self` receiver itself, a plain reborrow (no
        // call, so its loan ends where the reference's last use is).
        if target == CallTarget::Builtin(Builtin::IterByRef) && !ops.is_empty() {
            let r = ops.swap_remove(0);
            self.assign(d, Rvalue::Use(r), span);
            return;
        }
        self.call_into(target, ops, d, span);
    }

    /// True when a `&mut self` builtin is a slice method called on a `Vec`
    /// or an array (`v.swap(..)`, `a.get_mut(..)`): rustc reaches the slice
    /// through `DerefMut` or an unsize, so its autoref is not a two-phase
    /// borrow. On a slice place (`s.swap(..)` with `s: &mut [T]`) it is.
    fn slice_method_via_deref(&self, b: Builtin, recv_ty: Ty) -> bool {
        use Builtin as B;
        matches!(
            b,
            B::VecSwap
                | B::VecReverse
                | B::VecFirstMut
                | B::VecLastMut
                | B::VecGetMut
                | B::IterIterMut
                | B::SliceFill
                | B::SliceCopyFromSlice
                | B::SliceCloneFromSlice
                | B::SliceRotateLeft
                | B::SliceRotateRight
        )
            && (self.body.tys.vec_elem(recv_ty).is_some() || matches!(self.kind(recv_ty), TyKind::Array(..)))
    }

    fn binary_into(&mut self, e: ExprId, op: BinOp, lhs: ExprId, rhs: ExprId, dest: Option<&Place>, span: Span) {
        let ty = self.ty(e);
        let out = match dest {
            Some(d) => d.clone(),
            None => Place::local(self.temp(ty)),
        };
        if let Res::TraitBin { f, ld, rd } = self.ck.res(e) {
            let f = self.resolve_generic_fn(e, f);
            let a = self.operand_derefs(lhs, ld);
            let b = self.operand_derefs(rhs, rd);
            self.call_into(CallTarget::Fn(f), vec![a, b], out, span);
            return;
        }
        if let Res::TraitCmp { f, ld, rd, via } = self.ck.res(e) {
            let f = self.resolve_generic_fn(e, f);
            let (a, _) = self.borrow_of(lhs, ld);
            let (b, _) = self.borrow_of(rhs, rd);
            self.trait_cmp_call(f, a, b, via, out, span);
            return;
        }
        if matches!(op, BinOp::And | BinOp::Or) {
            // Short circuit. Both sides write a mutable temporary, and the destination is
            // written once at the end. Writing the destination twice would make the borrow
            // checker see `let hot = a && b;` as two assignments to an immutable binding.
            // Each side is a terminating scope, as in rustc: its temporaries drop right
            // after it.
            let tmp = Place::local(self.temp(ty));
            self.scopes.push(Vec::new());
            self.expr_into(lhs, Some(&tmp));
            self.pop_scope(span);
            let (rhs_bb, end) = (self.new_block(), self.new_block());
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = if op == BinOp::And {
                Terminator::If(Operand::Copy(tmp.clone()), rhs_bb, end)
            } else {
                Terminator::If(Operand::Copy(tmp.clone()), end, rhs_bb)
            };
            b.term_span = span;
            self.cur = rhs_bb;
            self.scopes.push(Vec::new());
            self.expr_into(rhs, Some(&tmp));
            self.pop_scope(span);
            self.goto(end, span);
            self.assign(out, Rvalue::Use(Operand::Copy(tmp)), span);
            return;
        }
        let (ld, rd) = match self.ck.res(e) {
            Res::Bin { ld, rd } => (ld, rd),
            _ => (0, 0),
        };
        let lt = self.ty(lhs);
        let base = self.peel(lt, ld);
        if self.ck.is_seq_cmp(e) {
            // A comparison across sequence forms (check/slice.rs):
            // both sides as fat slices, compared as `[T]`.
            let elem = match self.kind(base) {
                TyKind::Slice(el) | TyKind::Array(el, _) => el,
                _ => self.body.tys.vec_elem(base).unwrap_or(ERROR),
            };
            let sty = self.body.tys.intern(TyKind::Slice(elem));
            let rt = self.ref_ty(false, sty);
            let fat = |this: &mut Self, side: ExprId, d: u8| -> Operand {
                let pl = Self::derefs(this.place(side), d);
                let t = this.temp(rt);
                this.assign(Place::local(t), Rvalue::SliceOf(pl), span);
                Operand::Move(Place::local(t))
            };
            let a = fat(self, lhs, ld);
            let b = fat(self, rhs, rd);
            let rv = if matches!(op, BinOp::Eq | BinOp::Ne) {
                Rvalue::Eq { a, b, ty: sty, ne: op == BinOp::Ne }
            } else {
                Rvalue::Cmp { op, a, b, ty: sty }
            };
            self.assign(out, rv, span);
            return;
        }
        if op.is_cmp() && !matches!(op, BinOp::Eq | BinOp::Ne) && matches!(self.kind(base), TyKind::Tuple(_) | TyKind::Unit) && self.expands_ord(base) {
            // Tuple ordering is lexicographic: the first unequal field
            // decides, equal tuples order by the operator's reflexivity.
            let ao = self.operand_derefs(lhs, ld);
            let ap = self.op_place(ao, base, span);
            let bo = self.operand_derefs(rhs, rd);
            let bp = self.op_place(bo, base, span);
            self.ord_into(op, ap, bp, base, out, span);
            return;
        }
        let rv = if op.is_cmp() {
            match self.kind(base) {
                TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char => {
                    let a = self.operand_derefs(lhs, ld);
                    let b = self.operand_derefs(rhs, rd);
                    Rvalue::Bin(op, a, b)
                }
                TyKind::Str => {
                    let a = self.str_view(lhs, ld);
                    let b = self.str_view(rhs, rd);
                    Rvalue::StrCmp(op, a, b)
                }
                _ if self.body.tys.is_string_ty(base) => {
                    let a = self.str_view(lhs, ld);
                    let b = self.str_view(rhs, rd);
                    Rvalue::StrCmp(op, a, b)
                }
                // `Cow<str>` (W-STD-B) compares as its `str` view, also
                // against the other string types.
                _ if crate::check::collect::cow_arg(&self.body.tys, base).is_some_and(|b| self.kind(b) == TyKind::Str) => {
                    let a = self.str_view(lhs, ld);
                    let b = self.str_view(rhs, rd);
                    Rvalue::StrCmp(op, a, b)
                }
                _ if matches!(op, BinOp::Eq | BinOp::Ne) => {
                    let (a, t) = self.borrow_of(lhs, ld);
                    let (b, _) = self.borrow_of(rhs, rd);
                    Rvalue::Eq { a, b, ty: t, ne: op == BinOp::Ne }
                }
                // Ordering by structure (`has_ord`): the `cmp` glue.
                _ => {
                    let (a, t) = self.borrow_of(lhs, ld);
                    let (b, _) = self.borrow_of(rhs, rd);
                    Rvalue::Cmp { op, a, b, ty: t }
                }
            }
        } else if self.body.tys.is_string_ty(lt) {
            let a = self.operand(lhs);
            let b = self.operand(rhs);
            Rvalue::StringAdd(a, b)
        } else if crate::check::collect::cow_arg(&self.body.tys, lt).is_some() {
            // `Cow<str> + &str`: move the Cow into a temp, then the
            // add-assign builtin makes it owned and pushes.
            let a = self.operand(lhs);
            let b = self.cow_add_rhs(rhs, span);
            let t = self.temp(lt);
            self.assign(Place::local(t), Rvalue::Use(a), span);
            let mt = self.ref_ty(true, lt);
            let r = self.temp(mt);
            self.assign(Place::local(r), Rvalue::Ref(true, Place::local(t)), span);
            let u = self.temp(UNIT);
            self.call_into(
                CallTarget::Builtin(Builtin::CowAddAssignStr),
                vec![Operand::Move(Place::local(r)), b],
                Place::local(u),
                span,
            );
            self.assign(out, Rvalue::Use(Operand::Move(Place::local(t))), span);
            return;
        } else {
            let a = self.operand_derefs(lhs, ld);
            let b = self.operand_derefs(rhs, rd);
            Rvalue::Bin(op, a, b)
        };
        self.assign(out, rv, span);
    }

    /// True when a destructuring assignment target moves a non-Copy
    /// element out of its source. Leaf targets carry their element
    /// type from the checker, in both checking directions.
    fn assign_moves_noncopy(&self, e: ExprId) -> bool {
        match self.p.ast.expr(e) {
            Expr::Underscore | Expr::Unit => false,
            Expr::Path(_) if matches!(self.ck.res(e), Res::Variant(..)) => false,
            Expr::Tuple(elems) | Expr::Array(elems) => elems.iter().any(|&el| !self.is_rest_elem(el) && self.assign_moves_noncopy(el)),
            Expr::StructLit { fields, .. } => fields.iter().any(|&(_, _, fe)| self.assign_moves_noncopy(fe)),
            Expr::Call { args, .. } if matches!(self.ck.res(e), Res::Variant(..)) => {
                args.iter().any(|&arg| !self.is_rest_elem(arg) && self.assign_moves_noncopy(arg))
            }
            _ => !is_copy(self.p, &self.body.tys, self.ty(e)),
        }
    }

    /// The source place of a destructuring assignment, with the
    /// guard `pattern_place` puts on a pattern scrutinee: a move
    /// out of a place that goes through a written index expression
    /// is a move out of the reference the `Index` trait returns
    /// (rustc E0507/E0508), not the partial move the same
    /// projections mean when the target itself projects them.
    fn assign_pattern_place(&mut self, place: Place, ty: Ty, lhs: ExprId, span: Span) -> Place {
        if !place.proj.iter().any(|x| matches!(x, Proj::Index(_))) || !self.assign_moves_noncopy(lhs) {
            return place;
        }
        let rt = self.ref_ty(false, ty);
        let tmp = self.temp(rt);
        self.assign(Place::local(tmp), Rvalue::Ref(false, place), span);
        Place::local(tmp).deref()
    }

    /// Phase one of a destructuring assignment: move each written
    /// element of the source place into its own temporary, in target
    /// order, and collect the writes. `_`, `()`, a unit variant, and
    /// the elements a `..` rest covers write nothing and stay in the
    /// source place: the caller drops a temporary source next, so a
    /// discarded element of a value drops before the overwritten old
    /// values do, and a discarded element of an owned place stays
    /// in that place.
    fn collect_assign_pattern(&mut self, e: ExprId, src: Place, ty: Ty, span: Span, out: &mut Vec<(ExprId, Place, Ty)>) {
        let p = self.p;
        match p.ast.expr(e) {
            Expr::Underscore | Expr::Unit => {}
            Expr::Path(_) if matches!(self.ck.res(e), Res::Variant(..)) => {}
            Expr::Tuple(elems) => {
                let elem_tys: Vec<Ty> = match self.kind(ty) {
                    TyKind::Tuple(ts) => self.body.tys.tys_of(ts).to_vec(),
                    _ => Vec::new(),
                };
                for (i, el) in self.map_assign_elems(elems, elem_tys.len()) {
                    self.collect_assign_pattern(el, src.project(Proj::Field(i as u32)), elem_tys[i], span, out);
                }
            }
            Expr::Array(elems) => {
                let (elem_ty, arr_len) = match self.kind(ty) {
                    TyKind::Array(el, c) => {
                        let n = match self.body.tys.const_kind(c) {
                            ConstKind::Int(n) => Some(n as u64),
                            _ => None,
                        };
                        (el, n)
                    }
                    TyKind::Slice(el) => (el, None),
                    _ => (ERROR, None),
                };
                let (prefix, suffix): (&[ExprId], &[ExprId]) = match elems.iter().position(|&e| self.is_rest_elem(e)) {
                    Some(r) => (&elems[..r], &elems[r + 1..]),
                    None => (elems, &[]),
                };
                for (i, &el) in prefix.iter().enumerate() {
                    let idx = self.pat_front_index(i as u64, (prefix.len() + suffix.len()) as u64, span);
                    self.collect_assign_pattern(el, src.project(Proj::Index(idx)), elem_ty, span, out);
                }
                for (j, &el) in suffix.iter().enumerate() {
                    if self.is_rest_elem(el) {
                        continue;
                    }
                    let back = (suffix.len() - j) as u64;
                    let idx = self.slice_back_index(&src, back, arr_len, (prefix.len() + suffix.len()) as u64, span);
                    self.collect_assign_pattern(el, src.project(Proj::Index(idx)), elem_ty, span, out);
                }
            }
            Expr::StructLit { fields, .. } => {
                let Res::Variant(a, v) = self.ck.res(e) else { return };
                let base = if p.adt(a).is_enum { src.project(Proj::Downcast(v)) } else { src };
                let vfields = &p.adt(a).variants[v as usize].fields;
                for &(fname, _, fe) in fields {
                    if let Some(i) = vfields.iter().position(|f| f.name == fname) {
                        let fty = self.ty(fe);
                        self.collect_assign_pattern(fe, base.project(Proj::Field(i as u32)), fty, span, out);
                    }
                }
            }
            Expr::Call { args, .. } => {
                let Res::Variant(a, v) = self.ck.res(e) else { return };
                let base = if p.adt(a).is_enum { src.project(Proj::Downcast(v)) } else { src };
                let n = p.adt(a).variants[v as usize].fields.len();
                for (i, arg) in self.map_assign_elems(args, n) {
                    let fty = self.ty(arg);
                    self.collect_assign_pattern(arg, base.project(Proj::Field(i as u32)), fty, span, out);
                }
            }
            _ => {
                let t = Place::local(self.temp(ty));
                let op = self.operand_from(src, ty);
                self.assign(t.clone(), Rvalue::Use(op), span);
                out.push((e, t, ty));
            }
        }
    }

    /// A `&str` operand for a String or str place (a tuple field in an
    /// ordering expansion).
    fn str_place_view(&mut self, place: Place, ty: Ty, span: Span) -> Operand {
        let rt = self.ref_ty(false, ty);
        let r = self.temp(rt);
        self.assign(Place::local(r), Rvalue::Ref(false, place), span);
        if self.body.tys.is_string_ty(ty) {
            let t = self.temp(REF_STR);
            self.call_into(CallTarget::Builtin(Builtin::StringAsStr), vec![Operand::Copy(Place::local(r))], Place::local(t), span);
            Operand::Copy(Place::local(t))
        } else {
            Operand::Copy(Place::local(r))
        }
    }

    /// True when an ordering of `ty` expands in lowering (`ord_into`):
    /// tuples whose elements are scalars, strings, references to
    /// such, or tuples of such. Other orderable types compare
    /// through the `cmp` glue (`Rvalue::Cmp`).
    fn expands_ord(&self, ty: Ty) -> bool {
        match self.kind(ty) {
            TyKind::Unit | TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Str => true,
            TyKind::Ref(_, _, e) => self.expands_ord(e),
            TyKind::Tuple(ts) => self.body.tys.tys_of(ts).to_vec().into_iter().all(|e| self.expands_ord(e)),
            _ => self.body.tys.is_string_ty(ty),
        }
    }

    /// Writes the comparison `a <op> b` for orderable places into
    /// `out`. Tuples expand lexicographically, field by field, with a
    /// short circuit on the first unequal field; equality of nested
    /// tuples expands the same way. The checker gates the shapes this
    /// can see through `has_ord`; the caller sends only the shapes
    /// `expands_ord` accepts.
    fn ord_into(&mut self, op: BinOp, a: Place, b: Place, ty: Ty, out: Place, span: Span) {
        match self.kind(ty) {
            TyKind::Unit => {
                self.assign(out, Rvalue::Use(Operand::Const(Const::Bool(matches!(op, BinOp::Eq | BinOp::Le | BinOp::Ge)))), span)
            }
            TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char => {
                let (x, y) = (self.operand_from(a, ty), self.operand_from(b, ty));
                self.assign(out, Rvalue::Bin(op, x, y), span);
            }
            TyKind::Ref(_, _, inner) => self.ord_into(op, a.deref(), b.deref(), inner, out, span),
            TyKind::Str => {
                let (x, y) = (self.str_place_view(a, ty, span), self.str_place_view(b, ty, span));
                self.assign(out, Rvalue::StrCmp(op, x, y), span);
            }
            _ if self.body.tys.is_string_ty(ty) => {
                let (x, y) = (self.str_place_view(a, ty, span), self.str_place_view(b, ty, span));
                self.assign(out, Rvalue::StrCmp(op, x, y), span);
            }
            TyKind::Tuple(ts) => {
                let elems: Vec<Ty> = self.body.tys.tys_of(ts).to_vec();
                let res = Place::local(self.temp(BOOL));
                let end = self.new_block();
                if matches!(op, BinOp::Eq | BinOp::Ne) {
                    self.assign(res.clone(), Rvalue::Use(Operand::Const(Const::Bool(true))), span);
                    for (i, &ety) in elems.iter().enumerate() {
                        if self.kind(ety) == TyKind::Unit {
                            continue;
                        }
                        let eq = Place::local(self.temp(BOOL));
                        self.ord_into(BinOp::Eq, a.project(Proj::Field(i as u32)), b.project(Proj::Field(i as u32)), ety, eq.clone(), span);
                        let (next, fail) = (self.new_block(), self.new_block());
                        let blk = &mut self.body.blocks[self.cur.0 as usize];
                        blk.term = Terminator::If(Operand::Copy(eq), next, fail);
                        blk.term_span = span;
                        self.cur = fail;
                        self.assign(res.clone(), Rvalue::Use(Operand::Const(Const::Bool(false))), span);
                        self.goto(end, span);
                        self.cur = next;
                    }
                    self.goto(end, span);
                    self.cur = end;
                    if op == BinOp::Ne {
                        self.assign(out, Rvalue::Un(crate::ast::UnOp::Not, Operand::Copy(res)), span);
                    } else {
                        self.assign(out, Rvalue::Use(Operand::Copy(res)), span);
                    }
                } else {
                    self.assign(res.clone(), Rvalue::Use(Operand::Const(Const::Bool(matches!(op, BinOp::Le | BinOp::Ge)))), span);
                    for (i, &ety) in elems.iter().enumerate() {
                        if self.kind(ety) == TyKind::Unit {
                            continue;
                        }
                        let (af, bf) = (a.project(Proj::Field(i as u32)), b.project(Proj::Field(i as u32)));
                        let eq = Place::local(self.temp(BOOL));
                        self.ord_into(BinOp::Eq, af.clone(), bf.clone(), ety, eq.clone(), span);
                        let (next, decide) = (self.new_block(), self.new_block());
                        let blk = &mut self.body.blocks[self.cur.0 as usize];
                        blk.term = Terminator::If(Operand::Copy(eq), next, decide);
                        blk.term_span = span;
                        self.cur = decide;
                        self.ord_into(op, af, bf, ety, res.clone(), span);
                        self.goto(end, span);
                        self.cur = next;
                    }
                    self.goto(end, span);
                    self.cur = end;
                    self.assign(out, Rvalue::Use(Operand::Copy(res)), span);
                }
            }
            _ => self.assign(out, Rvalue::Use(Operand::Const(Const::Bool(false))), span),
        }
    }

    /// A `&str` view of a String or str value reached through `n` references.
    fn str_view(&mut self, e: ExprId, n: u8) -> Operand {
        let (span, t) = (self.span(e), self.ty(e));
        let p = self.place(e);
        self.str_view_at(p, t, n, span)
    }

    /// `str_view` of a value already evaluated into place `p` (of type
    /// `t`): `assert_eq!` borrows its operands first and must not
    /// evaluate them again.
    fn str_view_at(&mut self, p: Place, t: Ty, n: u8, span: Span) -> Operand {
        let base = self.peel(t, n);
        let borrow = |this: &mut Self, p: Place, t: Ty| {
            let rt = this.ref_ty(false, t);
            let tmp = this.temp(rt);
            this.assign(Place::local(tmp), Rvalue::Ref(false, p), span);
            Operand::Copy(Place::local(tmp))
        };
        if self.kind(base) == TyKind::Str {
            if n == 0 {
                // The place itself is a `str` place (`*t` for `t: &str`): borrow it back.
                return borrow(self, p, base);
            }
            return Operand::Copy(Self::derefs(p, n - 1));
        }
        // A String's `as_str`, or a `Cow<str>`'s view (W-STD-B).
        let b = if crate::check::collect::cow_arg(&self.body.tys, base).is_some() { Builtin::CowDeref } else { Builtin::StringAsStr };
        let r = borrow(self, Self::derefs(p, n), base);
        let t = self.temp(REF_STR);
        self.call_into(CallTarget::Builtin(b), vec![r], Place::local(t), span);
        Operand::Copy(Place::local(t))
    }

    // ---------- Loops ----------

    /// For an mpsc `Receiver<T>` (true) or `&Receiver<T>` (false): the
    /// element type `T`.
    fn recv_iterable(&self, t: Ty) -> Option<(bool, Ty)> {
        let (owned, r) = match self.kind(t) {
            TyKind::Ref(_, m, inner) if !m.is_mut() => (false, inner),
            _ => (true, t),
        };
        (crate::ty::sync::sync_kind(&self.body.tys, r) == Some(crate::ty::sync::SyncTy::Receiver)).then(|| self.body.tys.adt_first_ty_arg(r)).flatten().map(|e| (owned, e))
    }

    fn for_loop(
        &mut self,
        for_e: ExprId,
        label: Option<ast::Label>,
        pat: PatId,
        iter: ExprId,
        body: ast::BlockId,
        span: Span,
        dest: Option<&Place>,
    ) {
        let p = self.p;
        self.scopes.push(Vec::new());
        let item_ty = self.for_item_ty(for_e, pat, iter);
        let (head, bodyb, exit) = (self.new_block(), self.new_block(), self.new_block());
        // `next` computes the loop variable into this local at the top of
        // each iteration. It joins the iteration's scope (below), so what
        // the pattern leaves in it (all of it for `_`) drops at the end of
        // each iteration, after the pattern's bindings, as rustc's
        // `match next(&mut it) { Some(pat) => body }` drops its scrutinee:
        // before the next `next` call, never after it.
        let item = self.new_local(item_ty, true, None);
        if let Res::ForTrait { into_iter, next } = self.ck.res(for_e) {
            // `for x in it`: into_iter() then next() until None,
            // the Chars arm's shape with user methods. A builtin
            // iterator's `next` (sentinel id) is the builtin call.
            let next_f = (next.0 != u32::MAX).then(|| self.resolve_generic_fn(for_e, next));
            // The std blanket IntoIterator is synthetic with the
            // sentinel id: the receiver is already the iterator.
            // rustc's `match into_iter(head) { mut iter => loop {..} }`
            // drops the iterator before the head's temporaries (`files().
            // zip(order().iter())` borrows a temporary until it drops), and
            // not on an unwind from the head: it joins the scope after it.
            let (iter_ty, it) = if into_iter.0 == u32::MAX {
                let it = self.new_local(self.ty(iter), true, None);
                self.expr_into(iter, Some(&Place::local(it)));
                (self.ty(iter), it)
            } else {
                let into_f = self.resolve_generic_fn(for_e, into_iter);
                let iter_ty = self.site_ret_ty(for_e, into_iter, into_f);
                let src = self.temp(self.ty(iter));
                self.expr_into(iter, Some(&Place::local(src)));
                let it = self.new_local(iter_ty, true, None);
                let src_op = self.operand_from(Place::local(src), self.ty(iter));
                self.call_into(CallTarget::Fn(into_f), vec![src_op], Place::local(it), span);
                (iter_ty, it)
            };
            self.scopes.last_mut().unwrap().push(it);
            self.goto(head, span);
            // `it: &mut I` stepped by `I`'s own `next` (core's `impl
            // Iterator for &mut I`, check `for_trait_iter`): the reference
            // itself, reborrowed, is the receiver.
            let next_recv = next_f.and_then(|f| p.fn_info(f).params.first().map(|&t| (f, t))).map(|(f, t)| {
                let t = match self.site_args(for_e, next) {
                    Some(args) if f == next && !args.is_empty() => {
                        let args = args.to_vec();
                        subst(&mut self.body.tys, t, &args)
                    }
                    _ => t,
                };
                crate::borrowck::erase(&mut self.body.tys, t)
            });
            let by_mut = matches!(self.kind(iter_ty), TyKind::Ref(_, Mut::Mut, _))
                && next_recv.is_none_or(|t| !matches!(self.kind(t), TyKind::Ref(_, Mut::Mut, x) if x == iter_ty));
            let (mt, recv) = if by_mut { (iter_ty, Place::local(it).deref()) } else { (self.ref_ty(true, iter_ty), Place::local(it)) };
            let r = self.temp(mt);
            self.assign(Place::local(r), Rvalue::Ref(true, recv), span);
            let (ot, target) = match next_f {
                Some(f) => (self.site_ret_ty(for_e, next, f), CallTarget::Fn(f)),
                None => (self.body.tys.mk_option(item_ty), CallTarget::Builtin(Builtin::IterNext)),
            };
            let nx = self.temp(ot);
            self.call_into(target, vec![Operand::Move(Place::local(r))], Place::local(nx), span);
            let d = self.temp(int(IntTy::U32));
            self.assign(Place::local(d), Rvalue::Discriminant(Place::local(nx)), span);
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(1, bodyb)], exit);
            self.cur = bodyb;
            let c = Place::local(nx).project(Proj::Downcast(1)).project(Proj::Field(0));
            let op = self.operand_from(c, item_ty);
            self.assign(Place::local(item), Rvalue::Use(op), span);
        } else if let Expr::Range { lo, hi, inclusive } = p.ast.expr(iter)
            // A `char` range (typed by check) takes the iterator arm.
            && !crate::ty::iter::is_iter(&self.body.tys, self.ty(iter))
        {
            let (lo, hi) = (lo.unwrap(), hi.unwrap());
            let cur = self.temp(item_ty);
            self.expr_into(lo, Some(&Place::local(cur)));
            let end = self.temp(item_ty);
            self.expr_into(hi, Some(&Place::local(end)));
            let done = self.temp(BOOL);
            self.assign(Place::local(done), Rvalue::Use(Operand::Const(Const::Bool(false))), span);
            self.goto(head, span);
            // head: if !done && cur < end (or <=)
            let c = self.temp(BOOL);
            let cmp = if *inclusive { BinOp::Le } else { BinOp::Lt };
            self.assign(Place::local(c), Rvalue::Bin(cmp, Operand::Copy(Place::local(cur)), Operand::Copy(Place::local(end))), span);
            let check_done = self.new_block();
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), check_done, exit);
            self.cur = check_done;
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(done)), exit, bodyb);
            self.cur = bodyb;
            self.assign(Place::local(item), Rvalue::Use(Operand::Copy(Place::local(cur))), span);
            // Advance before the body, so `continue` can jump straight to `head`.
            let (inc, stop, after) = (self.new_block(), self.new_block(), self.new_block());
            let eq = self.temp(BOOL);
            self.assign(Place::local(eq), Rvalue::Bin(BinOp::Eq, Operand::Copy(Place::local(cur)), Operand::Copy(Place::local(end))), span);
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(eq)), stop, inc);
            self.cur = stop;
            self.assign(Place::local(done), Rvalue::Use(Operand::Const(Const::Bool(true))), span);
            self.goto(after, span);
            self.cur = inc;
            let one = match self.kind(item_ty) {
                TyKind::Int(it) => Const::Int(1, it),
                _ => Const::Int(1, IntTy::I32),
            };
            self.assign(Place::local(cur), Rvalue::Bin(BinOp::Add, Operand::Copy(Place::local(cur)), Operand::Const(one)), span);
            self.goto(after, span);
        } else if self.body.tys.is_chars_ty(self.ty(iter)) {
            // `for c in s.chars()`: call `next` until it returns None.
            let it = self.temp(self.ty(iter));
            self.expr_into(iter, Some(&Place::local(it)));
            self.goto(head, span);
            let mt = self.ref_ty(true, self.ty(iter));
            let r = self.temp(mt);
            self.assign(Place::local(r), Rvalue::Ref(true, Place::local(it)), span);
            let ot = self.body.tys.mk_option(CHAR);
            let nx = self.temp(ot);
            self.call_into(CallTarget::Builtin(Builtin::CharsNext), vec![Operand::Move(Place::local(r))], Place::local(nx), span);
            let d = self.temp(int(IntTy::U32));
            self.assign(Place::local(d), Rvalue::Discriminant(Place::local(nx)), span);
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(1, bodyb)], exit);
            self.cur = bodyb;
            let c = Place::local(nx).project(Proj::Downcast(1)).project(Proj::Field(0));
            self.assign(Place::local(item), Rvalue::Use(Operand::Copy(c)), span);
        } else if let Some(hash_it) = {
            let ity = self.ty(iter);
            let h = crate::ty::iter::hash_for_iter(&mut self.body.tys, ity).flatten();
            let o = crate::ty::iter::opt_res_iter(&mut self.body.tys, ity);
            // An array by value (fx-array-iter): its `array::IntoIter`,
            // for every element type and length. Its drop gives the
            // remaining elements front to back on `break`, `return`,
            // and panic exits, as rustc's desugaring does.
            let a = match self.kind(ity) {
                TyKind::Array(el, _) => Some(crate::ty::iter::mk_iter(&mut self.body.tys, crate::ty::iter::IterKind::ArrayIntoIter, &[el, ity])),
                _ => None,
            };
            // `for x in &mut it` over a builtin iterator: core's `impl
            // Iterator for &mut I`, a `ByNext` wrapper that steps `it` in
            // place (lower/iter.rs `by_mut_builtin`).
            let bm = match self.kind(ity) {
                TyKind::Ref(_, Mut::Mut, inner) if crate::ty::iter::is_iter(&self.body.tys, inner) || self.body.tys.is_chars_ty(inner) => {
                    let item = if self.body.tys.is_chars_ty(inner) { CHAR } else { crate::ty::iter::item_ty(&mut self.body.tys, inner).unwrap_or(ERROR) };
                    Some(crate::ty::iter::mk_iter(&mut self.body.tys, crate::ty::iter::IterKind::ByNext, &[ity, item]))
                }
                _ => None,
            };
            h.or(o).or(a).or(bm).or_else(|| {
                (crate::ty::iter::is_iter(&self.body.tys, ity) || self.body.tys.boxed_slice_elem(ity).is_some() || self.body.tys.vec_elem(ity).is_some() || self.recv_iterable(ity).is_some())
                    .then_some(ERROR)
            })
        } {
            // `for x in it` over a builtin iterator (ty/iter.rs): call
            // `next` until it returns None, like the Chars arm. A map or
            // set (or a reference to one) first makes its hash iterator. A
            // Vec by value, and a boxed slice by value (Rust 2024), iterate
            // their `vec::IntoIter`.
            let recv = self.recv_iterable(self.ty(iter));
            let (it_ty, it) = match self.body.tys.boxed_slice_elem(self.ty(iter)) {
                // An array by value (fx-array-iter): first make its
                // `array::IntoIter`.
                _ if crate::ty::iter::iter_parts(&self.body.tys, hash_it).is_some_and(|(k, _)| k == crate::ty::iter::IterKind::ArrayIntoIter) => {
                    let it = self.new_local(hash_it, true, None);
                    let src = self.temp(self.ty(iter));
                    self.expr_into(iter, Some(&Place::local(src)));
                    self.call_into(CallTarget::Builtin(Builtin::IterArrayIntoIter), vec![Operand::Move(Place::local(src))], Place::local(it), span);
                    (hash_it, it)
                }
                // An `Option` or `Result` (fx-option-rest): first
                // make its one-item iterator.
                _ if crate::ty::iter::iter_parts(&self.body.tys, hash_it).is_some_and(|(k, _)| crate::ty::iter::is_opt_res(k)) => {
                    let it = self.new_local(hash_it, true, None);
                    let src = self.temp(self.ty(iter));
                    self.expr_into(iter, Some(&Place::local(src)));
                    self.call_into(CallTarget::Builtin(Builtin::IterOptRes), vec![Operand::Move(Place::local(src))], Place::local(it), span);
                    (hash_it, it)
                }
                _ if crate::ty::iter::iter_parts(&self.body.tys, hash_it).is_some_and(|(k, _)| k == crate::ty::iter::IterKind::ByNext) => {
                    let src = self.temp(self.ty(iter));
                    self.expr_into(iter, Some(&Place::local(src)));
                    let it = self.new_local(hash_it, true, None);
                    self.assign(Place::local(it), Rvalue::TupleAgg(hash_it, vec![Operand::Move(Place::local(src))]), span);
                    (hash_it, it)
                }
                _ if hash_it != ERROR => {
                    let it = self.new_local(hash_it, true, None);
                    let src = self.temp(self.ty(iter));
                    self.expr_into(iter, Some(&Place::local(src)));
                    self.call_into(CallTarget::Builtin(Builtin::HashIterNew), vec![Operand::Move(Place::local(src))], Place::local(it), span);
                    (hash_it, it)
                }
                // An mpsc receiver (W-THREADS): `for x in rx` iterates
                // its `IntoIter`, `for x in &rx` its `Iter`.
                _ if let Some((owned, el)) = recv => {
                    let src = self.temp(self.ty(iter));
                    self.expr_into(iter, Some(&Place::local(src)));
                    let k = if owned { crate::ty::iter::IterKind::RecvIntoIter } else { crate::ty::iter::IterKind::RecvIter };
                    let it_ty = crate::ty::iter::mk_iter(&mut self.body.tys, k, &[el]);
                    let it = self.new_local(it_ty, true, None);
                    let op = crate::check::sync::SyncOp::RecvMakeIter(if owned { 2 } else { 0 });
                    self.call_into(CallTarget::Builtin(Builtin::Sync(op)), vec![Operand::Move(Place::local(src))], Place::local(it), span);
                    (it_ty, it)
                }
                // A Vec by value: its `vec::IntoIter`, a cursor (not `remove(0)` per item). Its
                // drop gives the remaining items front to back on `break`, `return` and panic
                // exits, as rustc's desugaring does.
                None if let Some(el) = self.body.tys.vec_elem(self.ty(iter)) => {
                    let v = self.temp(self.ty(iter));
                    self.expr_into(iter, Some(&Place::local(v)));
                    let it_ty = crate::ty::iter::mk_iter(&mut self.body.tys, crate::ty::iter::IterKind::VecIntoIter, &[el]);
                    let it = self.new_local(it_ty, true, None);
                    self.call_into(CallTarget::Builtin(Builtin::IterVecIntoIter), vec![Operand::Move(Place::local(v))], Place::local(it), span);
                    (it_ty, it)
                }
                Some(el) => {
                    let bx = self.temp(self.ty(iter));
                    self.expr_into(iter, Some(&Place::local(bx)));
                    let it_ty = crate::ty::iter::mk_iter(&mut self.body.tys, crate::ty::iter::IterKind::VecIntoIter, &[el]);
                    let it = self.new_local(it_ty, true, None);
                    self.call_into(CallTarget::Builtin(Builtin::BoxSliceIntoIter), vec![Operand::Move(Place::local(bx))], Place::local(it), span);
                    (it_ty, it)
                }
                None => {
                    let it_ty = self.ty(iter);
                    let it = self.new_local(it_ty, true, None);
                    self.expr_into(iter, Some(&Place::local(it)));
                    (it_ty, it)
                }
            };
            // The iterator joins the scope after the head (as above).
            self.scopes.last_mut().unwrap().push(it);
            self.goto(head, span);
            let mt = self.ref_ty(true, it_ty);
            let r = self.temp(mt);
            self.assign(Place::local(r), Rvalue::Ref(true, Place::local(it)), span);
            let ot = self.body.tys.mk_option(item_ty);
            let nx = self.temp(ot);
            self.call_into(CallTarget::Builtin(Builtin::IterNext), vec![Operand::Move(Place::local(r))], Place::local(nx), span);
            let d = self.temp(int(IntTy::U32));
            self.assign(Place::local(d), Rvalue::Discriminant(Place::local(nx)), span);
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(1, bodyb)], exit);
            self.cur = bodyb;
            let c = Place::local(nx).project(Proj::Downcast(1)).project(Proj::Field(0));
            let op = self.operand_from(c, item_ty);
            self.assign(Place::local(item), Rvalue::Use(op), span);
        } else {
            // `for x in &v` / `&mut v`: index loop over a reference held for the whole loop.
            // An array by value takes the `array::IntoIter` arm above.
            let it_ty = self.ty(iter);
            let m = matches!(self.kind(it_ty), TyKind::Ref(_, Mut::Mut, _));
            let vref = self.temp(it_ty);
            self.expr_into(iter, Some(&Place::local(vref)));
            let len = self.temp(USIZE);
            let shared = self.ref_ty(false, self.peel(it_ty, 1));
            let sref = self.temp(shared);
            self.assign(Place::local(sref), Rvalue::Ref(false, Place::local(vref).deref()), span);
            let len_builtin = if self.body.tys.vec_elem(self.peel(it_ty, 1)).is_some() { Builtin::VecLen } else { Builtin::SliceLen };
            self.call_into(CallTarget::Builtin(len_builtin), vec![Operand::Copy(Place::local(sref))], Place::local(len), span);
            let idx = self.temp(USIZE);
            self.assign(Place::local(idx), Rvalue::Use(Operand::Const(Const::Int(0, IntTy::Usize))), span);
            self.goto(head, span);
            let c = self.temp(BOOL);
            self.assign(Place::local(c), Rvalue::Bin(BinOp::Lt, Operand::Copy(Place::local(idx)), Operand::Copy(Place::local(len))), span);
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), bodyb, exit);
            self.cur = bodyb;
            let elem = Place::local(vref).deref().project(Proj::Index(idx));
            self.assign(Place::local(item), Rvalue::Ref(m, elem), span);
            self.assign(
                Place::local(idx),
                Rvalue::Bin(BinOp::Add, Operand::Copy(Place::local(idx)), Operand::Const(Const::Int(1, IntTy::Usize))),
                span,
            );
        }
        self.scopes.push(vec![item]);
        self.bind_pat(pat, Place::local(item));
        self.loops.push(LoopInfo {
            break_bb: exit,
            continue_bb: head,
            dest: None,
            depth: self.scopes.len() - 1,
            label: label.map(|l| (l.name, l.span)),
            is_block: false,
        });
        self.block_into(body, None);
        self.loops.pop();
        self.pop_scope(span);
        self.goto(head, span);
        self.cur = exit;
        self.pop_scope(span);
        self.unit(dest, span);
    }

    /// The type of a `for` loop's item: the pattern's type, or, when the
    /// pattern matches through references (default binding modes:
    /// `for (k, v) in &map_vec`, `pat_derefs`), the iterator's item those
    /// references wrap, which `bind_pat` derefs.
    fn for_item_ty(&mut self, for_e: ExprId, pat: PatId, iter: ExprId) -> Ty {
        let pt = self.ck.pat_ty(pat);
        if self.ck.pat_derefs(pat) == 0 {
            return pt;
        }
        let it = self.ty(iter);
        let elem = |this: &Self, t: Ty| match this.kind(t) {
            TyKind::Array(e, _) | TyKind::Slice(e) => Some(e),
            _ => this.body.tys.vec_elem(t),
        };
        let item = if let Res::ForTrait { next, .. } = self.ck.res(for_e) {
            let ret = self.p.fn_info(self.resolve_generic_fn(for_e, next)).ret;
            self.body.tys.option_elem(ret)
        } else if crate::ty::iter::is_iter(&self.body.tys, it) {
            crate::ty::iter::item_ty(&mut self.body.tys, it)
        } else if let TyKind::Ref(_, m, inner) = self.kind(it) {
            elem(self, inner).map(|e| self.ref_ty(m == Mut::Mut, e))
        } else {
            elem(self, it)
        };
        item.unwrap_or(pt)
    }

    /// True when `pat` has a binding that moves a non-Copy part
    /// out of the value it matches.
    fn pat_moves_noncopy(&self, pat: PatId) -> bool {
        let binding_moves = |this: &Self, pat: PatId| {
            matches!(this.ck.pat_res(pat), PatRes::Binding { mode: BindMode::Move, .. })
                && !is_copy(this.p, &this.body.tys, this.ck.pat_ty(pat))
        };
        match self.p.ast.pat(pat) {
            Pat::Binding { .. } => binding_moves(self, pat),
            Pat::At { inner, .. } => binding_moves(self, pat) || self.pat_moves_noncopy(*inner),
            Pat::TupleStruct { elems, .. } | Pat::Tuple(elems) | Pat::Or(elems) => elems.iter().any(|&s| self.pat_moves_noncopy(s)),
            Pat::Struct { fields, .. } => fields.iter().any(|&(_, s)| self.pat_moves_noncopy(s)),
            Pat::Slice { prefix, middle, suffix } => {
                middle.is_some_and(|m| self.pat_moves_noncopy(m)) || prefix.iter().chain(suffix.iter()).any(|&s| self.pat_moves_noncopy(s))
            }
            Pat::Paren(i) | Pat::Ref { inner: i, .. } => self.pat_moves_noncopy(*i),
            _ => false,
        }
    }

    /// The place a pattern binds out of, when `place` came from a
    /// place expression. A move out of a place that goes through
    /// an index expression is a move out of the reference the
    /// `Index` trait returns (rustc E0507/E0508), not the partial
    /// move the same projections mean when a pattern projects
    /// them: route such a place through a shared borrow temporary
    /// so the borrow checker reports the move, as `operand_raw`
    /// does for operand reads. When no pattern in `pats` moves a
    /// non-Copy part (tests only, `ref` bindings, Copy bindings),
    /// the direct place stays, so those matches work as before.
    fn pattern_place(&mut self, place: Place, ty: Ty, pats: &[PatId], span: Span) -> Place {
        if !place.proj.iter().any(|x| matches!(x, Proj::Index(_))) || !pats.iter().any(|&pat| self.pat_moves_noncopy(pat)) {
            return place;
        }
        let rt = self.ref_ty(false, ty);
        let tmp = self.temp(rt);
        self.assign(Place::local(tmp), Rvalue::Ref(false, place), span);
        Place::local(tmp).deref()
    }

    // ---------- Match ----------

    fn match_into(&mut self, scrut: ExprId, arms: &[ast::Arm], dest: Option<&Place>, span: Span) {
        // Temporaries in the scrutinee belong to the enclosing scope, as
        // in rustc (the scrutinee is not a terminating scope): in a `let`
        // or a call argument they live to the end of the statement.
        // Arms bind out of the scrutinee place itself, as in rustc: an
        // arm that moves a part is a partial move of that place, and
        // the rest drops with it (codegen elaborates the drop).
        let sp = self.place(scrut);
        let arm_pats: Vec<PatId> = arms.iter().map(|a| a.pat).collect();
        let scrut_ty = self.ty(scrut);
        let sp = self.pattern_place(sp, scrut_ty, &arm_pats, span);
        let end = self.new_block();
        // Reference-typed arms after the first that does not diverge are
        // reborrowed (`arm_into`).
        let first = arms.iter().position(|a| !self.diverges(a.body));
        let reborrow = first.is_some_and(|i| self.reborrows_arms(self.ty(arms[i].body)));
        for (ai, arm) in arms.iter().enumerate() {
            // A guard reads the arm's bindings by shared reference
            // (rustc binds pattern variables by reference for the
            // guard, then by their declared mode in the arm body):
            // bind for the guard first, and do the real binding,
            // moves included, only on the guard's success edge. A
            // failed guard then leaves the scrutinee whole for the
            // next arm. The one shape with no reference place to
            // read through, a by-value binding for the middle of
            // an array pattern, keeps the move-first order.
            let by_ref_guard = arm.guard.is_some() && !self.pat_has_slice_middle_move(arm.pat);
            // Under a guard, an or-pattern arm runs as one row
            // per combination of alternatives: a guard that
            // fails on one row tries the next matching row, as
            // in Rust, before the next arm (so the guard may run
            // more than once). Rows beyond a bound
            // keep the single tag-switched test; the checker
            // accepts those programs, so cap the expansion and
            // report it below instead of risking such a split.
            let rows: Vec<Vec<(PatId, usize)>> =
                if by_ref_guard && self.pat_has_or(arm.pat) { self.or_rows(arm.pat) } else { vec![Vec::new()] };
            if rows.len() > 64 {
                self.body.lower_errs.push(crate::diag::Diag::new(
                    "L9001",
                    span,
                    "a match guard over this many or-pattern alternatives is not supported yet",
                    "Split the arm into several arms, one per alternative.",
                ));
            }
            let expanded = rows.len() > 1 && rows.len() <= 64;
            let rows: Vec<Vec<(PatId, usize)>> = if expanded { rows } else { vec![Vec::new()] };
            let next = self.new_block();
            let body_bb = self.new_block();
            let row_starts: Vec<Bb> = (0..rows.len()).map(|r| if r == 0 { self.cur } else { self.new_block() }).collect();
            // A match nested in this arm's guard manages its own
            // rows; the outer rows resume after it.
            let saved_forced = std::mem::take(&mut self.or_forced);
            self.scopes.push(Vec::new());
            for (r, row) in rows.iter().enumerate() {
                self.cur = row_starts[r];
                let row_fail = if r + 1 < rows.len() { row_starts[r + 1] } else { next };
                self.or_forced = row.clone();
                self.test_pat(arm.pat, sp.clone(), row_fail);
                if arm.guard.is_none() {
                    self.false_edge_if_unreached(row_starts[r], next);
                }
                let mut guard_bound: Vec<u32> = Vec::new();
                let guard_popped;
                if by_ref_guard {
                    self.scopes.push(Vec::new());
                    self.bind_pat_guard(arm.pat, sp.clone(), &mut guard_bound);
                    guard_popped = false;
                } else {
                    self.bind_pat(arm.pat, sp.clone());
                    guard_popped = true;
                }
                match arm.guard {
                    Some(g) => {
                        let gspan = self.span(g);
                        self.scopes.push(Vec::new());
                        let held = self.hold_scrutinee(&sp, scrut_ty, gspan);
                        let c = self.operand(g);
                        // Mutable: the same local is written again on every
                        // pass when the match sits in a loop.
                        let cl = self.new_local(BOOL, true, None);
                        self.assign(Place::local(cl), Rvalue::Use(c), gspan);
                        self.push(StmtKind::FakeRead(held), gspan);
                        self.pop_scope(gspan);
                        for l in &guard_bound {
                            self.guard_places[*l as usize] = None;
                        }
                        let (ok, fail) = (self.new_block(), self.new_block());
                        let b = &mut self.body.blocks[self.cur.0 as usize];
                        b.term = Terminator::If(Operand::Copy(Place::local(cl)), ok, fail);
                        self.cur = fail;
                        let arm_locals = self.scopes.last().unwrap().clone();
                        self.emit_drops(&arm_locals, gspan);
                        self.goto(row_fail, gspan);
                        self.cur = ok;
                        if by_ref_guard {
                            // End the guard bindings' storage before the
                            // real binding moves out of the same places.
                            self.emit_drops(&arm_locals, gspan);
                            self.scopes.pop();
                            self.bind_pat(arm.pat, sp.clone());
                        }
                    }
                    None => {
                        debug_assert!(!expanded, "rows only expand under a guard");
                    }
                }
                if by_ref_guard && !guard_popped && arm.guard.is_none() {
                    self.scopes.pop();
                }
                self.goto(body_bb, span);
            }
            self.or_forced = saved_forced;
            self.cur = body_bb;
            let rb = reborrow && first.is_some_and(|i| ai > i) && !self.diverges(arm.body);
            self.arm_into(arm.body, rb, dest);
            self.pop_scope(span);
            self.goto(end, span);
            self.cur = next;
        }
        // Every arm's test failed: an exhaustive match ends here (rustc: unreachable).
        self.terminate(Terminator::MatchExhausted, span);
        self.cur = end;
    }

    /// A shared borrow of the scrutinee place that a guard holds until it
    /// ends (the caller emits the `FakeRead` of the returned local), as
    /// rustc's fake borrows of the matched places: a guard cannot assign
    /// to the scrutinee or borrow it mutably (E0510). rustc's borrows are
    /// shallow and cover only tested places; this one is deep, so a guard
    /// that writes an untested part is a false reject.
    fn hold_scrutinee(&mut self, sp: &Place, ty: Ty, span: Span) -> Local {
        let rt = self.ref_ty(false, ty);
        let t = self.temp(rt);
        self.assign(Place::local(t), Rvalue::Ref(false, sp.clone()), span);
        t
    }

    /// After an arm's pattern tests, which began in block `start`: when
    /// none of them jumps to `next` (the pattern is irrefutable), ends the
    /// current block and adds a borrowck-only edge from it to `next`, as
    /// rustc's false edge does, so the later arms are borrow-checked. The
    /// tests' blocks are `start` and every block made after `next`.
    fn false_edge_if_unreached(&mut self, start: Bb, next: Bb) {
        let jumps = |t: &Terminator| match t {
            Terminator::Goto(b) => *b == next,
            Terminator::If(_, a, b) => *a == next || *b == next,
            Terminator::Switch(_, cases, other) => *other == next || cases.iter().any(|c| c.1 == next),
            _ => false,
        };
        let blocks = &self.body.blocks;
        if jumps(&blocks[start.0 as usize].term) || blocks[next.0 as usize..].iter().any(|b| jumps(&b.term)) {
            return;
        }
        let pre = self.cur;
        let bind = self.new_block();
        self.goto(bind, Span::default());
        self.body.false_edges.push((pre, next));
    }

    /// True when a slice pattern in `pat` binds its middle by
    /// value: an owned smaller array (`rest @ ..` on an array).
    /// That value has no place to read by reference for a guard
    /// without moving the elements out, so `match_into` keeps
    /// the move-first order for such an arm (element copies on
    /// the guard edge; a non-`Copy` middle then fails borrowck
    /// when a later arm needs the scrutinee, as before). A
    /// middle of slice type is a fat value instead: the guard
    /// binds it by reference from a subslice temporary, like
    /// every other binding.
    fn pat_has_slice_middle_move(&self, pat: PatId) -> bool {
        if let Pat::Slice { middle, .. } = self.p.ast.pat(pat)
            && let Some(mid) = middle
            && self.pat_has_binding(*mid)
            && !matches!(self.kind(self.ck.pat_ty(*mid)), TyKind::Slice(_))
        {
            return true;
        }
        self.pat_children(pat).iter().any(|&s| self.pat_has_slice_middle_move(s))
    }

    /// A temporary holding the middle of a slice or array place
    /// as a slice fat value: elements `lo_n` up to `suffix_len`
    /// before the end.
    fn subslice_temp(&mut self, place: &Place, lo_n: usize, suffix_len: usize, arr_len: Option<u64>, elem: Ty, mutable: bool, span: Span) -> Local {
        let lo = self.const_usize(lo_n as u64, span);
        let hi = match arr_len {
            Some(n) => Operand::Const(Const::Int((n - suffix_len as u64) as u128, IntTy::Usize)),
            None => {
                let len = self.temp(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(place.clone()), span);
                let t = self.temp(USIZE);
                self.assign(
                    Place::local(t),
                    Rvalue::Bin(BinOp::Sub, Operand::Copy(Place::local(len)), Operand::Const(Const::Int(suffix_len as u128, IntTy::Usize))),
                    span,
                );
                self.body.pat_back_index.push((t, suffix_len as u64, (lo_n + suffix_len) as u64));
                Operand::Copy(Place::local(t))
            }
        };
        let slice = self.body.tys.intern(TyKind::Slice(elem));
        let t = self.temp(slice);
        self.assign(
            Place::local(t),
            Rvalue::Subslice { base: place.clone(), lo: Operand::Copy(Place::local(lo)), hi: Some(hi), inclusive: false, mutable },
            span,
        );
        self.body.pat_subslice.push(t);
        t
    }

    /// The direct sub-patterns of one pattern, in source order.
    fn pat_children(&self, pat: PatId) -> Vec<PatId> {
        match self.p.ast.pat(pat) {
            Pat::TupleStruct { elems, .. } | Pat::Tuple(elems) | Pat::Or(elems) => elems.clone(),
            Pat::Struct { fields, .. } => fields.iter().map(|&(_, s)| s).collect(),
            Pat::Slice { prefix, middle, suffix } => {
                let mut out: Vec<PatId> = prefix.clone();
                if let Some(m) = middle {
                    out.push(*m);
                }
                out.extend(suffix.iter().copied());
                out
            }
            Pat::Paren(i) | Pat::Ref { inner: i, .. } | Pat::At { inner: i, .. } => vec![*i],
            _ => Vec::new(),
        }
    }

    /// True when the pattern binds any name, itself or below.
    fn pat_has_binding(&self, pat: PatId) -> bool {
        matches!(self.ck.pat_res(pat), PatRes::Binding { .. }) || self.pat_children(pat).iter().any(|&s| self.pat_has_binding(s))
    }

    /// True when the pattern holds an or-pattern: the shape whose
    /// alternatives a guard must retry. Rust runs the guard once per
    /// matching combination of alternatives, with or without bindings
    /// (`Some(_) | Some(3) if g()` calls `g` twice on `Some(3)`).
    fn pat_has_or(&self, pat: PatId) -> bool {
        matches!(self.p.ast.pat(pat), Pat::Or(_)) || self.pat_children(pat).iter().any(|&s| self.pat_has_or(s))
    }

    /// The alternative a guard row fixes this or-pattern to.
    fn or_forced(&self, pat: PatId) -> Option<usize> {
        self.or_forced.iter().find(|&&(q, _)| q == pat).map(|&(_, i)| i)
    }

    /// The tag local for an or-pattern, made on first test.
    fn or_tag(&mut self, pat: PatId) -> Local {
        if let Some(&(_, l)) = self.or_tags.iter().find(|&&(q, _)| q == pat) {
            return l;
        }
        let l = self.temp(int(IntTy::U32));
        self.or_tags.push((pat, l));
        l
    }

    /// Every combination of or-pattern alternatives in one
    /// pattern, as a list of (or-pattern, alternative index)
    /// rows. Rust tries the rows in this order under a guard:
    /// a later or-pattern's alternatives cycle first.
    fn or_rows(&self, pat: PatId) -> Vec<Vec<(PatId, usize)>> {
        if let Pat::Or(alts) = self.p.ast.pat(pat) {
            let mut rows = Vec::new();
            for (i, &alt) in alts.iter().enumerate() {
                for sub in self.or_rows(alt) {
                    let mut row = vec![(pat, i)];
                    row.extend(sub);
                    rows.push(row);
                }
            }
            return rows;
        }
        let mut rows: Vec<Vec<(PatId, usize)>> = vec![Vec::new()];
        for child in self.pat_children(pat) {
            let sub = self.or_rows(child);
            let mut next = Vec::with_capacity(rows.len() * sub.len());
            for row in &rows {
                for s in &sub {
                    let mut r = row.clone();
                    r.extend(s.iter().copied());
                    next.push(r);
                }
            }
            rows = next;
        }
        rows
    }

    /// Records one pattern binding for guard evaluation: a fresh
    /// shared-reference local that borrows `place`, with
    /// `guard_places` set so the guard reads the binding through
    /// it. A move binding reads the value at `*tmp` (a move out of
    /// it in the guard is then a move out of a reference, and a
    /// mutable borrow of it borrows through a shared reference:
    /// both errors, as in rustc); a `ref` binding, whose value is
    /// itself a reference, reads as the local holding a shared
    /// borrow of the same place. The temporaries go in the
    /// innermost scope and need no drop.
    fn guard_binding(&mut self, local: u32, mode: BindMode, value_ty: Ty, place: Place, span: Span, bound: &mut Vec<u32>) {
        // Every alternative (and guard row) that binds this
        // local writes the one guard temporary: the blocks
        // merge before the guard reads it.
        let t = match self.guard_temps.iter().find(|&&(l, _)| l == local) {
            Some(&(_, t)) => t,
            None => {
                let name = self.p.name(self.ck.locals[local as usize].name).to_string();
                let rt = self.ref_ty(false, value_ty);
                let t = self.new_local(rt, false, Some(name));
                self.guard_temps.push((local, t));
                t
            }
        };
        if !self.scopes.last().unwrap().contains(&t) {
            self.scopes.last_mut().unwrap().push(t);
        }
        self.assign(Place::local(t), Rvalue::Ref(false, place), span);
        self.guard_places[local as usize] = Some(match mode {
            BindMode::Move => Place::local(t).deref(),
            BindMode::Ref(_) => Place::local(t),
        });
        if !bound.contains(&local) {
            bound.push(local);
        }
    }

    /// Binds an already-tested pattern for a match guard, mirroring
    /// `bind_pat` case by case, but by shared reference (see
    /// `guard_binding`). Records every bound checker local in
    /// `bound` so the caller can clear `guard_places` after the
    /// guard. A by-value array middle binding never reaches
    /// here (see `pat_has_slice_middle_move`); a slice middle
    /// reads through a shared subslice temporary.
    fn bind_pat_guard(&mut self, pat: PatId, place: Place, bound: &mut Vec<u32>) {
        let p = self.p;
        let place = Self::derefs(place, self.ck.pat_derefs(pat));
        let span = p.ast.pat_span(pat);
        match (p.ast.pat(pat), self.ck.pat_res(pat)) {
            (Pat::Binding { .. }, PatRes::Binding { local, mode }) => {
                self.guard_binding(local, mode, self.ck.pat_ty(pat), place, span, bound);
            }
            (Pat::TupleStruct { elems, .. }, PatRes::Opt(true)) => {
                self.bind_pat_guard(elems[0], place.project(Proj::Downcast(1)).project(Proj::Field(0)), bound);
            }
            (Pat::TupleStruct { elems, .. }, PatRes::Res(is_ok)) => {
                self.bind_pat_guard(elems[0], place.project(Proj::Downcast((!is_ok) as u32)).project(Proj::Field(0)), bound);
            }
            (Pat::TupleStruct { .. } | Pat::Struct { .. }, PatRes::Variant(a, v)) => {
                let base = if p.adt(a).is_enum { place.project(Proj::Downcast(v)) } else { place };
                for (i, sub) in self.sub_pats(pat, a, v) {
                    self.bind_pat_guard(sub, base.project(Proj::Field(i)), bound);
                }
            }
            (Pat::Tuple(elems), _) => {
                let ty = self.ck.pat_ty(pat);
                let n = match self.kind(ty) {
                    TyKind::Tuple(ts) => self.body.tys.tys_of(ts).len(),
                    _ => elems.len(),
                };
                if let Some(mapped) = crate::check::map_tuple_elems(&p.ast, elems, n) {
                    for (i, sub) in mapped {
                        self.bind_pat_guard(sub, place.project(Proj::Field(i as u32)), bound);
                    }
                }
            }
            (Pat::Paren(inner), _) => self.bind_pat_guard(*inner, place, bound),
            (Pat::Slice { prefix, middle, suffix }, _) => {
                let ty = self.ck.pat_ty(pat);
                let (elem, arr_len) = match self.kind(ty) {
                    TyKind::Array(e, c) => {
                        let n = match self.body.tys.const_kind(c) {
                            ConstKind::Int(n) => Some(n as u64),
                            _ => None,
                        };
                        (e, n)
                    }
                    TyKind::Slice(e) => (e, None),
                    _ => (ERROR, None),
                };
                // Index and length temporaries first: a `LenOf`
                // read between two mutable element borrows of
                // the same slice would read a mutably borrowed
                // place (the bindings are disjoint by the
                // pattern's own length test).
                let suffix_idx: Vec<Local> = suffix
                    .iter()
                    .enumerate()
                    .map(|(j, _)| self.slice_back_index(&place, (suffix.len() - j) as u64, arr_len, (prefix.len() + suffix.len()) as u64, span))
                    .collect();
                // The middle binding reads a shared subslice of
                // the same place for the guard; the real binding
                // makes its own (possibly mutable) one later. A
                // by-value array middle never reaches here (see
                // `pat_has_slice_middle_move`).
                let mid_temp = match middle {
                    Some(mid) if self.pat_has_binding(*mid) => {
                        Some(self.subslice_temp(&place, prefix.len(), suffix.len(), arr_len, elem, false, span))
                    }
                    _ => None,
                };
                for (i, &sub) in prefix.iter().enumerate() {
                    let idx = self.pat_front_index(i as u64, (prefix.len() + suffix.len()) as u64, span);
                    self.bind_pat_guard(sub, place.project(Proj::Index(idx)), bound);
                }
                for (j, &sub) in suffix.iter().enumerate() {
                    self.bind_pat_guard(sub, place.project(Proj::Index(suffix_idx[j])), bound);
                }
                if let (Some(mid), Some(t)) = (middle, mid_temp) {
                    self.bind_pat_guard(*mid, Place::local(t), bound);
                }
            }
            (Pat::Ref { inner, .. }, _) => self.bind_pat_guard(*inner, place.deref(), bound),
            (Pat::At { inner, .. }, PatRes::Binding { local, mode }) => {
                self.bind_pat_guard(*inner, place.clone(), bound);
                self.guard_binding(local, mode, self.ck.pat_ty(pat), place, span, bound);
            }
            (Pat::Or(alts), _) => {
                // Bind by reference for the alternative that
                // matched: the row's forced alternative, else a
                // switch on the test's tag (see `test_pat`).
                if !self.pat_has_binding(pat) || alts.is_empty() {
                    return;
                }
                if let Some(i) = self.or_forced(pat) {
                    self.bind_pat_guard(alts[i], place, bound);
                    return;
                }
                let alts = alts.clone();
                match self.or_tags.iter().find(|&&(q, _)| q == pat).map(|&(_, l)| l) {
                    Some(tag) => {
                        let end = self.new_block();
                        // The otherwise edge cannot run (a test
                        // set the tag), and must not look like a
                        // path where the bindings stay unassigned.
                        let bad = self.new_block();
                        self.body.blocks[bad.0 as usize].term = Terminator::Unreachable;
                        let branches: Vec<(u32, Bb)> = (0..alts.len()).map(|i| (i as u32, self.new_block())).collect();
                        let b = &mut self.body.blocks[self.cur.0 as usize];
                        b.term = Terminator::Switch(Operand::Copy(Place::local(tag)), branches.clone(), bad);
                        b.term_span = span;
                        for (i, &(_, bb)) in branches.iter().enumerate() {
                            self.cur = bb;
                            self.bind_pat_guard(alts[i], place.clone(), bound);
                            self.goto(end, span);
                        }
                        self.cur = end;
                    }
                    None => {
                        // No test ran (a `let` or parameter bind
                        // reached a guard bind first): try each
                        // alternative, as `bind_pat` does.
                        let end = self.new_block();
                        for &alt in &alts {
                            let next = self.new_block();
                            self.test_pat(alt, place.clone(), next);
                            self.bind_pat_guard(alt, place.clone(), bound);
                            self.goto(end, span);
                            self.cur = next;
                        }
                        self.terminate(Terminator::Unreachable, span);
                        self.cur = end;
                    }
                }
            }
            _ => {}
        }
    }

    /// The bytes of a byte string literal pattern, which the parser
    /// builds as a reference to one blob node (an empty C string in
    /// cfg syntax keeps the empty array form).
    fn byte_str_bytes(&self, l: ExprId) -> Option<Vec<u8>> {
        let Expr::Ref { mutable: false, raw: false, expr } = self.p.ast.expr(l) else { return None };
        if let Expr::ByteStr(i) = self.p.ast.expr(*expr) {
            return self.p.ast.blobs.get(*i as usize).map(|b| b.as_slice().to_vec());
        }
        let Expr::Array(elems) = self.p.ast.expr(*expr) else { return None };
        let mut out = Vec::with_capacity(elems.len());
        for &e in elems {
            match self.p.ast.expr(e) {
                Expr::Int(v, Some(crate::lexer::IntSuffix::U8)) => out.push(*v as u8),
                _ => return None,
            }
        }
        Some(out)
    }

    fn lit_operand(&mut self, l: ExprId, ty: Ty) -> Operand {
        match self.p.ast.expr(l) {
            Expr::Unary { expr, .. } => match (self.p.ast.expr(*expr), self.kind(ty)) {
                (Expr::Int(v, _), TyKind::Int(it)) => Operand::Const(Const::Int(v.wrapping_neg(), it)),
                (Expr::Float(i), TyKind::Float(ft)) => {
                    let text = &self.p.ast.strings[*i as usize];
                    // Negation flips only the sign bit, as in rustc:
                    // `-0.0` stays distinct in bits from `0.0`.
                    match crate::check::collect::parse_float_literal_as(text, ft) {
                        Some(bits) => {
                            let sign = match ft {
                                FloatTy::F32 => 1u64 << 31,
                                FloatTy::F64 => 1u64 << 63,
                            };
                            Operand::Const(Const::Float(bits ^ sign, ft))
                        }
                        None => Operand::Const(Const::Unit),
                    }
                }
                _ => Operand::Const(Const::Unit),
            },
            Expr::Int(v, _) => match self.kind(ty) {
                TyKind::Int(it) => Operand::Const(Const::Int(*v, it)),
                _ => Operand::Const(Const::Int(*v, IntTy::I32)),
            },
            Expr::Float(i) => {
                let text = &self.p.ast.strings[*i as usize];
                let ft = match self.kind(ty) {
                    TyKind::Float(f) => f,
                    _ => FloatTy::F64,
                };
                // Parse straight to the literal's type: one rounding.
                match crate::check::collect::parse_float_literal_as(text, ft) {
                    Some(bits) => Operand::Const(Const::Float(bits, ft)),
                    None => Operand::Const(Const::Unit),
                }
            }
            Expr::Bool(b) => Operand::Const(Const::Bool(*b)),
            Expr::Char(c) => Operand::Const(Const::Char(*c)),
            Expr::Str(s) => Operand::Const(Const::Str(*s)),
            Expr::Path(_) | Expr::QPath { .. } => self.operand_raw(l),
            _ => Operand::Const(Const::Unit),
        }
    }

    /// A usize local holding a constant, for slice pattern indexes.
    fn const_usize(&mut self, v: u64, span: Span) -> Local {
        let t = self.temp(USIZE);
        self.assign(Place::local(t), Rvalue::Use(Operand::Const(Const::Int(v as u128, IntTy::Usize))), span);
        t
    }

    /// The index local for a slice pattern's prefix element, recorded
    /// for borrowck with the pattern's length lower bound.
    fn pat_front_index(&mut self, i: u64, min_len: u64, span: Span) -> Local {
        let idx = self.const_usize(i, span);
        self.body.pat_front_index.push((idx, i, min_len));
        idx
    }

    /// The index local for an element `back` positions from the end of a
    /// slice or array place. `min_len` is the pattern's length lower
    /// bound for this place (its fixed element count).
    fn slice_back_index(&mut self, place: &Place, back: u64, arr_len: Option<u64>, min_len: u64, span: Span) -> Local {
        match arr_len {
            Some(n) => self.const_usize(n - back, span),
            None => {
                let len = self.temp(USIZE);
                self.assign(Place::local(len), Rvalue::LenOf(place.clone()), span);
                let idx = self.temp(USIZE);
                self.assign(
                    Place::local(idx),
                    Rvalue::Bin(BinOp::Sub, Operand::Copy(Place::local(len)), Operand::Const(Const::Int(back as u128, IntTy::Usize))),
                    span,
                );
                self.body.pat_back_index.push((idx, back, min_len));
                idx
            }
        }
    }

    /// Emits the tests of a structural const pattern (a value the
    /// checker's `const_structural` accepted) against `place` of type
    /// `ty`, field by field as rustc's const-to-pattern does: scalars
    /// by `==` (so `-0.0` matches `0.0`), `&str` by content, variants
    /// by discriminant, references through their pointee, and slices
    /// by length first. Falls through on a match; jumps to `fail`.
    fn test_const_value(&mut self, cv: &crate::ty::consteval::ConstValue, ty: Ty, place: Place, fail: Bb, span: Span) {
        use crate::ty::consteval::ConstValue as CV;
        let branch = |this: &mut Self, cond: Rvalue| {
            let c = this.temp(BOOL);
            this.assign(Place::local(c), cond, span);
            let ok = this.new_block();
            let b = &mut this.body.blocks[this.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), ok, fail);
            this.cur = ok;
        };
        let switch = |this: &mut Self, place: &Place, v: u32| {
            let d = this.temp(int(IntTy::U32));
            this.assign(Place::local(d), Rvalue::Discriminant(place.clone()), span);
            let ok = this.new_block();
            let b = &mut this.body.blocks[this.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(v, ok)], fail);
            this.cur = ok;
        };
        match (self.kind(ty), cv) {
            (_, CV::Unit) => {}
            (_, CV::Int(_) | CV::Float(..) | CV::Bool(_) | CV::Char(_)) => {
                let op = self.const_operand(cv, ty, span);
                branch(self, Rvalue::Bin(BinOp::Eq, Operand::Copy(place), op));
            }
            (_, CV::Str(i)) => branch(self, Rvalue::StrCmp(BinOp::Eq, Operand::Copy(place), Operand::Const(Const::Str(*i)))),
            (TyKind::Ref(_, _, inner), CV::Ref(v)) => self.test_const_value(v, inner, place.deref(), fail, span),
            // A slice reference holds its backing array in place.
            (TyKind::Ref(_, _, inner), _) => self.test_const_value(cv, inner, place.deref(), fail, span),
            (TyKind::Tuple(ts), CV::Aggregate(vals)) => {
                let ts = self.body.tys.tys_of(ts).to_vec();
                for (i, (v, ft)) in vals.iter().zip(ts).enumerate() {
                    self.test_const_value(v, ft, place.project(Proj::Field(i as u32)), fail, span);
                }
            }
            (TyKind::Array(el, _) | TyKind::Slice(el), CV::Aggregate(_) | CV::Repeat(..) | CV::Bytes(_)) => {
                let n = match cv {
                    CV::Aggregate(vals) => vals.len(),
                    CV::Repeat(_, n) => *n as usize,
                    CV::Bytes(b) => b.len(),
                    _ => 0,
                };
                if matches!(self.kind(ty), TyKind::Slice(_)) {
                    let len = self.temp(USIZE);
                    self.assign(Place::local(len), Rvalue::LenOf(place.clone()), span);
                    branch(self, Rvalue::Bin(BinOp::Eq, Operand::Copy(Place::local(len)), Operand::Const(Const::Int(n as u128, IntTy::Usize))));
                }
                for i in 0..n {
                    let idx = self.const_usize(i as u64, span);
                    let at = place.project(Proj::Index(idx));
                    match cv {
                        CV::Aggregate(vals) => self.test_const_value(&vals[i], el, at, fail, span),
                        CV::Repeat(v, _) => self.test_const_value(v, el, at, fail, span),
                        CV::Bytes(b) => branch(self, Rvalue::Bin(BinOp::Eq, Operand::Copy(at), Operand::Const(Const::Int(b.as_slice()[i] as u128, IntTy::U8)))),
                        _ => {}
                    }
                }
            }
            (_, CV::Variant(v, vals)) if self.body.tys.option_elem(ty).is_some() => {
                let elem = self.body.tys.option_elem(ty).unwrap_or(ERROR);
                switch(self, &place, *v);
                if let [x] = vals.as_slice() {
                    self.test_const_value(x, elem, place.project(Proj::Downcast(1)).project(Proj::Field(0)), fail, span);
                }
            }
            (_, CV::Variant(v, vals)) if self.body.tys.result_args(ty).is_some() => {
                let (ok_t, err_t) = self.body.tys.result_args(ty).unwrap_or((ERROR, ERROR));
                switch(self, &place, *v);
                if let [x] = vals.as_slice() {
                    let ft = if *v == 0 { ok_t } else { err_t };
                    self.test_const_value(x, ft, place.project(Proj::Downcast(*v)).project(Proj::Field(0)), fail, span);
                }
            }
            (_, CV::Aggregate(vals) | CV::Variant(_, vals)) => {
                let Some(a) = self.body.tys.local_adt(ty) else { return };
                let v = match cv {
                    CV::Variant(v, _) if self.p.adt(a).is_enum => {
                        switch(self, &place, *v);
                        *v
                    }
                    _ => 0,
                };
                let base = if self.p.adt(a).is_enum { place.project(Proj::Downcast(v)) } else { place };
                let args: Vec<GenericArg> = match self.kind(ty) {
                    TyKind::Adt(_, aa) => self.body.tys.args(aa).to_vec(),
                    _ => Vec::new(),
                };
                let fields: Vec<Ty> = self.p.adt(a).variants[v as usize].fields.iter().map(|f| f.ty).collect();
                for (i, (x, ft)) in vals.iter().zip(fields).enumerate() {
                    let ft = subst(&mut self.body.tys, ft, &args);
                    self.test_const_value(x, ft, base.project(Proj::Field(i as u32)), fail, span);
                }
            }
            _ => {}
        }
    }

    /// Emits tests for `pat` against `place`. Falls through on a match; jumps to `fail` otherwise.
    fn test_pat(&mut self, pat: PatId, place: Place, fail: Bb) {
        use crate::ty::consteval::ConstValue as CV;
        let p = self.p;
        let place = Self::derefs(place, self.ck.pat_derefs(pat));
        let ty = self.ck.pat_ty(pat);
        let span = p.ast.pat_span(pat);
        if let PatRes::Opt(some) = self.ck.pat_res(pat) {
            let d = self.temp(int(IntTy::U32));
            self.assign(Place::local(d), Rvalue::Discriminant(place.clone()), span);
            let ok = self.new_block();
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(some as u32, ok)], fail);
            self.cur = ok;
            if let (true, Pat::TupleStruct { elems, .. }) = (some, p.ast.pat(pat)) {
                self.test_pat(elems[0], place.project(Proj::Downcast(1)).project(Proj::Field(0)), fail);
            }
            return;
        }
        // `Entry::Occupied(_)` / `Entry::Vacant(_)`: the Entry's slot test
        // (its payload pattern is a binding or `_`, check/mod.rs).
        if let PatRes::Entry(occupied) = self.ck.pat_res(pat) {
            let rt = self.ref_ty(false, ty);
            let r = self.temp(rt);
            self.assign(Place::local(r), Rvalue::Ref(false, place), span);
            let c = self.temp(BOOL);
            self.call_into(CallTarget::Builtin(Builtin::EntryOccupied), vec![Operand::Move(Place::local(r))], Place::local(c), span);
            let ok = self.new_block();
            let (tb, eb) = if occupied { (ok, fail) } else { (fail, ok) };
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), tb, eb);
            self.cur = ok;
            return;
        }
        if let PatRes::Res(is_ok) = self.ck.pat_res(pat) {
            let d = self.temp(int(IntTy::U32));
            self.assign(Place::local(d), Rvalue::Discriminant(place.clone()), span);
            let ok = self.new_block();
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![((!is_ok) as u32, ok)], fail);
            self.cur = ok;
            if let Pat::TupleStruct { elems, .. } = p.ast.pat(pat) {
                self.test_pat(elems[0], place.project(Proj::Downcast((!is_ok) as u32)).project(Proj::Field(0)), fail);
            }
            return;
        }
        let const_pat = match self.ck.pat_res(pat) {
            PatRes::ConstItem(idx) => Some(p.consts[idx as usize].value.clone()),
            PatRes::PrimConst(v) => Some(crate::ty::consteval::ConstValue::Int(v)),
            PatRes::BodyConst(idx) => Some(p.body_consts[idx as usize].value.clone()),
            _ => None,
        };
        if let Some(cv) = const_pat {
            if !matches!(cv, CV::Int(_) | CV::Float(..) | CV::Bool(_) | CV::Char(_) | CV::Str(_)) {
                self.test_const_value(&cv, ty, place, fail, span);
                return;
            }
            let op = self.const_operand(&cv, ty, span);
            let c = self.temp(BOOL);
            let cond = if matches!(cv, crate::ty::consteval::ConstValue::Str(_)) {
                Rvalue::StrCmp(BinOp::Eq, Operand::Copy(place), op)
            } else {
                Rvalue::Bin(BinOp::Eq, Operand::Copy(place), op)
            };
            self.assign(Place::local(c), cond, span);
            let ok = self.new_block();
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), ok, fail);
            self.cur = ok;
            return;
        }
        if let Some(cv) = self.ck.pat_const(pat).cloned() {
            let op = self.const_operand(&cv, ty, span);
            let c = self.temp(BOOL);
            self.assign(Place::local(c), Rvalue::Bin(BinOp::Eq, Operand::Copy(place), op), span);
            let ok = self.new_block();
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), ok, fail);
            self.cur = ok;
            return;
        }
        // A lone identifier that resolved to a unit variant tests the
        // discriminant, exactly like the written path form.
        if let (Pat::Binding { .. }, PatRes::Variant(a, v)) = (p.ast.pat(pat), self.ck.pat_res(pat))
            && p.adt(a).is_enum
        {
            let d = self.temp(int(IntTy::U32));
            self.assign(Place::local(d), Rvalue::Discriminant(place), span);
            let ok = self.new_block();
            let b = &mut self.body.blocks[self.cur.0 as usize];
            b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(v, ok)], fail);
            self.cur = ok;
            return;
        }
        let branch = |this: &mut Self, cond: Rvalue| {
            let c = this.temp(BOOL);
            this.assign(Place::local(c), cond, span);
            let ok = this.new_block();
            let b = &mut this.body.blocks[this.cur.0 as usize];
            b.term = Terminator::If(Operand::Copy(Place::local(c)), ok, fail);
            this.cur = ok;
        };
        match p.ast.pat(pat) {
            Pat::Wild | Pat::Binding { .. } => {}
            Pat::Lit(l) => {
                if let Some(bytes) = self.byte_str_bytes(*l) {
                    // A byte string pattern: `place` holds `&[u8; N]`
                    // or `&[u8]`. A slice needs a length test first;
                    // then each byte must be equal.
                    let base = place.deref();
                    let is_slice = match self.kind(ty) {
                        TyKind::Ref(_, _, inner) => matches!(self.kind(inner), TyKind::Slice(_)),
                        _ => false,
                    };
                    if is_slice {
                        let len = self.temp(USIZE);
                        self.assign(Place::local(len), Rvalue::LenOf(base.clone()), span);
                        branch(
                            self,
                            Rvalue::Bin(
                                BinOp::Eq,
                                Operand::Copy(Place::local(len)),
                                Operand::Const(Const::Int(bytes.len() as u128, IntTy::Usize)),
                            ),
                        );
                    }
                    for (i, b) in bytes.iter().enumerate() {
                        let idx = self.const_usize(i as u64, span);
                        branch(
                            self,
                            Rvalue::Bin(
                                BinOp::Eq,
                                Operand::Copy(base.project(Proj::Index(idx))),
                                Operand::Const(Const::Int(*b as u128, IntTy::U8)),
                            ),
                        );
                    }
                    return;
                }
                let lit = self.lit_operand(*l, ty);
                if matches!(lit, Operand::Const(Const::Str(_))) {
                    branch(self, Rvalue::StrCmp(BinOp::Eq, Operand::Copy(place), lit));
                } else {
                    branch(self, Rvalue::Bin(BinOp::Eq, Operand::Copy(place), lit));
                }
            }
            Pat::Range { lo, hi, inclusive } => {
                if let Some(lo) = lo {
                    let a = self.lit_operand(*lo, ty);
                    branch(self, Rvalue::Bin(BinOp::Ge, Operand::Copy(place.clone()), a));
                }
                if let Some(hi) = hi {
                    let b = self.lit_operand(*hi, ty);
                    let op = if *inclusive { BinOp::Le } else { BinOp::Lt };
                    branch(self, Rvalue::Bin(op, Operand::Copy(place), b));
                }
            }
            Pat::Slice { prefix, middle, suffix } => {
                let fixed = (prefix.len() + suffix.len()) as u64;
                let arr_len = match self.kind(ty) {
                    TyKind::Array(_, c) => match self.body.tys.const_kind(c) {
                        ConstKind::Int(n) => Some(n as u64),
                        _ => None,
                    },
                    _ => None,
                };
                if arr_len.is_none() {
                    // A slice place needs a runtime length test.
                    let len = self.temp(USIZE);
                    self.assign(Place::local(len), Rvalue::LenOf(place.clone()), span);
                    let op = if middle.is_some() { BinOp::Ge } else { BinOp::Eq };
                    branch(
                        self,
                        Rvalue::Bin(op, Operand::Copy(Place::local(len)), Operand::Const(Const::Int(fixed as u128, IntTy::Usize))),
                    );
                }
                for (i, &sub) in prefix.iter().enumerate() {
                    let idx = self.pat_front_index(i as u64, fixed, span);
                    self.test_pat(sub, place.project(Proj::Index(idx)), fail);
                }
                for (j, &sub) in suffix.iter().enumerate() {
                    let back = (suffix.len() - j) as u64;
                    let idx = self.slice_back_index(&place, back, arr_len, fixed, span);
                    self.test_pat(sub, place.project(Proj::Index(idx)), fail);
                }
            }
            Pat::Path(_) | Pat::QPath { .. } | Pat::TupleStruct { .. } | Pat::Struct { .. } => {
                let PatRes::Variant(a, v) = self.ck.pat_res(pat) else { return };
                let is_enum = p.adt(a).is_enum;
                if is_enum {
                    let d = self.temp(int(IntTy::U32));
                    self.assign(Place::local(d), Rvalue::Discriminant(place.clone()), span);
                    let ok = self.new_block();
                    let b = &mut self.body.blocks[self.cur.0 as usize];
                    b.term = Terminator::Switch(Operand::Copy(Place::local(d)), vec![(v, ok)], fail);
                    self.cur = ok;
                }
                let base = if is_enum { place.project(Proj::Downcast(v)) } else { place };
                for (i, sub) in self.sub_pats(pat, a, v) {
                    self.test_pat(sub, base.project(Proj::Field(i)), fail);
                }
            }
            Pat::Or(alts) => {
                // One guard row tests only its fixed alternative.
                if let Some(i) = self.or_forced(pat) {
                    self.test_pat(alts[i], place, fail);
                    return;
                }
                let alts = alts.clone();
                // With bindings, remember which alternative
                // matched in a tag: the binding moves happen
                // only after the whole pattern and guard pass,
                // when the merged block no longer knows.
                let tag = if self.pat_has_binding(pat) { Some(self.or_tag(pat)) } else { None };
                let cont = self.new_block();
                for (i, &alt) in alts.iter().enumerate() {
                    let next = self.new_block();
                    self.test_pat(alt, place.clone(), next);
                    if let Some(tag) = tag {
                        self.assign(
                            Place::local(tag),
                            Rvalue::Use(Operand::Const(Const::Int(i as u128, IntTy::U32))),
                            span,
                        );
                    }
                    self.goto(cont, span);
                    self.cur = next;
                }
                self.terminate(Terminator::Goto(fail), span);
                self.cur = cont;
            }
            Pat::Tuple(elems) => {
                let n = match self.kind(ty) {
                    TyKind::Tuple(ts) => self.body.tys.tys_of(ts).len(),
                    _ => elems.len(),
                };
                if let Some(mapped) = crate::check::map_tuple_elems(&p.ast, elems, n) {
                    for (i, sub) in mapped {
                        self.test_pat(sub, place.project(Proj::Field(i as u32)), fail);
                    }
                }
            }
            Pat::Rest => {}
            Pat::Paren(inner) => self.test_pat(*inner, place, fail),
            Pat::At { inner, .. } => self.test_pat(*inner, place, fail),
            Pat::Ref { inner, .. } => self.test_pat(*inner, place.deref(), fail),
            // AST v2 pattern forms the parser still rejects.
            Pat::Slice { .. } | Pat::QPath { .. } | Pat::MacroCall(_) => {}
        }
    }

    /// Sub-patterns of a struct or variant pattern, with their field indexes.
    fn sub_pats(&self, pat: PatId, a: AdtId, v: u32) -> Vec<(u32, PatId)> {
        let p = self.p;
        match p.ast.pat(pat) {
            Pat::TupleStruct { elems, .. } => {
                let n = p.adt(a).variants[v as usize].fields.len();
                crate::check::map_tuple_elems(&p.ast, elems, n).unwrap_or_default().into_iter().map(|(i, s)| (i as u32, s)).collect()
            }
            Pat::Struct { fields, .. } => {
                let vf = &p.adt(a).variants[v as usize].fields;
                fields.iter().filter_map(|&(n, s)| vf.iter().position(|f| f.name == n).map(|i| (i as u32, s))).collect()
            }
            _ => Vec::new(),
        }
    }

    /// Binds one checker local from `place` by `mode`. The
    /// first call for a local makes its IR local; later calls
    /// (the other or-pattern alternatives of the same name, the
    /// other guard rows, an unrolled loop's copies) assign into
    /// that same local, and scope membership is per bind site.
    fn bind_one(&mut self, local: u32, mode: BindMode, place: Place, value_ty: Ty, span: Span) {
        let l = match self.bind_reuse.iter().find(|&&(c, _)| c == local) {
            Some(&(_, l)) => l,
            None => {
                let info = &self.ck.locals[local as usize];
                let (ty, m, name) = (info.ty, info.mutable, self.p.name(info.name).to_string());
                let l = self.new_local(ty, m, Some(name));
                self.bind_reuse.push((local, l));
                self.bind_of.push((l, local));
                l
            }
        };
        self.local_map[local as usize] = l;
        let rv = match mode {
            BindMode::Move if self.local_moved(local) => Rvalue::Use(Operand::Move(place)),
            BindMode::Move => Rvalue::Use(self.operand_from(place, value_ty)),
            BindMode::Ref(m) => Rvalue::Ref(m, place),
        };
        self.assign(Place::local(l), rv, span);
        if !self.scopes.last().unwrap().contains(&l) {
            self.scopes.last_mut().unwrap().push(l);
        }
    }

    /// Binds the variables of an already-tested pattern.
    /// rustc's pattern-level check of `x @ sub`, which holds even when the
    /// bindings are never used: a by-move non-Copy `x` cannot have `ref`
    /// bindings in `sub` (L0301), a by-ref `x` cannot have by-move non-Copy
    /// ones (L0311), and `ref mut` conflicts with any other by-ref binding
    /// (L0303). Modes are after default binding modes. A pattern bound
    /// more than once (guard rows) reports once.
    fn check_at_conflicts(&mut self, pat: PatId, inner: PatId, mode: BindMode) {
        let mut subs: Vec<(BindMode, Ty)> = Vec::new();
        let mut stack = vec![inner];
        while let Some(q) = stack.pop() {
            if let PatRes::Binding { mode, .. } = self.ck.pat_res(q)
                && matches!(self.p.ast.pat(q), Pat::Binding { .. } | Pat::At { .. })
            {
                subs.push((mode, self.ck.pat_ty(q)));
            }
            stack.extend(self.pat_children(q));
        }
        let moves = |this: &Self, t: Ty| !is_copy(this.p, &this.body.tys, t);
        let err = match mode {
            BindMode::Move if !moves(self, self.ck.pat_ty(pat)) => None,
            BindMode::Move => subs
                .iter()
                .any(|&(m, _)| m != BindMode::Move)
                .then_some(("L0301", "borrow of moved value: the `@` binding moves the value its subpattern borrows")),
            BindMode::Ref(outer) => {
                if subs.iter().any(|&(m, t)| m == BindMode::Move && moves(self, t)) {
                    Some(("L0311", "cannot move out of a value the `@` binding borrows"))
                } else if subs.iter().any(|&(m, _)| matches!(m, BindMode::Ref(inner) if inner || outer)) {
                    Some(("L0303", "cannot borrow a value as mutable because the `@` pattern also borrows it"))
                } else {
                    None
                }
            }
        };
        let span = self.p.ast.pat_span(pat);
        if let Some((code, msg)) = err
            && !self.body.lower_errs.iter().any(|d| d.span == span && d.code == code)
        {
            let fix = "Bind the parts in the subpattern only, or bind the whole value by `ref` with `ref` parts.";
            self.body.lower_errs.push(crate::diag::Diag::new(code, span, msg, fix));
        }
    }

    fn bind_pat(&mut self, pat: PatId, place: Place) {
        // Or-pattern tags a re-test inside this bind made belong
        // to this one bind: a statically repeated bind of the
        // same pattern (an unrolled loop) tests again.
        let snap = if self.bind_depth == 0 { Some(self.or_tags.len()) } else { None };
        self.bind_depth += 1;
        self.bind_pat_go(pat, place);
        self.bind_depth -= 1;
        if let Some(snap) = snap {
            self.or_tags.truncate(snap);
        }
    }

    fn bind_pat_go(&mut self, pat: PatId, place: Place) {
        let p = self.p;
        let place = Self::derefs(place, self.ck.pat_derefs(pat));
        let span = p.ast.pat_span(pat);
        match (p.ast.pat(pat), self.ck.pat_res(pat)) {
            (Pat::Binding { .. }, PatRes::Binding { local, mode }) => {
                let value_ty = self.ck.pat_ty(pat);
                self.bind_one(local, mode, place, value_ty, span);
            }
            (Pat::TupleStruct { elems, .. }, PatRes::Opt(true)) => {
                self.bind_pat(elems[0], place.project(Proj::Downcast(1)).project(Proj::Field(0)));
            }
            (Pat::TupleStruct { elems, .. }, PatRes::Res(is_ok)) => {
                self.bind_pat(elems[0], place.project(Proj::Downcast((!is_ok) as u32)).project(Proj::Field(0)));
            }
            // The payload binding takes the Entry by value, read as the
            // variant's entry type (`_` leaves it in place).
            (Pat::TupleStruct { elems, .. }, PatRes::Entry(occupied)) => {
                let sub = elems[0];
                if !matches!(p.ast.pat(sub), Pat::Wild) {
                    let pt = self.ck.pat_ty(sub);
                    let tmp = self.temp(pt);
                    let b = if occupied { Builtin::EntryAsOccupied } else { Builtin::EntryAsVacant };
                    self.call_into(CallTarget::Builtin(b), vec![Operand::Move(place)], Place::local(tmp), span);
                    self.bind_pat(sub, Place::local(tmp));
                }
            }
            (Pat::TupleStruct { .. } | Pat::Struct { .. }, PatRes::Variant(a, v)) => {
                let base = if p.adt(a).is_enum { place.project(Proj::Downcast(v)) } else { place };
                for (i, sub) in self.sub_pats(pat, a, v) {
                    self.bind_pat(sub, base.project(Proj::Field(i)));
                }
            }
            (Pat::Tuple(elems), _) => {
                let ty = self.ck.pat_ty(pat);
                let n = match self.kind(ty) {
                    TyKind::Tuple(ts) => self.body.tys.tys_of(ts).len(),
                    _ => elems.len(),
                };
                if let Some(mapped) = crate::check::map_tuple_elems(&p.ast, elems, n) {
                    for (i, sub) in mapped {
                        self.bind_pat(sub, place.project(Proj::Field(i as u32)));
                    }
                }
            }
            (Pat::Paren(inner), _) => self.bind_pat(*inner, place),
            (Pat::Slice { prefix, middle, suffix }, _) => {
                let ty = self.ck.pat_ty(pat);
                let (elem, arr_len) = match self.kind(ty) {
                    TyKind::Array(e, c) => {
                        let n = match self.body.tys.const_kind(c) {
                            ConstKind::Int(n) => Some(n as u64),
                            _ => None,
                        };
                        (e, n)
                    }
                    TyKind::Slice(e) => (e, None),
                    _ => (ERROR, None),
                };
                // Index and length temporaries first, and the
                // reference middle's subslice next: a `LenOf`
                // read between two mutable element borrows of
                // the same slice would read a mutably borrowed
                // place (the bindings are disjoint by the
                // pattern's own length test).
                let suffix_idx: Vec<Local> = suffix
                    .iter()
                    .enumerate()
                    .map(|(j, _)| self.slice_back_index(&place, (suffix.len() - j) as u64, arr_len, (prefix.len() + suffix.len()) as u64, span))
                    .collect();
                enum MidPlan {
                    OwnedArray(u64),
                    Ref(Local),
                }
                let mid_plan = match middle {
                    Some(mid) if matches!(p.ast.pat(*mid), Pat::Binding { .. } | Pat::At { .. }) => {
                        let mid_ty = self.ck.pat_ty(*mid);
                        match (arr_len, self.kind(mid_ty)) {
                            (Some(n), TyKind::Array(..)) => Some(MidPlan::OwnedArray(n)),
                            _ => {
                                let mode = match self.ck.pat_res(*mid) {
                                    PatRes::Binding { mode, .. } => mode,
                                    _ => BindMode::Move,
                                };
                                let mutable = mode == BindMode::Ref(true);
                                Some(MidPlan::Ref(self.subslice_temp(&place, prefix.len(), suffix.len(), arr_len, elem, mutable, span)))
                            }
                        }
                    }
                    _ => None,
                };
                for (i, &sub) in prefix.iter().enumerate() {
                    let idx = self.pat_front_index(i as u64, (prefix.len() + suffix.len()) as u64, span);
                    self.bind_pat(sub, place.project(Proj::Index(idx)));
                }
                for (j, &sub) in suffix.iter().enumerate() {
                    self.bind_pat(sub, place.project(Proj::Index(suffix_idx[j])));
                }
                if let (Some(mid), Some(plan)) = (middle, mid_plan) {
                    match plan {
                        MidPlan::OwnedArray(n) => {
                            // An owned middle of an array is a smaller array
                            // built from the element places.
                            let mid_ty = self.ck.pat_ty(*mid);
                            let mut ops = Vec::new();
                            for i in prefix.len() as u64..(n - suffix.len() as u64) {
                                let idx = self.const_usize(i, span);
                                ops.push(self.operand_from(place.project(Proj::Index(idx)), elem));
                            }
                            let t = self.temp(mid_ty);
                            self.assign(Place::local(t), Rvalue::ArrayAgg(mid_ty, ops), span);
                            self.bind_pat(*mid, Place::local(t));
                        }
                        MidPlan::Ref(t) => self.bind_pat(*mid, Place::local(t)),
                    }
                }
            }
            (Pat::Ref { inner, .. }, _) => self.bind_pat(*inner, place.deref()),
            (Pat::At { inner, .. }, PatRes::Binding { local, mode }) => {
                self.check_at_conflicts(pat, *inner, mode);
                // Subpattern bindings first: copying Copy fields out leaves the
                // whole value movable for the `@` binding, as in Rust. A
                // moving subpattern then makes the whole move an error.
                self.bind_pat(*inner, place.clone());
                let value_ty = self.ck.pat_ty(pat);
                self.bind_one(local, mode, place, value_ty, span);
            }
            (Pat::Or(alts), _) => {
                // Bind the alternative that matched (see
                // `bind_pat_guard` for the same three shapes).
                if !self.pat_has_binding(pat) || alts.is_empty() {
                    return;
                }
                if let Some(i) = self.or_forced(pat) {
                    self.bind_pat(alts[i], place);
                    return;
                }
                let alts = alts.clone();
                match self.or_tags.iter().find(|&&(q, _)| q == pat).map(|&(_, l)| l) {
                    Some(tag) => {
                        let end = self.new_block();
                        // The otherwise edge cannot run (a test
                        // set the tag), and must not look like a
                        // path where the bindings stay unassigned.
                        let bad = self.new_block();
                        self.body.blocks[bad.0 as usize].term = Terminator::Unreachable;
                        let branches: Vec<(u32, Bb)> = (0..alts.len()).map(|i| (i as u32, self.new_block())).collect();
                        let b = &mut self.body.blocks[self.cur.0 as usize];
                        b.term = Terminator::Switch(Operand::Copy(Place::local(tag)), branches.clone(), bad);
                        b.term_span = span;
                        for (i, &(_, bb)) in branches.iter().enumerate() {
                            self.cur = bb;
                            self.bind_pat(alts[i], place.clone());
                            self.goto(end, span);
                        }
                        self.cur = end;
                    }
                    None => {
                        // No test ran before this bind (a plain
                        // `let`, a parameter, a loop binding):
                        // the pattern cannot fail there, so find
                        // the matching alternative now.
                        let end = self.new_block();
                        for &alt in &alts {
                            let next = self.new_block();
                            self.test_pat(alt, place.clone(), next);
                            self.bind_pat(alt, place.clone());
                            self.goto(end, span);
                            self.cur = next;
                        }
                        self.terminate(Terminator::Unreachable, span);
                        self.cur = end;
                    }
                }
            }
            _ => {}
        }
    }

    // ---------- Macros ----------

    /// Format pieces as IR parts. A literal argument rustc inlines into
    /// the format string (`inline_literal`) becomes literal text, merged
    /// with its neighbours, so `format!` capacity and the panic payload
    /// kind match rustc's (W-STD-B).
    /// rustc's `flatten_format_args`: a `format_args!` argument (under
    /// any `&`) that one Display or Debug placeholder uses, and no other
    /// placeholder, is spliced into the outer format. Its pieces replace
    /// the placeholder and its arguments take the outer argument's
    /// place, so the evaluation order stays. An `Arguments` writes the
    /// same text either way; the flattened form changes
    /// `estimated_capacity`, which literals inline, and whether a
    /// `format_args!` value is `'static`, as in rustc. None when
    /// nothing flattens.
    fn flatten_fmt(&self, args: &[ExprId], fmt: &[FmtPiece]) -> Option<(Vec<ExprId>, Vec<FmtPiece>)> {
        let (mut args, mut fmt) = (args.to_vec(), fmt.to_vec());
        let mut changed = false;
        let mut i = 0;
        while i < fmt.len() {
            let FmtPiece::Arg { index, spec, .. } = &fmt[i] else {
                i += 1;
                continue;
            };
            let (index, kind) = (*index, spec.kind);
            let mut a = args[index];
            while let Expr::Ref { raw: false, expr, .. } = self.p.ast.expr(a) {
                a = *expr;
            }
            let once = fmt.iter().enumerate().all(|(j, p)| j == i || !matches!(p, FmtPiece::Arg { index: k, .. } if *k == index));
            let Expr::Macro { kind: MacroKind::FormatArgs, args: inner_args, fmt: inner_fmt, .. } = self.p.ast.expr(a) else {
                i += 1;
                continue;
            };
            if !once || !matches!(kind, FmtKind::Display | FmtKind::Debug) {
                i += 1;
                continue;
            }
            // Outer argument `index` becomes the inner arguments: later
            // outer indices move by their count less one.
            let n = inner_args.len();
            let outer = |k: u32| if k as usize > index { (k as usize + n - 1) as u32 } else { k };
            for p in fmt.iter_mut() {
                if let FmtPiece::Arg { index: k, spec, .. } = p {
                    *k = outer(*k as u32) as usize;
                    spec.width_arg = spec.width_arg.map(outer);
                    spec.precision_arg = spec.precision_arg.map(outer);
                }
            }
            let inner: Vec<FmtPiece> = inner_fmt
                .iter()
                .cloned()
                .map(|mut p| {
                    if let FmtPiece::Arg { index: k, spec, .. } = &mut p {
                        *k += index;
                        spec.width_arg = spec.width_arg.map(|c| c + index as u32);
                        spec.precision_arg = spec.precision_arg.map(|c| c + index as u32);
                    }
                    p
                })
                .collect();
            args.splice(index..index + 1, inner_args.iter().copied());
            fmt.splice(i..i + 1, inner);
            changed = true;
        }
        changed.then_some((args, fmt))
    }

    /// True when an `assert!`'s message is `ASSERT_TEXT_UNKNOWN`: the format
    /// string itself (the parser's form) or its one `{}` argument (the
    /// expander's form).
    fn assert_text_unknown(&self, args: &[ExprId], fmt: &[FmtPiece]) -> bool {
        let marker = crate::expand::builtin::ASSERT_TEXT_UNKNOWN;
        fmt.iter().any(|f| matches!(f, FmtPiece::Lit(s) if s == marker))
            || args.iter().skip(1).any(|&a| matches!(self.p.ast.expr(a), Expr::Str(i) if self.p.ast.strings[*i as usize] == marker))
    }

    fn fmt_parts(&mut self, args: &[ExprId], fmt: &[FmtPiece]) -> Vec<FmtPart> {
        let flat = self.flatten_fmt(args, fmt);
        let (args, fmt) = flat.as_ref().map_or((args, fmt), |(a, f)| (&a[..], &f[..]));
        let mut parts: Vec<FmtPart> = Vec::with_capacity(fmt.len());
        let push_lit = |parts: &mut Vec<FmtPart>, text: &str| match parts.last_mut() {
            Some(FmtPart::Lit(prev)) => prev.push_str(text),
            _ => parts.push(FmtPart::Lit(text.to_string())),
        };
        // As in rustc, each argument the pieces use is evaluated once, in
        // argument order, before any of it is formatted; a literal rustc
        // inlines needs no evaluation.
        let inlined = |this: &Self, index: usize, spec: &FmtSpec| -> Option<String> {
            if *spec == FmtSpec::default() { this.inline_literal(args[index]) } else { None }
        };
        let mut wanted: Vec<usize> = Vec::new();
        for piece in fmt {
            if let FmtPiece::Arg { index, spec, .. } = piece {
                if inlined(self, *index, spec).is_none() {
                    wanted.push(*index);
                }
                wanted.extend([spec.width_arg, spec.precision_arg].into_iter().flatten().map(|c| c as usize));
            }
        }
        wanted.sort_unstable();
        wanted.dedup();
        let mut borrowed: crate::intern::FxMap<usize, (Operand, Ty)> = Default::default();
        for i in wanted {
            let b = self.borrow_of(args[i], 0);
            borrowed.insert(i, b);
        }
        for piece in fmt {
            match piece {
                FmtPiece::Lit(s) => push_lit(&mut parts, s),
                FmtPiece::Arg { index, debug, spec } => {
                    if let Some(text) = inlined(self, *index, spec) {
                        push_lit(&mut parts, &text);
                        continue;
                    }
                    let (value, ty) = borrowed[index].clone();
                    let count = |c: Option<u32>| c.map(|c| borrowed[&(c as usize)].0.clone());
                    let (width, prec) = (count(spec.width_arg), count(spec.precision_arg));
                    // A range's Debug, part by part (lower/range_fmt.rs).
                    if *debug
                        && let Some(rparts) = self.range_debug_parts(&value, ty, *spec, width.clone(), prec.clone())
                    {
                        for part in rparts {
                            match part {
                                FmtPart::Lit(s) => push_lit(&mut parts, &s),
                                other => parts.push(other),
                            }
                        }
                        continue;
                    }
                    parts.push(FmtPart::Arg { value, ty, debug: *debug, spec: *spec, width, prec });
                }
            }
        }
        parts
    }

    /// `Some(to_stderr)` when `t` peels through references and smart
    /// pointers to one of std's stream types (`Stdout`, `StdoutLock`,
    /// `Stderr`, `StderrLock`): the writers whose `write_fmt` streams
    /// its parts (see `method_into`).
    fn stream_kind(&self, mut t: Ty) -> Option<bool> {
        loop {
            if let TyKind::Ref(_, _, inner) = self.kind(t) {
                t = inner;
            } else if let Some(inner) = self.body.tys.smart_elem(t) {
                t = inner;
            } else {
                break;
            }
        }
        let a = self.body.tys.local_adt(t)?;
        if self.p.shipped_crate_at(self.p.adt(a).span) != Some(crate::ty::lang::ShippedCrate::Std) {
            return None;
        }
        match self.p.display_path(self.p.adt(a).name).as_str() {
            "std::io::Stdout" | "std::io::StdoutLock" => Some(false),
            "std::io::Stderr" | "std::io::StderrLock" => Some(true),
            _ => None,
        }
    }

    /// `dst.write_fmt(format_args!(..))` (W-STD-B): a two-phase `&mut`
    /// of the receiver around the borrows of the format arguments, then
    /// one `WriteFmt` rvalue. An argument that borrows the receiver again
    /// is live at the activation, so borrowck rejects it as rustc does.
    #[allow(clippy::too_many_arguments)]
    fn write_fmt_into(
        &mut self,
        e: ExprId,
        recv: ExprId,
        args: &[ExprId],
        derefs: u8,
        dest: Option<&Place>,
        span: Span,
        stream: Option<bool>,
    ) {
        let recv_ty = self.peel(self.ty(recv), derefs);
        let pl = self.place_for_mut(recv);
        let pl = Self::derefs(pl, derefs);
        let st = self.ref_ty(false, recv_ty);
        let reserve = self.temp(st);
        self.assign(Place::local(reserve), Rvalue::Ref(false, pl.clone()), span);
        let parts = match args.first().map(|&a| self.p.ast.expr(a)) {
            Some(Expr::Macro { args: fa, fmt, .. }) => self.fmt_parts(fa, fmt),
            _ => Vec::new(),
        };
        self.push(StmtKind::FakeRead(reserve), span);
        let mt = self.ref_ty(true, recv_ty);
        let t = self.temp(mt);
        self.assign(Place::local(t), Rvalue::Ref(true, pl), span);
        let ty = self.ty(e);
        self.set_or_temp(dest, Rvalue::WriteFmt(Operand::Move(Place::local(t)), parts, stream), ty, span);
    }

    /// The text rustc's `format_args!` lowering inlines for a `{}`
    /// argument (`inline_literals`): a string literal, or an integer
    /// literal in range of its type (unsuffixed is `i32`), under any
    /// number of `&`. Other literals (char, bool, float, negative) stay
    /// arguments, as in rustc.
    fn inline_literal(&self, mut e: ExprId) -> Option<String> {
        use crate::lexer::IntSuffix as S;
        while let Expr::Ref { raw: false, expr, .. } = self.p.ast.expr(e) {
            e = *expr;
        }
        match self.p.ast.expr(e) {
            Expr::Str(i) => self.p.ast.strings.get(*i as usize).cloned(),
            Expr::Int(v, suffix) => {
                let max: u128 = match suffix {
                    None | Some(S::I32) => i32::MAX as u128,
                    Some(S::I8) => i8::MAX as u128,
                    Some(S::I16) => i16::MAX as u128,
                    Some(S::I64 | S::Isize) => i64::MAX as u128,
                    Some(S::I128) => i128::MAX as u128,
                    Some(S::U8) => u8::MAX as u128,
                    Some(S::U16) => u16::MAX as u128,
                    Some(S::U32) => u32::MAX as u128,
                    Some(S::U64 | S::Usize) => u64::MAX as u128,
                    Some(S::U128) => u128::MAX,
                };
                (*v <= max).then(|| v.to_string())
            }
            _ => None,
        }
    }

    /// `format_args!` as an `fmt::Arguments` value (R9). The arguments
    /// are evaluated and borrowed here, as in rustc; their references
    /// go into one tuple temporary, rustc's args array, in the scope
    /// rustc gives that array: the innermost one, or the enclosing
    /// block's when a `let` extends the expression (`mark_extending`).
    /// The value borrows the temporary, so borrowck keeps it inside
    /// that scope, and its parts read the references from the
    /// temporary's fields. cgen formats the parts each time the value
    /// is formatted. With no argument left after literal inlining the
    /// value is `'static` text and borrows nothing.
    fn format_args_into(&mut self, e: ExprId, args: &[ExprId], fmt: &[FmtPiece], dest: Option<&Place>, ty: Ty, span: Span) {
        let mut parts = self.fmt_parts(args, fmt);
        // Each distinct argument reference (`fmt_parts` borrows each
        // used argument once, into a local) is one field.
        let mut refs: Vec<Local> = Vec::new();
        let mut field = |o: &mut Operand| {
            let (Operand::Copy(pl) | Operand::Move(pl)) = o else { unreachable!("fmt_parts borrows each argument into a local") };
            let i = refs.iter().position(|&l| l == pl.local).unwrap_or_else(|| {
                refs.push(pl.local);
                refs.len() - 1
            });
            i as u32
        };
        let mut fields: Vec<u32> = Vec::new();
        for part in &mut parts {
            if let FmtPart::Arg { value, width, prec, .. } = part {
                fields.push(field(value));
                fields.extend(width.iter_mut().chain(prec.iter_mut()).map(&mut field));
            }
        }
        if refs.is_empty() {
            self.set_or_temp(dest, Rvalue::FormatArgs(None, parts), ty, span);
            return;
        }
        let ref_tys: Vec<Ty> = refs.iter().map(|&l| self.body.locals[l as usize].ty).collect();
        let env_ty = {
            let ts = self.body.tys.intern_tys(&ref_tys);
            self.body.tys.intern(TyKind::Tuple(ts))
        };
        let refs = refs.into_iter().map(|l| Operand::Copy(Place::local(l))).collect();
        let env = self.new_local(env_ty, true, None);
        self.assign(Place::local(env), Rvalue::TupleAgg(env_ty, refs), span);
        self.push_extended(e, env);
        let rt = self.ref_ty(false, env_ty);
        let r = self.temp(rt);
        self.assign(Place::local(r), Rvalue::Ref(false, Place::local(env)), span);
        let mut fields = fields.into_iter();
        let mut read = |o: &mut Operand| *o = Operand::Copy(Place { local: env, proj: vec![Proj::Field(fields.next().unwrap())] });
        for part in &mut parts {
            if let FmtPart::Arg { value, width, prec, .. } = part {
                read(value);
                width.iter_mut().chain(prec.iter_mut()).for_each(&mut read);
            }
        }
        self.set_or_temp(dest, Rvalue::FormatArgs(Some(Operand::Copy(Place::local(r))), parts), ty, span);
    }

    #[allow(clippy::too_many_arguments)]
    fn macro_into(
        &mut self,
        e: ExprId,
        kind: MacroKind,
        args: &[ExprId],
        fmt: &[FmtPiece],
        repeat: bool,
        dest: Option<&Place>,
        ty: Ty,
        span: Span,
    ) {
        match kind {
            MacroKind::Println | MacroKind::Print | MacroKind::Eprintln | MacroKind::Eprint => {
                let parts = self.fmt_parts(args, fmt);
                let stderr = matches!(kind, MacroKind::Eprintln | MacroKind::Eprint);
                let newline = matches!(kind, MacroKind::Println | MacroKind::Eprintln);
                self.push(StmtKind::Print { stderr, newline, parts }, span);
                self.unit(dest, span);
            }
            MacroKind::Format => {
                let parts = self.fmt_parts(args, fmt);
                self.set_or_temp(dest, Rvalue::Format(parts), STRING, span);
            }
            MacroKind::Panic => {
                let mut parts = self.fmt_parts(args, fmt);
                if parts.is_empty() {
                    parts.push(FmtPart::Lit("explicit panic".into()));
                }
                self.terminate(Terminator::Panic(parts), span);
            }
            MacroKind::Todo => {
                let parts = self.prefixed_parts("not yet implemented", args, fmt);
                self.terminate(Terminator::Panic(parts), span)
            }
            // As a `write_fmt` argument on a Formatter, a String, or a
            // std stream it lowers in `write_fmt_into`; anywhere else it
            // is an `Arguments` value.
            MacroKind::FormatArgs => self.format_args_into(e, args, fmt, dest, ty, span),
            MacroKind::Unreachable => {
                let parts = self.prefixed_parts("internal error: entered unreachable code", args, fmt);
                self.terminate(Terminator::Panic(parts), span)
            }
            MacroKind::Vec => {
                let elem = self.peel_vec(ty);
                let rv = if repeat {
                    let x = self.operand(args[0]);
                    let n = self.operand(args[1]);
                    Rvalue::VecRepeat(elem, x, n)
                } else {
                    let ops = self.ordered_operands(args);
                    Rvalue::VecLit(elem, ops)
                };
                self.set_or_temp(dest, rv, ty, span);
            }
            MacroKind::Assert => {
                // A no-message assert whose text lust cannot print as rustc
                // does (expand/builtin.rs ASSERT_TEXT_UNKNOWN): a const
                // context never prints it (a body only borrowck reads,
                // `check_only`), runtime code would.
                if !self.check_only() && self.assert_text_unknown(args, fmt) {
                    self.body.lower_errs.push(crate::expand::builtin::assert_text_too_long(span));
                }
                let c = self.operand(args[0]);
                let (ok, fail) = (self.new_block(), self.new_block());
                let b = &mut self.body.blocks[self.cur.0 as usize];
                b.term = Terminator::If(c, ok, fail);
                b.term_span = span;
                self.cur = fail;
                let mut parts = self.fmt_parts(args, fmt);
                if parts.is_empty() {
                    parts.push(FmtPart::Lit("assertion failed".into()));
                }
                self.terminate(Terminator::Panic(parts), span);
                self.cur = ok;
                self.unit(dest, span);
            }
            MacroKind::AssertEq | MacroKind::AssertNe => {
                let ne = kind == MacroKind::AssertNe;
                let (a, t) = self.borrow_of(args[0], 0);
                let (b, tb) = self.borrow_of(args[1], 0);
                let c = self.temp(BOOL);
                let cmp = match self.ck.res(e) {
                    Res::Bin { ld, rd } => {
                        // The operands are already borrowed (`a`, `b`): view
                        // them in place, so each is evaluated once.
                        let place_of = |o: &Operand| match o {
                            Operand::Copy(p) | Operand::Move(p) => p.clone().deref(),
                            _ => unreachable!("borrow_of gives a place operand"),
                        };
                        let (pa, pb) = (place_of(&a), place_of(&b));
                        let (x, y) = (self.str_view_at(pa, t, ld, span), self.str_view_at(pb, tb, rd, span));
                        Rvalue::StrCmp(if ne { BinOp::Ne } else { BinOp::Eq }, x, y)
                    }
                    _ => Rvalue::Eq { a: a.clone(), b: b.clone(), ty: t, ne },
                };
                self.assign(Place::local(c), cmp, span);
                let (ok, fail) = (self.new_block(), self.new_block());
                let blk = &mut self.body.blocks[self.cur.0 as usize];
                blk.term = Terminator::If(Operand::Copy(Place::local(c)), ok, fail);
                blk.term_span = span;
                self.cur = fail;
                let opname = if ne { "!=" } else { "==" };
                let mut parts = vec![FmtPart::Lit(format!("assertion `left {opname} right` failed"))];
                let msg = self.fmt_parts(args, fmt);
                if !msg.is_empty() {
                    parts.push(FmtPart::Lit(": ".into()));
                    parts.extend(msg);
                }
                parts.push(FmtPart::Lit("\n  left: ".into()));
                let dbg = FmtSpec { kind: FmtKind::Debug, ..FmtSpec::default() };
                parts.push(FmtPart::Arg { value: a, ty: t, debug: true, spec: dbg, width: None, prec: None });
                parts.push(FmtPart::Lit("\n right: ".into()));
                parts.push(FmtPart::Arg { value: b, ty: tb, debug: true, spec: dbg, width: None, prec: None });
                self.terminate(Terminator::Panic(parts), span);
                self.cur = ok;
                self.unit(dest, span);
            }
        }
    }

    /// A panic message as rustc's `todo!` and `unreachable!` build it:
    /// `base`, then `: ` and the caller's format string when given.
    fn prefixed_parts(&mut self, base: &str, args: &[ExprId], fmt: &[FmtPiece]) -> Vec<FmtPart> {
        let msg = self.fmt_parts(args, fmt);
        let mut parts = vec![FmtPart::Lit(if msg.is_empty() { base.to_string() } else { format!("{base}: ") })];
        parts.extend(msg);
        parts
    }

    /// An operand for a const value, building aggregates in a temporary.
    fn const_operand(&mut self, v: &crate::ty::consteval::ConstValue, ty: Ty, span: Span) -> Operand {
        use crate::ty::consteval::ConstValue as CV;
        // A `Cell::new(v)` const is its value's (the same C form).
        if let Some(inner) = self.body.tys.cell_elem(ty) {
            return self.const_operand(v, inner, span);
        }
        match v {
            CV::Int(i) if !self.body.tys.is_exit_code(ty) => {
                let it = match self.kind(ty) {
                    TyKind::Int(it) => it,
                    _ => IntTy::I32,
                };
                Operand::Const(Const::Int(*i as u128, it))
            }
            CV::Float(bits, f) => Operand::Const(Const::Float(*bits, *f)),
            CV::Bool(b) => Operand::Const(Const::Bool(*b)),
            CV::Char(c) => Operand::Const(Const::Char(*c)),
            CV::Str(i) => Operand::Const(Const::Str(*i)),
            CV::StrBytes(b) => Operand::Const(Const::StrBytes(b.clone())),
            CV::Bytes(b) if matches!(self.kind(ty), TyKind::Array(..)) => Operand::Const(Const::Bytes(b.clone())),
            CV::Unit => Operand::Const(Const::Unit),
            _ => {
                let t = self.temp(ty);
                self.const_into(v, ty, &Place::local(t), span);
                self.operand_from(Place::local(t), ty)
            }
        }
    }

    /// Stores a const value into a place, building it from its parts.
    /// Stores into `dest` (of reference type `ty`) the address of the
    /// place at `path` inside static `idx` (a `StaticRef` or `StaticPlace`
    /// const value), reached from the static's address at run time. A
    /// slice reference type takes the fat value of the array place.
    fn static_place_into(&mut self, idx: u32, path: &[crate::ty::consteval::StaticStep], ty: Ty, dest: &Place, span: Span) {
        use crate::ty::consteval::StaticStep;
        let mut cur = self.p.statics[idx as usize].ty;
        let wants_slice = matches!(self.kind(ty), TyKind::Ref(_, _, inner) if matches!(self.kind(inner), TyKind::Slice(_)));
        if path.is_empty() && !(wants_slice && matches!(self.kind(cur), TyKind::Array(..))) {
            self.assign(dest.clone(), Rvalue::StaticRef(idx), span);
            return;
        }
        let rt = self.ref_ty(false, cur);
        let t = self.temp(rt);
        self.assign(Place::local(t), Rvalue::StaticRef(idx), span);
        let mut place = Place::local(t).deref();
        for step in path {
            cur = match (step, self.kind(cur)) {
                (StaticStep::Field(i), TyKind::Tuple(ts)) => {
                    place = place.project(Proj::Field(*i));
                    self.body.tys.tys_of(ts)[*i as usize]
                }
                (StaticStep::Field(i), _) => {
                    let a = self.body.tys.local_adt(cur).expect("internal: a static place field of a non-struct");
                    place = place.project(Proj::Field(*i));
                    self.p.adt(a).variants[0].fields[*i as usize].ty
                }
                (StaticStep::Elem(i), TyKind::Array(el, _) | TyKind::Slice(el)) => {
                    let il = self.temp(USIZE);
                    self.assign(Place::local(il), Rvalue::Use(Operand::Const(Const::Int(u128::from(*i), IntTy::Usize))), span);
                    self.mark_index_loc(il, span);
                    place = place.project(Proj::Index(il));
                    el
                }
                (StaticStep::Deref, TyKind::Ref(_, _, inner)) => {
                    place = place.deref();
                    inner
                }
                _ => panic!("internal: a static place step {step:?} on a type without it"),
            };
        }
        if wants_slice && matches!(self.kind(cur), TyKind::Array(..) | TyKind::Slice(_)) {
            self.assign(dest.clone(), Rvalue::SliceOf(place), span);
        } else {
            self.assign(dest.clone(), Rvalue::Ref(false, place), span);
        }
    }

    fn const_into(&mut self, v: &crate::ty::consteval::ConstValue, ty: Ty, dest: &Place, span: Span) {
        use crate::ty::consteval::ConstValue as CV;
        if let Some(inner) = self.body.tys.cell_elem(ty) {
            return self.const_into(v, inner, dest, span);
        }
        // `ExitCode::SUCCESS` and `FAILURE` build through `ExitCode::from`.
        if let CV::Int(i) = v
            && self.body.tys.is_exit_code(ty)
        {
            let status = Operand::Const(Const::Int(*i as u128, IntTy::U8));
            self.call_into(CallTarget::Builtin(Builtin::ExitCodeFrom), vec![status], dest.clone(), span);
            return;
        }
        // An array const value at a slice reference type goes through a
        // temporary array and a SliceOf, like the coercion path.
        if let TyKind::Ref(_, _, inner) = self.kind(ty)
            && let TyKind::Slice(elem) = self.kind(inner)
            && matches!(v, CV::Aggregate(_) | CV::Repeat(..) | CV::Bytes(_))
        {
            let n = match v {
                CV::Aggregate(vals) => vals.len() as u128,
                CV::Repeat(_, n) => *n as u128,
                CV::Bytes(b) => b.len() as u128,
                _ => unreachable!(),
            };
            let c = self.body.tys.intern_const(ConstKind::Int(n));
            let at = self.body.tys.intern(TyKind::Array(elem, c));
            // The backing array is promoted with the reference:
            // never dropped, even for a drop element type.
            let t = self.promoted_temp(at);
            self.const_into(v, at, &Place::local(t), span);
            self.assign(dest.clone(), Rvalue::SliceOf(Place::local(t)), span);
            return;
        }
        match v {
            CV::Aggregate(vals) => match self.kind(ty) {
                TyKind::Tuple(ts) => {
                    let tys: Vec<Ty> = self.body.tys.tys_of(ts).to_vec();
                    let ops: Vec<Operand> =
                        vals.iter().enumerate().map(|(i, x)| self.const_operand(x, tys.get(i).copied().unwrap_or(ERROR), span)).collect();
                    self.assign(dest.clone(), Rvalue::TupleAgg(ty, ops), span);
                }
                TyKind::Array(elem, _) => {
                    let ops: Vec<Operand> = vals.iter().map(|x| self.const_operand(x, elem, span)).collect();
                    self.assign(dest.clone(), Rvalue::ArrayAgg(ty, ops), span);
                }
                _ => match self.body.tys.local_adt(ty) {
                    Some(a) => {
                        let ops: Vec<Operand> = vals
                            .iter()
                            .enumerate()
                            .map(|(i, x)| self.const_operand(x, self.p.adt(a).variants[0].fields[i].ty, span))
                            .collect();
                        self.assign(dest.clone(), Rvalue::Aggregate(a, 0, ops), span);
                    }
                    None => self.const_builtin_aggregate(vals, ty, dest, span),
                },
            },
            CV::Variant(variant, vals) => {
                if let Some(elem) = self.body.tys.option_elem(ty) {
                    let op = if *variant == 1 && !vals.is_empty() { Some(self.const_operand(&vals[0], elem, span)) } else { None };
                    self.assign(dest.clone(), Rvalue::Opt(ty, op), span);
                } else if let Some((ok_t, err_t)) = self.body.tys.result_args(ty) {
                    if !vals.is_empty() {
                        let is_ok = *variant == 0;
                        let op = self.const_operand(&vals[0], if is_ok { ok_t } else { err_t }, span);
                        self.assign(dest.clone(), Rvalue::Res(ty, is_ok, op), span);
                    }
                } else if let Some(a) = self.body.tys.local_adt(ty) {
                    let ops: Vec<Operand> = vals
                        .iter()
                        .enumerate()
                        .map(|(i, x)| self.const_operand(x, self.p.adt(a).variants[*variant as usize].fields[i].ty, span))
                        .collect();
                    self.assign(dest.clone(), Rvalue::Aggregate(a, *variant, ops), span);
                }
            }
            CV::Repeat(x, n) => {
                let elem = match self.kind(ty) {
                    TyKind::Array(el, _) => el,
                    _ => ERROR,
                };
                if *n > 1 && is_copy(self.p, &self.body.tys, elem) && matches!(**x, CV::Int(_) | CV::Bool(_) | CV::Char(_)) {
                    let op = self.const_operand(x, elem, span);
                    self.assign(dest.clone(), Rvalue::ArrayRepeat(ty, op, *n), span);
                } else {
                    let ops: Vec<Operand> = (0..*n).map(|_| self.const_operand(x, elem, span)).collect();
                    self.assign(dest.clone(), Rvalue::ArrayAgg(ty, ops), span);
                }
            }
            CV::Ref(inner) => {
                let inner_ty = match self.kind(ty) {
                    TyKind::Ref(_, _, it) => it,
                    _ => ERROR,
                };
                // A const reference's pointee is promoted: never
                // dropped, even for a drop type.
                let t = self.promoted_temp(inner_ty);
                self.const_into(inner, inner_ty, &Place::local(t), span);
                let mutable = matches!(self.kind(ty), TyKind::Ref(_, Mut::Mut, _));
                self.assign(dest.clone(), Rvalue::Ref(mutable, Place::local(t)), span);
            }
            CV::StaticRef(idx) => self.static_place_into(*idx, &[], ty, dest, span),
            CV::StaticPlace(idx, path) => self.static_place_into(*idx, path, ty, dest, span),
            // A fn pointer in a const value (W-STD-C): the slot trampoline.
            CV::FnPtr(f) => self.assign(dest.clone(), Rvalue::FnValue(LocalDefId(*f), ty), span),
            CV::ClosureFn(h, o) => {
                let f = self.p.value_closure_fn(*h, *o).expect("internal: a const closure with no body fn");
                self.assign(dest.clone(), Rvalue::FnValue(f, ty), span)
            }
            _ => {
                let op = self.const_operand(v, ty, span);
                self.assign(dest.clone(), Rvalue::Use(op), span);
            }
        }
    }

    /// A const aggregate of a builtin type, built by the same call
    /// its `::new` lowers to: the const evaluator gives
    /// `Mutex::new(v)`, `RwLock::new(v)`, `OnceLock::new()`,
    /// `Condvar::new()`, `Barrier::new(n)`, `Vec::new()`, and
    /// `String::new()` this shape (ty/consteval.rs). Any other
    /// builtin aggregate is a clean reject, never a recursion back
    /// into `const_operand`.
    fn const_builtin_aggregate(&mut self, vals: &[crate::ty::consteval::ConstValue], ty: Ty, dest: &Place, span: Span) {
        use crate::check::sync::SyncOp;
        use crate::ty::sync::SyncTy;
        let sync = |this: &mut Self, op: SyncOp, args: Vec<Operand>| {
            this.call_into(CallTarget::Builtin(Builtin::Sync(op)), args, dest.clone(), span);
        };
        match self.body.tys.builtin_of(ty) {
            Some(BuiltinTy::Sync(k)) if k.is_lock() && vals.len() == 1 => {
                let elem = self.body.tys.adt_first_ty_arg(ty).unwrap_or(ERROR);
                let op = self.const_operand(&vals[0], elem, span);
                sync(self, SyncOp::LockNew(k), vec![op]);
            }
            Some(BuiltinTy::Sync(k @ (SyncTy::OnceLock | SyncTy::Condvar))) if vals.is_empty() => {
                sync(self, SyncOp::SyncNew(k), Vec::new());
            }
            Some(BuiltinTy::Sync(k @ SyncTy::Barrier)) if vals.len() == 1 => {
                let op = self.const_operand(&vals[0], USIZE, span);
                sync(self, SyncOp::SyncNew(k), vec![op]);
            }
            // A const range (ty/consteval.rs): its bounds, then an
            // inclusive range's `exhausted` flag, as `Expr::Range` lowers.
            Some(BuiltinTy::Iter(k)) if k.is_range() && k != crate::ty::iter::IterKind::RangeFull => {
                let elem = crate::ty::iter::iter_parts(&self.body.tys, ty).and_then(|(_, a)| a.first().copied()).unwrap_or(ERROR);
                let ops: Vec<Operand> = vals
                    .iter()
                    .map(|x| match x {
                        crate::ty::consteval::ConstValue::Bool(b) => Operand::Const(Const::Bool(*b)),
                        _ => self.const_operand(x, elem, span),
                    })
                    .collect();
                self.assign(dest.clone(), Rvalue::TupleAgg(ty, ops), span);
            }
            Some(BuiltinTy::Vec) if vals.is_empty() => {
                self.assign(dest.clone(), Rvalue::VecLit(self.peel_vec(ty), Vec::new()), span);
            }
            Some(BuiltinTy::String) if vals.is_empty() => {
                self.call_into(CallTarget::Builtin(Builtin::StringNew), Vec::new(), dest.clone(), span);
            }
            _ => {
                self.body.lower_errs.push(crate::diag::Diag::new(
                    "L0630",
                    span,
                    "this const value is outside the bounded const evaluator",
                    "Use literals, const items, and const fn calls only.",
                ));
                self.assign(dest.clone(), Rvalue::Use(Operand::Const(Const::Unit)), span);
            }
        }
    }

    /// True for the type of a trait fn value check left as a marker
    /// (check/traitpath.rs `finish_marker_value`): the trait method's
    /// own `FnDef`, zero-sized; calls through it select by the trait.
    fn is_trait_marker_value(&self, ty: Ty) -> bool {
        matches!(self.kind(ty), TyKind::FnDef(d, _) if self.p.gx.index.trait_of_method(d).is_some() || d == crate::check::generics::to_string_defs().1)
    }

    fn set_or_temp(&mut self, dest: Option<&Place>, rv: Rvalue, ty: Ty, span: Span) {
        match dest {
            Some(d) => self.assign(d.clone(), rv, span),
            None => {
                let t = self.temp(ty);
                self.assign(Place::local(t), rv, span);
            }
        }
    }

    /// An Adt value built by `e` (`set_or_temp`). Built through a `Self`
    /// path, it has the impl's own lifetimes, as in rustc (W-BORROW):
    /// it goes into a temporary whose regions equal them (a body
    /// annotation), so its fields must outlive them, and then moves on.
    fn aggregate_into(&mut self, e: ExprId, rv: Rvalue, dest: Option<&Place>, ty: Ty, span: Span) {
        match self.self_ctor_regions(e) {
            Some(r) => {
                let t = self.temp(ty);
                self.assign(Place::local(t), rv, span);
                self.body.annotations.push((t, r));
                self.set_or_temp(dest, Rvalue::Use(Operand::Move(Place::local(t))), ty, span);
            }
            None => self.set_or_temp(dest, rv, ty, span),
        }
    }

    /// The impl's regioned `Self` type when `e` builds a value through a
    /// `Self` path (`Self { .. }`, `Self(..)`, `Self::V(..)`, `Self::V`)
    /// and that type has lifetimes. Template and plain bodies only: an
    /// instance's types are concrete, and its template carries the check.
    fn self_ctor_regions(&self, e: ExprId) -> Option<Ty> {
        let p = self.p;
        let head = match p.ast.expr(e) {
            Expr::StructLit { path, .. } | Expr::Path(path) => path.first(),
            Expr::Call { callee, .. } => match p.ast.expr(*callee) {
                Expr::Path(segs) => segs.first(),
                _ => None,
            },
            _ => None,
        }?;
        let fid = self.body.fn_id;
        if head.name != p.known.self_type || self.in_instance(fid) {
            return None;
        }
        let t = p.gx.fn_scopes.get(fid.0 as usize)?.scope.self_ty_regioned?;
        let mut regs = Vec::new();
        crate::borrowck::regions_of(&self.body.tys, t, &mut regs);
        regs.iter().any(|r| matches!(r, Region::Static | Region::Param(_))).then_some(t)
    }

    /// True for a mono instance body, or a closure body fn inside one.
    fn in_instance(&self, fid: LocalDefId) -> bool {
        use crate::check::generics::FnClass;
        let p = self.p;
        match p.gx.fn_class.get(fid.0 as usize) {
            Some(FnClass::Instance) => true,
            Some(FnClass::Closure) => {
                let parent = p.gx.closure_fns.get(&fid).and_then(|d| p.gx.closures.get(d)).map(|c| c.parent);
                parent.is_some_and(|f| f != fid && self.in_instance(f))
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::def::{CrateIds, LOCAL_CRATE};
    use crate::diag::FileId;
    use crate::intern::{Interner, Known};
    use crate::{lexer, parser};

    /// A deep method chain lowers to a linear number of IR
    /// statements (the shared unwind ladder of `call_into`).
    /// Before the ladder, each call's cleanup re-emitted a drop
    /// for every local in scope, so a 400-link chain lowered to
    /// about 80000 statements (~links^2/2), which every later
    /// phase then paid for in time and memory.
    #[test]
    fn deep_chain_lowers_to_linear_ir() {
        let links = 400;
        // Lowering a deep chain recurses over the expression spine,
        // as it does on the driver's pool threads: use their stack.
        let (stmts, blocks) = std::thread::Builder::new()
            .stack_size(crate::pool::STACK_SIZE)
            .spawn(move || {
                let src = format!("fn main() {{ println!(\"{{}}\", 5i64{}); }}\n", ".abs()".repeat(links));
                let interner = std::sync::Arc::new(Interner::default());
                let known = std::sync::Arc::new(Known::new(&interner));
                let lexed = lexer::lex(&src, FileId(0), 0, &interner).unwrap();
                let ast = parser::parse(&lexed, &interner, &known).unwrap();
                let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
                let program = crate::check::collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
                let main = program.main.unwrap();
                let (ck, errs) = crate::check::check_fn(&program, main);
                assert!(errs.is_empty(), "{errs:?}");
                let body = lower(&program, main, ck);
                (body.blocks.iter().map(|b| b.stmts.len()).sum::<usize>(), body.blocks.len())
            })
            .unwrap()
            .join()
            .unwrap();
        assert!(stmts < 20 * links, "linear IR for a {links}-link chain, got {stmts} statements in {blocks} blocks");
    }
}
