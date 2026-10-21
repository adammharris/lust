// Checking of `std::panic`'s compiler-known fns (W-UNWIND, docs/ARCH.md
// sections 2.7 and 7.2): `catch_unwind`, `resume_unwind`, and
// `panic_any`, which the sync table routes here (check/sync.rs), and the
// `UnwindSafe` / `RefUnwindSafe` facts that `catch_unwind`'s bound needs.
// `AssertUnwindSafe` is std source (library/std/src/panic.rs); it is
// `FnOnce()` when its value is (`closure::fn_like_facts`), as std's impl.
//
// The two unwind-safety traits have their own fixed table below, taken
// from rustc 1.99 (`F: UnwindSafe` and `F: RefUnwindSafe` probes over the
// std types lust has): `&mut T` is not `UnwindSafe`; `&T` and `*const T`
// are `UnwindSafe` when `T: RefUnwindSafe`; the cells (`Cell`, `RefCell`,
// `OnceCell`, `LazyCell`) and their guards are not `RefUnwindSafe`; the
// locks, atomics, and `OnceLock` are both; `Rc`, `Arc`, and `sync::Weak`
// need `T: RefUnwindSafe` for both; `rc::Weak`, `JoinHandle`, and `dyn`
// types are neither. Everything else is structural. An answer that
// needs a type parameter's bounds or an unknown std type is "unknown":
// lust rejects the call (L0820) rather than guess.
use super::*;
use crate::check::sync::SyncOp;
use crate::ty::BuiltinTy as B;
use crate::ty::sync::SyncTy as S;

/// One body-end check: the closure type of a `catch_unwind` call, or the
/// payload type of a `panic_any` call.
#[derive(Clone, Copy)]
pub(super) enum UnwindCheck {
    Catch(Ty, Span),
    PanicAny(Ty, Span),
    /// The source of a coercion to `dyn Tr + UnwindSafe` (false) or
    /// `+ RefUnwindSafe` (true).
    Dyn(Ty, bool, Span),
}

impl<'p> Ctx<'p> {
    /// `Box<dyn Any + Send>`: the payload type of `catch_unwind`'s `Err`
    /// and of `resume_unwind`.
    pub(super) fn box_any_send(&mut self) -> Ty {
        let d = self.dyn_any_send();
        self.tys.mk_boxed(d)
    }

    fn dyn_any_send(&mut self) -> Ty {
        dyn_any_send(&mut self.tys, self.p.gx.lang.any)
    }

    /// The signature of a `std::panic` fn the sync table routes here.
    pub(super) fn unwind_call_sig(&mut self, op: SyncOp, span: Span) -> (Vec<Ty>, Ty) {
        let payload = self.box_any_send();
        match op {
            // `catch_unwind<F: FnOnce() -> R + UnwindSafe, R>(f: F)
            // -> Result<R, Box<dyn Any + Send>>`.
            SyncOp::CatchUnwind => {
                let ret = self.new_var(false);
                let f = self.fn_once_param(&[], ret, span);
                self.unwind_checks.push(UnwindCheck::Catch(f, span));
                (vec![f], self.tys.mk_result(ret, payload))
            }
            // `resume_unwind(payload: Box<dyn Any + Send>) -> !`.
            SyncOp::ResumeUnwind => (vec![payload], NEVER),
            // `panic_any<M: 'static + Any + Send>(msg: M) -> !`.
            SyncOp::PanicAny => {
                let m = self.new_var(false);
                self.require_send(m, span);
                self.unwind_checks.push(UnwindCheck::PanicAny(m, span));
                (vec![m], NEVER)
            }
            // The hook slot (std source only): `swap<T>(new: T) -> T`, and
            // `ref<T>() -> &'static T`, typed by the caller's annotation.
            SyncOp::PanicHookSwap => {
                let t = self.new_var(false);
                (vec![t], t)
            }
            SyncOp::PanicHookRef => {
                let t = self.new_var(false);
                (vec![], self.tys.mk_ref(false, t))
            }
            SyncOp::PanicHookPayload => {
                let d = self.dyn_any_send();
                (vec![], self.tys.mk_ref(false, d))
            }
            SyncOp::PanicHookLocation => {
                let l = self.tys.intern(TyKind::Adt(generics::location_def(), EMPTY_ARGS));
                (vec![], self.tys.mk_ref(false, l))
            }
            _ => unreachable!("not a std::panic fn: {op:?}"),
        }
    }

    /// The unwind-safety bits of a `dyn` coercion target: the source
    /// must have each, by the table at body end.
    pub(super) fn require_unwind_auto(&mut self, x: Ty, want: crate::ty::AutoTraits, span: Span) {
        if want.unwind_safe {
            self.unwind_checks.push(UnwindCheck::Dyn(x, false, span));
        }
        if want.ref_unwind_safe {
            self.unwind_checks.push(UnwindCheck::Dyn(x, true, span));
        }
    }

    /// Body end: each `catch_unwind` closure must be `UnwindSafe` (rustc
    /// E0277), and each `panic_any` payload an `Any` type, whose vtable
    /// the call needs (lowering boxes it as `Box<dyn Any + Send>`).
    pub(super) fn finish_unwind(&mut self) {
        for c in std::mem::take(&mut self.unwind_checks) {
            match c {
                UnwindCheck::Catch(f, span) => {
                    let f = self.deep(f);
                    if matches!(self.kind(f), TyKind::Error) {
                        continue;
                    }
                    let env = self.solve_env();
                    match unwind_safe(self.p, &mut self.tys, &env, false, f, &mut Vec::new()) {
                        Some(true) => {}
                        Some(false) => {
                            let tn = self.tn(f);
                            self.err(
                                "L0612",
                                span,
                                format!("no impl of `std::panic::UnwindSafe` for `{tn}`: `catch_unwind` needs it"),
                                "Wrap the closure in `std::panic::AssertUnwindSafe(..)` if a panic cannot leave its captures broken.",
                            )
                        }
                        None => {
                            let tn = self.tn(f);
                            self.err(
                                "L0820",
                                span,
                                format!("lust cannot decide whether `{tn}` is `UnwindSafe` yet"),
                                "Wrap the closure in `std::panic::AssertUnwindSafe(..)`.",
                            )
                        }
                    }
                }
                UnwindCheck::Dyn(x, refs, span) => {
                    let x = self.deep(x);
                    if matches!(self.kind(x), TyKind::Error) {
                        continue;
                    }
                    let env = self.solve_env();
                    let name = if refs { "RefUnwindSafe" } else { "UnwindSafe" };
                    match unwind_safe(self.p, &mut self.tys, &env, refs, x, &mut Vec::new()) {
                        Some(true) => {}
                        Some(false) => {
                            let tn = self.tn(x);
                            self.err(
                                "L0612",
                                span,
                                format!("no impl of `std::panic::{name}` for `{tn}`: this `dyn` type needs it"),
                                format!("Drop `{name}` from the `dyn` type, or wrap the value in `std::panic::AssertUnwindSafe(..)`."),
                            )
                        }
                        None => {
                            let tn = self.tn(x);
                            self.err("L0820", span, format!("lust cannot decide whether `{tn}` is `{name}` yet"), format!("Drop `{name}` from the `dyn` type."))
                        }
                    }
                }
                UnwindCheck::PanicAny(m, span) => {
                    let m = self.deep(m);
                    if matches!(self.kind(m), TyKind::Error) || !self.any_type_ok(m, None, false, false, span) {
                        continue;
                    }
                    let d = self.dyn_any_send();
                    self.vtable_sites.push((m, d, span));
                }
            }
        }
    }
}

/// `dyn Any + Send + 'static` (`any` is the `Any` trait's def).
pub fn dyn_any_send(tys: &mut impl TyIntern, any: DefId) -> Ty {
    let args = tys.intern_args(&[GenericArg::Ty(DYN_SELF)]);
    let tr = TraitRef { def: any, args, bindings: EMPTY_BINDINGS };
    let auto = crate::ty::AutoTraits { send: true, ..Default::default() };
    let b = tys.intern_dyn_bounds(crate::ty::DynBounds { principal: Some(Binder::plain(tr)), supertraits: Box::new([]), auto });
    tys.intern(TyKind::Dyn(b, Region::Static))
}

/// For std's `UnwindSafe` (false) and `RefUnwindSafe` (true) marker
/// traits (library/std/src/panic.rs), which bit `unwind_safe` answers;
/// None for any other trait.
pub fn unwind_trait(p: &Program, def: DefId) -> Option<bool> {
    let name = p.defs.get(def)?.name;
    if !p.interner.get(name).ends_with("UnwindSafe") {
        return None;
    }
    match p.display_path(name).as_str() {
        "std::panic::UnwindSafe" => Some(false),
        "std::panic::RefUnwindSafe" => Some(true),
        _ => None,
    }
}

/// True for std's `AssertUnwindSafe` (library/std/src/panic.rs).
pub fn is_assert_unwind_safe(p: &Program, a: crate::ty::AdtId) -> bool {
    p.is_std_adt(a) && p.display_path(p.adt(a).name) == "std::panic::AssertUnwindSafe"
}

/// `T: UnwindSafe` (`refs` false) or `T: RefUnwindSafe` (`refs` true) by
/// the table in the header. None when lust cannot tell.
pub fn unwind_safe(p: &Program, tys: &mut impl TyIntern, env: &[Predicate], refs: bool, t: Ty, seen: &mut Vec<(bool, Ty)>) -> Option<bool> {
    if seen.contains(&(refs, t)) {
        return Some(true);
    }
    let all = |tys: &mut _, parts: Vec<(bool, Ty)>, seen: &mut Vec<(bool, Ty)>| -> Option<bool> {
        let mut unknown = false;
        for (r, e) in parts {
            match unwind_safe(p, tys, env, r, e, seen) {
                Some(false) => return Some(false),
                None => unknown = true,
                Some(true) => {}
            }
        }
        if unknown { None } else { Some(true) }
    };
    seen.push((refs, t));
    let out = match tys.kind(t) {
        TyKind::Error => Some(true),
        TyKind::Infer(v) if v.is_int() || v.is_float() => Some(true),
        TyKind::Int(_)
        | TyKind::Float(_)
        | TyKind::Bool
        | TyKind::Char
        | TyKind::Unit
        | TyKind::Str
        | TyKind::Never
        | TyKind::FnDef(..)
        | TyKind::FnPtr(_) => Some(true),
        TyKind::Dyn(..) => {
            let a = crate::check::object::dyn_auto(p, &*tys, t);
            Some(if refs { a.ref_unwind_safe } else { a.unwind_safe })
        }
        TyKind::Ref(_, m, _) if m.is_mut() && !refs => Some(false),
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) => all(tys, vec![(true, e)], seen),
        TyKind::Slice(e) | TyKind::Array(e, _) => all(tys, vec![(refs, e)], seen),
        TyKind::Tuple(ts) => {
            let parts = tys.tys_of(ts).iter().map(|&e| (refs, e)).collect();
            all(tys, parts, seen)
        }
        TyKind::Closure(_, a) => {
            let parts = crate::check::collect::closure_fields(tys, a).into_iter().map(|e| (refs, e)).collect();
            all(tys, parts, seen)
        }
        TyKind::Opaque(od, a) => match p.gx.opaque_hidden.get(&od) {
            Some(&h) => {
                let args: Vec<GenericArg> = tys.args(a).to_vec();
                let h = subst(tys, h, &args);
                all(tys, vec![(refs, h)], seen)
            }
            None => None,
        },
        TyKind::Adt(..) => adt_unwind_safe(p, tys, env, refs, t, seen),
        // A type parameter with the bound written (`F: UnwindSafe`).
        TyKind::Param(_) => env
            .iter()
            .any(|pred| {
                matches!(pred, Predicate::Trait(b) if unwind_trait(p, b.value.def) == Some(refs)
                    && tys.args(b.value.args).first().and_then(|g| g.as_ty()) == Some(t))
            })
            .then_some(true),
        _ => None,
    };
    seen.pop();
    out
}

/// `unwind_safe` for an Adt: the std table, then structure.
fn adt_unwind_safe(p: &Program, tys: &mut impl TyIntern, env: &[Predicate], refs: bool, t: Ty, seen: &mut Vec<(bool, Ty)>) -> Option<bool> {
    let args: Vec<Ty> = tys.adt_parts(t).map(|(_, a)| tys.args(a).iter().filter_map(|g| g.as_ty()).collect()).unwrap_or_default();
    let elem = args.first().copied();
    let each = |tys: &mut _, parts: Vec<(bool, Ty)>, seen: &mut Vec<(bool, Ty)>| -> Option<bool> {
        let mut unknown = false;
        for (r, e) in parts {
            match unwind_safe(p, tys, env, r, e, seen) {
                Some(false) => return Some(false),
                None => unknown = true,
                Some(true) => {}
            }
        }
        if unknown { None } else { Some(true) }
    };
    if let Some(b) = tys.builtin_of(t) {
        return match b {
            B::String | B::Chars | B::ExitCode | B::LocalKey | B::AccessError => Some(true),
            B::Vec | B::Option | B::Boxed | B::Result | B::Hash(_) => each(tys, args.iter().map(|&e| (refs, e)).collect(), seen),
            B::Rc | B::Sync(S::Arc | S::ArcWeak) => each(tys, elem.map(|e| (true, e)).into_iter().collect(), seen),
            B::Weak | B::RefGuard | B::RefMutGuard | B::Sync(S::JoinHandle | S::ScopedJoinHandle) => Some(false),
            B::Cell | B::RefCell => {
                if refs {
                    Some(false)
                } else {
                    each(tys, elem.map(|e| (false, e)).into_iter().collect(), seen)
                }
            }
            B::Sync(
                S::Mutex
                | S::RwLock
                | S::MutexGuard
                | S::RwLockReadGuard
                | S::RwLockWriteGuard
                | S::Condvar
                | S::Barrier
                | S::BarrierWaitResult
                | S::Duration
                | S::Sender
                | S::SyncSender
                | S::Receiver,
            ) => Some(true),
            B::Sync(k) if k.atomic_value().is_some() => Some(true),
            // `UnwindSafe` when `T` is; `RefUnwindSafe` when `T` is both.
            B::Sync(S::OnceLock) => {
                let mut parts: Vec<(bool, Ty)> = elem.map(|e| (false, e)).into_iter().collect();
                if refs {
                    parts.extend(elem.map(|e| (true, e)));
                }
                each(tys, parts, seen)
            }
            B::Sync(S::PoisonError | S::SendError) => each(tys, args.iter().map(|&e| (refs, e)).collect(), seen),
            _ => None,
        };
    }
    let a = tys.local_adt(t)?;
    if is_assert_unwind_safe(p, a) {
        return Some(true);
    }
    if p.is_std_adt(a) {
        let path = p.display_path(p.adt(a).name);
        if path == "core::marker::PhantomData" {
            return each(tys, args.iter().map(|&e| (refs, e)).collect(), seen);
        }
        if path == "core::cell::OnceCell" || path == "core::cell::LazyCell" {
            return if refs { Some(false) } else { each(tys, elem.map(|e| (false, e)).into_iter().collect(), seen) };
        }
        // Other std source types: structure, as for user types below.
    }
    let gargs: Vec<GenericArg> = tys.adt_parts(t).map(|(_, a)| tys.args(a).to_vec()).unwrap_or_default();
    let raw: Vec<Ty> = p.adt(a).variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect();
    let fields: Vec<(bool, Ty)> =
        raw.into_iter().map(|f| (refs, if gargs.is_empty() || !tys.flags(f).contains_param() { f } else { subst(tys, f, &gargs) })).collect();
    each(tys, fields, seen)
}
