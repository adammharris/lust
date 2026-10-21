// Codegen for the `std::sync` and `std::thread` types (W-THREADS, ARCH
// 7.3): their C forms, layouts, glue, and the builtin calls check/sync.rs
// types. The operations call the runtime (src/runtime/sync.c), which
// holds every atomic and every OS call, so the generated code stays
// plain C that tcc and gcc compile the same way.
//
// Atomics are their value's C integer type (`uint8_t` for `AtomicBool`),
// accessed only through the runtime's `lust_at_*` functions, which take
// Rust's `atomic::Ordering` discriminant and panic on the orderings
// Rust's methods reject.
use super::*;
use crate::check::sync::SyncOp;
use crate::ty::sync::{AtomicVal, SyncTy};

/// The C type of a sync type with type argument `e`. `Arc<T>` and
/// `sync::Weak<T>` point at `Rc<T>`'s counted header (`RcI_T`).
pub(super) fn sync_ctype(k: SyncTy, e: &CTy) -> String {
    match (k, k.atomic_value()) {
        (SyncTy::Arc | SyncTy::ArcWeak, _) => format!("RcI_{}*", mangle(e)),
        // A lock is its struct (`LkM_T`/`LkR_T`); a guard points at its
        // lock; a `PoisonError<G>` is `G` itself.
        (SyncTy::Mutex | SyncTy::RwLock | SyncTy::OnceLock, _) => {
            format!("Lk{}_{}", if k == SyncTy::Mutex { "M" } else if k == SyncTy::RwLock { "R" } else { "O" }, mangle(e))
        }
        (SyncTy::Condvar, _) => "uint32_t".into(),
        (SyncTy::Duration, _) => "lust_Duration".into(),
        (SyncTy::Barrier, _) => "lust_Barrier".into(),
        (SyncTy::BarrierWaitResult, _) => "uint8_t".into(),
        (SyncTy::ThreadBuilder, _) => "lust_ThreadBuilder".into(),
        (SyncTy::MutexGuard | SyncTy::RwLockReadGuard | SyncTy::RwLockWriteGuard, _) => format!("{}*", sync_ctype(k.guard().expect("a guard").0, e)),
        (SyncTy::PoisonError | SyncTy::SendError, _) => ctype(e),
        (SyncTy::Sender | SyncTy::SyncSender | SyncTy::Receiver, _) => "lust_Chan*".into(),
        (SyncTy::JoinHandle | SyncTy::ScopedJoinHandle, _) => "lust_JoinHdr*".into(),
        (SyncTy::Scope, _) => "lust_Scope".into(),
        (SyncTy::Thread, _) => "lust_ThreadInfo*".into(),
        (SyncTy::ThreadId, _) => "uint64_t".into(),
        // Never built (a panic aborts): a zero-size stand-in.
        (SyncTy::JoinError, _) => "lust_Unit".into(),
        (_, Some(AtomicVal::Bool)) => "uint8_t".into(),
        (_, Some(AtomicVal::Int(i))) => int_c(i).into(),
        (_, None) => unreachable!("a sync type with no C form"),
    }
}

/// The state words ahead of the value in a lock or `OnceLock` struct:
/// `st` (the futex word), then `wn` (an RwLock's sleepers) and `poison`.
pub(super) fn cell_words(k: SyncTy) -> &'static [IntTy] {
    match k {
        SyncTy::Mutex => &[IntTy::U32, IntTy::U8],
        SyncTy::RwLock => &[IntTy::U32, IntTy::U32, IntTy::U8],
        _ => &[IntTy::U32],
    }
}

/// The exact Rust layout of a sync type. An atomic is its value's
/// size and alignment with no niche (`UnsafeCell`); `Arc` and
/// `sync::Weak` are a non-null pointer.
pub(super) fn sync_layout(k: SyncTy) -> Option<Layout> {
    if matches!(
        k,
        SyncTy::Arc | SyncTy::ArcWeak | SyncTy::JoinHandle | SyncTy::ScopedJoinHandle | SyncTy::Thread | SyncTy::Sender | SyncTy::SyncSender | SyncTy::Receiver
    ) || k.guard().is_some()
    {
        return Some(layout::ptr_layout());
    }
    match k {
        SyncTy::Scope | SyncTy::Condvar => return Some(plain_layout(4, 4)),
        SyncTy::Barrier => return Some(plain_layout(32, 8)),
        SyncTy::Duration => return Some(plain_layout(16, 8)),
        SyncTy::BarrierWaitResult => return Some(plain_layout(1, 1)),
        SyncTy::ThreadBuilder => return Some(plain_layout(40, 8)),
        _ => {}
    }
    if k == SyncTy::ThreadId {
        return Some(plain_layout(8, 8));
    }
    if k == SyncTy::JoinError {
        return Some(layout::zst_layout(1));
    }
    let v = k.atomic_value()?;
    let n = v.bytes() as u64;
    Some(plain_layout(n, n))
}

/// True when a value of the sync type needs drop glue.
pub(super) fn sync_needs_drop(p: &Program, k: SyncTy, e: &CTy) -> bool {
    match k {
        SyncTy::ThreadBuilder => true,
        SyncTy::Mutex | SyncTy::RwLock | SyncTy::PoisonError | SyncTy::SendError | SyncTy::OnceLock => needs_drop_c(p, e),
        _ => {
            matches!(
                k,
                SyncTy::Arc
                    | SyncTy::ArcWeak
                    | SyncTy::JoinHandle
                    | SyncTy::ScopedJoinHandle
                    | SyncTy::Thread
                    | SyncTy::Sender
                    | SyncTy::SyncSender
                    | SyncTy::Receiver
            ) || k.guard().is_some()
        }
    }
}

/// The C types a sync type's code names: `Arc` and `sync::Weak` need
/// `Rc`'s header struct for their element.
pub(super) fn sync_collect_types(k: SyncTy, e: &CTy, out: &mut HashSet<CTy>) {
    if matches!(k, SyncTy::Arc | SyncTy::ArcWeak) {
        out.insert(CTy::Rc(Box::new(e.clone())));
        collect_types(e, out);
    }
    if let Some(l) = if k.is_cell_struct() { Some(k) } else { k.guard().map(|g| g.0) } {
        out.insert(CTy::Sync(l, Box::new(e.clone())));
        collect_types(e, out);
    }
    if matches!(k, SyncTy::PoisonError | SyncTy::SendError | SyncTy::Sender | SyncTy::SyncSender | SyncTy::Receiver | SyncTy::JoinHandle | SyncTy::ScopedJoinHandle) {
        collect_types(e, out);
    }
    if k == SyncTy::ThreadBuilder {
        out.insert(CTy::String);
    }
}

/// The glue function `g` of a sync type: its prototype to `protos` and
/// its definition to `defs`. Glue a type does not have is never asked
/// for (check answers the trait as not implemented).
/// `types`: the C types a definition holds besides its own (release C units declare them).
#[allow(clippy::too_many_arguments)]
pub(super) fn sync_glue_def(
    p: &Program,
    g: Glue,
    k: SyncTy,
    e: &CTy,
    protos: &mut String,
    defs: &mut String,
    need: &mut dyn FnMut(Glue, &CTy),
    types: &mut Vec<CTy>,
) {
    let t = CTy::Sync(k, Box::new(e.clone()));
    let (m, ct) = (mangle(&t), ctype(&t));
    let it = format!("RcI_{}", mangle(e));
    let dealloc = format!("lust_rc_free(*p, _Alignof({it}))");
    // `Arc`'s value glue (Eq, Cmp, Debug, Display, Default) is `Rc`'s:
    // the same header, read the same way.
    let forward = |g: Glue, rc: &CTy, need: &mut dyn FnMut(Glue, &CTy), protos: &mut String, defs: &mut String| {
        need(g, rc);
        let rm = mangle(rc);
        let (proto, call) = match g {
            Glue::Eq => (format!("uint8_t eq_{m}({ct} *a, {ct} *b)"), format!("eq_{rm}(a, b)")),
            Glue::Cmp => (format!("int8_t cmp_{m}({ct} *a, {ct} *b)"), format!("cmp_{rm}(a, b)")),
            Glue::PCmp => (format!("int8_t pcmp_{m}({ct} *a, {ct} *b)"), format!("pcmp_{rm}(a, b)")),
            Glue::Debug => (format!("int dbg_{m}(lust_Formatter *f, {ct} *p)"), format!("dbg_{rm}(f, p)")),
            Glue::Display => (format!("int disp_{m}(lust_Formatter *f, {ct} *p)"), format!("disp_{rm}(f, p)")),
            Glue::Default => (format!("{ct} default_{m}(void)"), format!("default_{rm}()")),
            Glue::Drop | Glue::Clone => unreachable!("Arc's own drop and clone"),
            // `clonefrom` never forwards here: clonefrom.rs handles
            // every shape itself, sync types by the default body.
            Glue::CloneFrom => unreachable!("clonefrom glue is in clonefrom.rs"),
            Glue::TlsInit | Glue::TlsDtor => unreachable!("TLS glue is per thread_local! key"),
            Glue::FmtWrite => unreachable!("fmt::Write glue is a user writer's"),
            // Hash glue is keyed by (value, hasher) tuples (cgen/hash.rs
            // hashes an Arc as its value), never by an Arc itself.
            Glue::HashValue
            | Glue::HashKey
            | Glue::HashOf
            | Glue::HashEq
            | Glue::HashClone
            | Glue::HashKeyQ
            | Glue::HashEqQ
            | Glue::HashEqEntry
            | Glue::HashDrop
            | Glue::HashOne => unreachable!("hash glue of an Arc"),
        };
        let _ = writeln!(protos, "{proto};");
        let _ = writeln!(defs, "{proto} {{\n  return {call};\n}}\n");
    };
    match (g, k) {
        // The last strong ref drops the value, then gives up the implicit
        // weak ref; the last weak ref frees the header.
        (Glue::Drop, SyncTy::Arc) => {
            let inner = if needs_drop_c(p, e) {
                need(Glue::Drop, e);
                format!("drop_{}({}); ", mangle(e), super::rc_ptr("*p", e))
            } else {
                String::new()
            };
            let _ = writeln!(protos, "void drop_{m}({ct} *p);");
            let _ = writeln!(
                defs,
                "void drop_{m}({ct} *p) {{\n  if (lust_arc_dec(&(*p)->strong)) {{ {inner}if (lust_arc_dec(&(*p)->weak)) {dealloc}; }}\n}}\n"
            );
        }
        (Glue::Drop, SyncTy::ArcWeak) => {
            let _ = writeln!(protos, "void drop_{m}({ct} *p);");
            let _ = writeln!(defs, "void drop_{m}({ct} *p) {{\n  if (*p != ({it}*)~(uint64_t)0 && lust_arc_dec(&(*p)->weak)) {dealloc};\n}}\n");
        }
        (Glue::Clone, SyncTy::Arc) => {
            let _ = writeln!(protos, "{ct} clone_{m}({ct} *p);");
            let _ = writeln!(defs, "{ct} clone_{m}({ct} *p) {{\n  lust_arc_inc(&(*p)->strong); return *p;\n}}\n");
        }
        (Glue::Clone, SyncTy::ArcWeak) => {
            let _ = writeln!(protos, "{ct} clone_{m}({ct} *p);");
            let _ = writeln!(defs, "{ct} clone_{m}({ct} *p) {{\n  if (*p != ({it}*)~(uint64_t)0) lust_arc_inc(&(*p)->weak); return *p;\n}}\n");
        }
        (Glue::Debug, SyncTy::ArcWeak) => forward(g, &CTy::Weak(Box::new(e.clone())), need, protos, defs),
        // `Weak::default()` is `Weak::new()`: the dangling pointer.
        (Glue::Default, SyncTy::ArcWeak) => {
            let _ = writeln!(protos, "{ct} default_{m}(void);");
            let _ = writeln!(defs, "{ct} default_{m}(void) {{\n  return ({it}*)~(uint64_t)0;\n}}\n");
        }
        (_, SyncTy::Arc) => forward(g, &CTy::Rc(Box::new(e.clone())), need, protos, defs),
        (_, SyncTy::Mutex | SyncTy::RwLock | SyncTy::MutexGuard | SyncTy::RwLockReadGuard | SyncTy::RwLockWriteGuard | SyncTy::PoisonError) => {
            lock_glue_def(p, g, k, e, &m, &ct, protos, defs, need)
        }
        (_, SyncTy::ThreadBuilder) => builder_glue_def(p, g, &m, &ct, protos, defs, need, types),
        (_, SyncTy::JoinHandle | SyncTy::ScopedJoinHandle | SyncTy::Scope | SyncTy::Thread | SyncTy::ThreadId | SyncTy::JoinError) => {
            thread_glue_def(g, k, &m, &ct, protos, defs)
        }
        (_, SyncTy::Sender | SyncTy::SyncSender | SyncTy::Receiver | SyncTy::SendError) => chan_glue_def(p, g, k, e, &m, &ct, protos, defs, need),
        (_, SyncTy::Condvar | SyncTy::Barrier | SyncTy::BarrierWaitResult | SyncTy::OnceLock) => once_glue_def(p, g, k, e, &m, &ct, protos, defs, need),
        // `Duration`: a plain `{ secs, nanos }` value.
        (Glue::Clone, SyncTy::Duration) => {
            let _ = writeln!(protos, "{ct} clone_{m}({ct} *p);");
            let _ = writeln!(defs, "{ct} clone_{m}({ct} *p) {{\n  return *p;\n}}\n");
        }
        (Glue::Eq, SyncTy::Duration) => {
            let _ = writeln!(protos, "uint8_t eq_{m}({ct} *a, {ct} *b);");
            let _ = writeln!(defs, "uint8_t eq_{m}({ct} *a, {ct} *b) {{\n  return a->secs == b->secs && a->nanos == b->nanos;\n}}\n");
        }
        (Glue::Default, SyncTy::Duration) => {
            let _ = writeln!(protos, "{ct} default_{m}(void);");
            let _ = writeln!(defs, "{ct} default_{m}(void) {{\n  {ct} r = {{0, 0}}; return r;\n}}\n");
        }
        (Glue::Drop, SyncTy::Duration) => {
            let _ = writeln!(protos, "void drop_{m}({ct} *p);");
            let _ = writeln!(defs, "void drop_{m}({ct} *p) {{\n  (void)p;\n}}\n");
        }
        (Glue::Default, _) if k.atomic_value().is_some() => {
            let _ = writeln!(protos, "{ct} default_{m}(void);");
            let _ = writeln!(defs, "{ct} default_{m}(void) {{\n  return 0;\n}}\n");
        }
        (Glue::Drop, _) if k.atomic_value().is_some() => {
            let _ = writeln!(protos, "void drop_{m}({ct} *p);");
            let _ = writeln!(defs, "void drop_{m}({ct} *p) {{\n  (void)p;\n}}\n");
        }
        _ => unreachable!("internal: no {g:?} glue for `{}`", k.name()),
    }
}

/// Glue of `thread::Builder`: drop frees the name; Debug is
/// std's struct form over the name and stack size options.
#[allow(clippy::too_many_arguments)]
fn builder_glue_def(p: &Program, g: Glue, m: &str, ct: &str, protos: &mut String, defs: &mut String, need: &mut dyn FnMut(Glue, &CTy), types: &mut Vec<CTy>) {
    let lit = |s: &str| format!("(lust_str){{(uint8_t*)\"{s}\", {}}}", s.len());
    match g {
        Glue::Drop => {
            need(Glue::Drop, &CTy::String);
            let _ = writeln!(protos, "void drop_{m}({ct} *p);");
            let _ = writeln!(defs, "void drop_{m}({ct} *p) {{\n  if (p->has_name) drop_{}(&p->name);\n}}\n", mangle(&CTy::String));
        }
        Glue::Debug => {
            // `Builder { name: Some("x"), stack_size: None }` over
            // two Option values built from the fields (the name
            // Option only borrows the String for printing).
            let opt_str = CTy::Option(Box::new(CTy::String));
            let opt_usize = CTy::Option(Box::new(CTy::Int(IntTy::Usize)));
            types.extend([opt_str.clone(), opt_usize.clone()]);
            let name_f = super::fmt::fmt_expr(&opt_str, FmtKind::Debug, "w", "(&no_)", need);
            let stack_f = super::fmt::fmt_expr(&opt_usize, FmtKind::Debug, "w", "(&so_)", need);
            let nf = variant_field(p, &opt_str, "no_", 1, 0);
            let sf = variant_field(p, &opt_usize, "so_", 1, 0);
            let _ = writeln!(protos, "int dbg_{m}(lust_Formatter *f, {ct} *p);");
            let _ = writeln!(
                defs,
                "int dbg_{m}(lust_Formatter *f, {ct} *p) {{\n  {} no_; {} if (p->has_name) {{ {} {nf} = p->name; }} {} so_; {} if (p->has_stack) {{ {} {sf} = p->stack; }} lust_DebugStruct b; lust_fmt_slot s; lust_Formatter *w; lust_dstruct_new(&b, f, {}); if ((w = lust_dstruct_field(&b, &s, {}))) lust_dstruct_field_end(&b, &s, {name_f}); if ((w = lust_dstruct_field(&b, &s, {}))) lust_dstruct_field_end(&b, &s, {stack_f}); if ((w = lust_dstruct_field(&b, &s, {}))) lust_dstruct_field_end(&b, &s, lust_f_bool(w, 0)); return lust_dstruct_finish(&b);\n}}\n",
                ctype(&opt_str),
                disc_set(p, &opt_str, "no_", 0),
                disc_set(p, &opt_str, "no_", 1),
                ctype(&opt_usize),
                disc_set(p, &opt_usize, "so_", 0),
                disc_set(p, &opt_usize, "so_", 1),
                lit("Builder"),
                lit("name"),
                lit("stack_size"),
                lit("no_hooks"),
            );
        }
        _ => unreachable!("internal: no {g:?} glue for `Builder`"),
    }
}

/// Glue of `Condvar`, `Barrier`, `BarrierWaitResult`, and `OnceLock`.
#[allow(clippy::too_many_arguments)]
fn once_glue_def(p: &Program, g: Glue, k: SyncTy, e: &CTy, m: &str, ct: &str, protos: &mut String, defs: &mut String, need: &mut dyn FnMut(Glue, &CTy)) {
    let lit = |s: &str| format!("(lust_str){{(uint8_t*)\"{s}\", {}}}", s.len());
    let dbg = format!("int dbg_{m}(lust_Formatter *f, {ct} *p)");
    let (proto, body) = match (g, k) {
        (Glue::Drop, SyncTy::OnceLock) => {
            let body = if needs_drop_c(p, e) {
                need(Glue::Drop, e);
                format!("if (p->st == 2) drop_{}(&p->v);", mangle(e))
            } else {
                "(void)p;".into()
            };
            (format!("void drop_{m}({ct} *p)"), body)
        }
        (Glue::Drop, _) => (format!("void drop_{m}({ct} *p)"), "(void)p;".into()),
        (Glue::Default, _) => (format!("{ct} default_{m}(void)"), format!("{ct} r; {} return r;", zero_c("r"))),
        // `OnceLock(5)` or `OnceLock(<uninit>)` (a `format_args!`).
        (Glue::Debug, SyncTy::OnceLock) => {
            let v = super::fmt::fmt_expr(e, FmtKind::Debug, "w", "(&p->v)", need);
            (
                dbg,
                format!(
                    "lust_DebugTuple b; lust_fmt_slot s; lust_Formatter *w; lust_dtuple_new(&b, f, {}); if ((w = lust_dtuple_field(&b, &s))) lust_dtuple_field_end(&b, &s, lust_once_is_done(&p->st) ? {v} : lust_f_write_str(w, {})); return lust_dtuple_finish(&b);",
                    lit("OnceLock"),
                    lit("<uninit>")
                ),
            )
        }
        (Glue::Debug, SyncTy::BarrierWaitResult) => (
            dbg,
            format!(
                "lust_DebugStruct b; lust_fmt_slot s; lust_Formatter *w; lust_dstruct_new(&b, f, {}); if ((w = lust_dstruct_field(&b, &s, {}))) lust_dstruct_field_end(&b, &s, lust_f_bool(w, *p)); return lust_dstruct_finish(&b);",
                lit("BarrierWaitResult"),
                lit("is_leader")
            ),
        ),
        (Glue::Debug, _) => (
            dbg,
            format!("(void)p; lust_DebugStruct b; lust_dstruct_new(&b, f, {}); return lust_dstruct_finish_ne(&b);", lit(k.name())),
        ),
        _ => unreachable!("internal: no {g:?} glue for `{}`", k.name()),
    };
    let _ = writeln!(protos, "{proto};");
    let _ = writeln!(defs, "{proto} {{\n  {body}\n}}\n");
}

/// Glue of the channel ends and `SendError` (std's impls).
#[allow(clippy::too_many_arguments)]
fn chan_glue_def(p: &Program, g: Glue, k: SyncTy, e: &CTy, m: &str, ct: &str, protos: &mut String, defs: &mut String, need: &mut dyn FnMut(Glue, &CTy)) {
    let lit = |s: &str| format!("(lust_str){{(uint8_t*)\"{s}\", {}}}", s.len());
    let (proto, body) = match (g, k) {
        (Glue::Drop, SyncTy::Sender | SyncTy::SyncSender) => (format!("void drop_{m}({ct} *p)"), "lust_chan_drop_sender(*p);".to_string()),
        (Glue::Drop, SyncTy::Receiver) => (format!("void drop_{m}({ct} *p)"), "lust_chan_drop_receiver(*p);".to_string()),
        (Glue::Drop, _) => {
            let body = if needs_drop_c(p, e) {
                need(Glue::Drop, e);
                format!("drop_{}(p);", mangle(e))
            } else {
                "(void)p;".into()
            };
            (format!("void drop_{m}({ct} *p)"), body)
        }
        (Glue::Clone, SyncTy::Sender | SyncTy::SyncSender) => (format!("{ct} clone_{m}({ct} *p)"), "return lust_chan_clone_sender(*p);".to_string()),
        // `Sender { .. }`, `SyncSender { .. }`, `Receiver { .. }`, and
        // `SendError { .. }`.
        (Glue::Debug, _) => (
            format!("int dbg_{m}(lust_Formatter *f, {ct} *p)"),
            format!("(void)p; lust_DebugStruct b; lust_dstruct_new(&b, f, {}); return lust_dstruct_finish_ne(&b);", lit(k.name())),
        ),
        (Glue::Display, SyncTy::SendError) => {
            (format!("int disp_{m}(lust_Formatter *f, {ct} *p)"), format!("(void)p; return lust_f_pad(f, {});", lit("sending on a closed channel")))
        }
        _ => unreachable!("internal: no {g:?} glue for `{}`", k.name()),
    };
    let _ = writeln!(protos, "{proto};");
    let _ = writeln!(defs, "{proto} {{\n  {body}\n}}\n");
}

/// Glue of the thread types (std's impls): a `JoinHandle` drop detaches
/// its thread; `Thread` is counted; `ThreadId` prints `ThreadId(N)`.
fn thread_glue_def(g: Glue, k: SyncTy, m: &str, ct: &str, protos: &mut String, defs: &mut String) {
    let lit = |s: &str| format!("(lust_str){{(uint8_t*)\"{s}\", {}}}", s.len());
    let dbg = format!("int dbg_{m}(lust_Formatter *f, {ct} *p)");
    let (proto, body) = match (g, k) {
        (Glue::Drop, SyncTy::JoinHandle | SyncTy::ScopedJoinHandle) => (format!("void drop_{m}({ct} *p)"), "lust_join_drop(*p);".to_string()),
        (Glue::Drop, SyncTy::Thread) => (format!("void drop_{m}({ct} *p)"), "lust_thread_drop(*p);".to_string()),
        (Glue::Drop, _) => (format!("void drop_{m}({ct} *p)"), "(void)p;".to_string()),
        (Glue::Clone, SyncTy::Thread) => (format!("{ct} clone_{m}({ct} *p)"), "return lust_thread_clone(*p);".to_string()),
        (Glue::Clone, SyncTy::ThreadId) => (format!("{ct} clone_{m}({ct} *p)"), "return *p;".to_string()),
        (Glue::Eq, SyncTy::ThreadId) => (format!("uint8_t eq_{m}({ct} *a, {ct} *b)"), "return *a == *b;".to_string()),
        (Glue::Debug, SyncTy::ThreadId) => (
            dbg,
            format!(
                "lust_DebugTuple b; lust_fmt_slot s; lust_Formatter *w; lust_dtuple_new(&b, f, {}); if ((w = lust_dtuple_field(&b, &s))) lust_dtuple_field_end(&b, &s, lust_f_u64(w, *p)); return lust_dtuple_finish(&b);",
                lit("ThreadId")
            ),
        ),
        // `Thread { id: ThreadId(N), name: Some("main"), .. }`.
        (Glue::Debug, SyncTy::Thread) => (
            dbg,
            format!(
                "lust_DebugStruct b; lust_fmt_slot s; lust_Formatter *w; lust_dstruct_new(&b, f, {}); \
if ((w = lust_dstruct_field(&b, &s, {}))) {{ lust_DebugTuple b2; lust_fmt_slot s2; lust_Formatter *w2; lust_dtuple_new(&b2, w, {}); if ((w2 = lust_dtuple_field(&b2, &s2))) lust_dtuple_field_end(&b2, &s2, lust_f_u64(w2, (*p)->id)); lust_dstruct_field_end(&b, &s, lust_dtuple_finish(&b2)); }} \
if ((w = lust_dstruct_field(&b, &s, {}))) {{ int e; if ((*p)->name) {{ lust_DebugTuple b3; lust_fmt_slot s3; lust_Formatter *w3; lust_dtuple_new(&b3, w, {}); if ((w3 = lust_dtuple_field(&b3, &s3))) lust_dtuple_field_end(&b3, &s3, lust_f_dbg_str(w3, (lust_str){{(uint8_t*)(*p)->name, (*p)->name_len}})); e = lust_dtuple_finish(&b3); }} else e = lust_f_write_str(w, {}); lust_dstruct_field_end(&b, &s, e); }} \
return lust_dstruct_finish_ne(&b);",
                lit("Thread"),
                lit("id"),
                lit("ThreadId"),
                lit("name"),
                lit("Some"),
                lit("None")
            ),
        ),
        (Glue::Debug, SyncTy::JoinHandle | SyncTy::ScopedJoinHandle) => (
            dbg,
            format!("(void)p; lust_DebugStruct b; lust_dstruct_new(&b, f, {}); return lust_dstruct_finish_ne(&b);", lit(k.name())),
        ),
        (Glue::Debug, SyncTy::JoinError) => (
            dbg,
            format!("(void)p; lust_DebugStruct b; lust_dstruct_new(&b, f, {}); return lust_dstruct_finish_ne(&b);", lit("Any")),
        ),
        _ => unreachable!("internal: no {g:?} glue for `{}`", k.name()),
    };
    let _ = writeln!(protos, "{proto};");
    let _ = writeln!(defs, "{proto} {{\n  {body}\n}}\n");
}

/// Glue of the locks, their guards, and `PoisonError` (std's impls).
#[allow(clippy::too_many_arguments)]
fn lock_glue_def(p: &Program, g: Glue, k: SyncTy, e: &CTy, m: &str, ct: &str, protos: &mut String, defs: &mut String, need: &mut dyn FnMut(Glue, &CTy)) {
    let lit = |s: &str| format!("(lust_str){{(uint8_t*)\"{s}\", {}}}", s.len());
    let (proto, body) = match (g, k) {
        (Glue::Drop, SyncTy::Mutex | SyncTy::RwLock | SyncTy::PoisonError) => {
            let inner = if needs_drop_c(p, e) {
                need(Glue::Drop, e);
                let at = if k == SyncTy::PoisonError { "p" } else { "&p->v" };
                format!("drop_{}({at});", mangle(e))
            } else {
                "(void)p;".into()
            };
            (format!("void drop_{m}({ct} *p)"), inner)
        }
        // A guard gives its lock back (runtime/sync.c).
        // A write guard dropped by a panic poisons its lock (runtime/sync.c
        // `lust_poison_leave`).
        (Glue::Drop, SyncTy::MutexGuard) => (format!("void drop_{m}({ct} *p)"), "lust_poison_leave(&(*p)->poison); lust_mutex_unlock(&(*p)->st);".into()),
        (Glue::Drop, SyncTy::RwLockReadGuard) => (format!("void drop_{m}({ct} *p)"), "lust_rw_read_unlock(&(*p)->st);".into()),
        (Glue::Drop, SyncTy::RwLockWriteGuard) => {
            (format!("void drop_{m}({ct} *p)"), "lust_poison_leave(&(*p)->poison); lust_rw_write_unlock(&(*p)->st);".into())
        }
        (Glue::Default, SyncTy::Mutex | SyncTy::RwLock) => {
            need(Glue::Default, e);
            (format!("{ct} default_{m}(void)"), format!("{ct} r; {} r.v = default_{}(); return r;", zero_c("r"), mangle(e)))
        }
        // `Mutex { data: .., poisoned: false, .. }`: std's try_lock (or
        // try_read); a held Mutex prints the str `"<locked>"` (Debug,
        // so quoted), a held RwLock prints a bare `<locked>`.
        (Glue::Debug, SyncTy::Mutex | SyncTy::RwLock) => {
            let (name, try_, unlock, locked) = if k == SyncTy::Mutex {
                ("Mutex", "lust_mutex_trylock", "lust_mutex_unlock", "lust_f_dbg_str")
            } else {
                ("RwLock", "lust_rw_tryread", "lust_rw_read_unlock", "lust_f_write_str")
            };
            let v = super::fmt::fmt_expr(e, FmtKind::Debug, "w", "(&p->v)", need);
            let body = format!(
                "lust_DebugStruct b; lust_fmt_slot s; lust_Formatter *w; lust_dstruct_new(&b, f, {}); \
if ({try_}(&p->st)) {{ if ((w = lust_dstruct_field(&b, &s, {}))) lust_dstruct_field_end(&b, &s, {v}); {unlock}(&p->st); }} \
else if ((w = lust_dstruct_field(&b, &s, {}))) lust_dstruct_field_end(&b, &s, {locked}(w, {})); \
if ((w = lust_dstruct_field(&b, &s, {}))) lust_dstruct_field_end(&b, &s, lust_f_bool(w, p->poison & 1)); return lust_dstruct_finish_ne(&b);",
                lit(name),
                lit("data"),
                lit("data"),
                lit("<locked>"),
                lit("poisoned")
            );
            (format!("int dbg_{m}(lust_Formatter *f, {ct} *p)"), body)
        }
        // A guard formats its value.
        (Glue::Debug | Glue::Display, _) if k.guard().is_some() => {
            let kind = if g == Glue::Debug { FmtKind::Debug } else { FmtKind::Display };
            let v = super::fmt::fmt_expr(e, kind, "f", "(&(*p)->v)", need);
            let name = if g == Glue::Debug { "dbg" } else { "disp" };
            (format!("int {name}_{m}(lust_Formatter *f, {ct} *p)"), format!("return {v};"))
        }
        (Glue::Debug, SyncTy::PoisonError) => (
            format!("int dbg_{m}(lust_Formatter *f, {ct} *p)"),
            format!("(void)p; lust_DebugStruct b; lust_dstruct_new(&b, f, {}); return lust_dstruct_finish_ne(&b);", lit("PoisonError")),
        ),
        (Glue::Display, SyncTy::PoisonError) => (
            format!("int disp_{m}(lust_Formatter *f, {ct} *p)"),
            format!("(void)p; return lust_f_pad(f, {});", lit("poisoned lock: another task failed inside")),
        ),
        _ => unreachable!("internal: no {g:?} glue for `{}`", k.name()),
    };
    let _ = writeln!(protos, "{proto};");
    let _ = writeln!(defs, "{proto} {{\n  {body}\n}}\n");
}

/// What a closure-taking thread or sync call calls (`FnGen::callee_of`).
pub(super) enum Callee {
    /// A closure's body fn; true when it takes its env by value.
    Closure(LocalDefId, bool),
    /// A fn item's instance.
    Fn(LocalDefId),
    /// A fn pointer of this C type, held in the operand.
    Ptr(CTy),
    /// A `Box<dyn FnOnce() -> R>` (gopanic.rs `ThreadMain`): the call is
    /// the vtable's word `.1` (`FnOnce::call_once`) on the box's data
    /// pointer; that entry consumes the value and frees the box. `.0` is
    /// the C type of `R`.
    DynOnce(CTy, u32),
    /// A `&dyn Fn(..) -> R` or `&mut dyn FnMut(..) -> R` value (a fat
    /// reference: goport.rs `guard(emit_file)` with `emit_file: &dyn
    /// Fn() -> EmitResult`): the call is the vtable's call entry
    /// (`VT_HEADER`) on the data pointer with the arguments, as a `dyn
    /// Fn*` call is; nothing is consumed. `.0` is the C type of `R`,
    /// `.1` the C types of the parameters.
    DynRef(CTy, Vec<CTy>),
}

/// The runtime width suffix of an atomic (`1`, `2`, `4`, or `8`).
fn width(v: AtomicVal) -> u32 {
    v.bytes()
}

/// The atomic of a `&Atomic*` operand type.
fn atomic_of_ref(t: &CTy) -> AtomicVal {
    match t {
        CTy::Ref(inner) => atomic_of_ref(inner),
        CTy::Sync(k, _) => k.atomic_value().expect("an atomic receiver"),
        _ => unreachable!("an atomic receiver"),
    }
}

/// The C form of an atomic's value type.
pub(super) fn vt_of(v: AtomicVal) -> CTy {
    match v {
        AtomicVal::Bool => CTy::Bool,
        AtomicVal::Int(i) => CTy::Int(i),
    }
}

/// The C value of an `atomic::Ordering` operand (its discriminant).
fn ord(p: &Program, v: &str, t: &CTy) -> String {
    disc_call(p, t, &format!("(&{v})"))
}

impl FnGen<'_, '_> {
    /// One sync builtin call: C statements to `self.out`, and the C
    /// expression of its value.
    pub(super) fn sync_builtin(&mut self, op: SyncOp, vals: &[String], tys: &[CTy], loc: &str) -> String {
        use crate::check::sync::FetchOp as F;
        use SyncOp as S;
        // The runtime works on unsigned words of the atomic's width: the
        // receiver pointer and the values cast to it, the result back.
        let atomic = |i: usize| atomic_of_ref(&tys[i]);
        let word = |v: AtomicVal| format!("uint{}_t", width(v) * 8);
        let ptr = |v: AtomicVal| format!("(({}*)({}))", word(v), vals[0]);
        let arg = |v: AtomicVal, i: usize| format!("(({})({}))", word(v), vals[i]);
        let back = |v: AtomicVal, call: String| format!("(({}){call})", ctype(&vt_of(v)));
        match op {
            S::AtomicNew(_) | S::AtomicFrom(_) | S::AtomicIntoInner | S::AtomicGetMut => vals[0].clone(),
            S::AtomicDefault(k) => format!("(({})0)", sync_ctype(k, &CTy::Unit)),
            S::AtomicLoad => {
                let v = atomic(0);
                back(v, format!("lust_at_load_{}({}, {}, {loc})", width(v), ptr(v), ord(self.p, &vals[1], &tys[1])))
            }
            S::AtomicStore => {
                let v = atomic(0);
                format!("(lust_at_store_{}({}, {}, {}, {loc}), ((lust_Unit){{}}))", width(v), ptr(v), arg(v, 1), ord(self.p, &vals[2], &tys[2]))
            }
            S::AtomicSwap => {
                let v = atomic(0);
                back(v, format!("lust_at_swap_{}({}, {}, {})", width(v), ptr(v), arg(v, 1), ord(self.p, &vals[2], &tys[2])))
            }
            S::AtomicFetch(f) => {
                let v = atomic(0);
                let signed = matches!(v, AtomicVal::Int(i) if i.signed());
                let name = match f {
                    F::Add => "add",
                    F::Sub => "sub",
                    F::And => "and",
                    F::Or => "or",
                    F::Xor => "xor",
                    F::Nand if v == AtomicVal::Bool => "bnand",
                    F::Nand => "nand",
                    F::Max if signed => "smax",
                    F::Max => "umax",
                    F::Min if signed => "smin",
                    F::Min => "umin",
                };
                back(v, format!("lust_at_fetch_{name}_{}({}, {}, {})", width(v), ptr(v), arg(v, 1), ord(self.p, &vals[2], &tys[2])))
            }
            S::AtomicFetchNot => {
                let v = atomic(0);
                back(v, format!("lust_at_fetch_xor_{}({}, 1, {})", width(v), ptr(v), ord(self.p, &vals[1], &tys[1])))
            }
            S::AtomicCompareExchange | S::AtomicCompareExchangeWeak => {
                let v = atomic(0);
                let res = CTy::Result(Box::new(vt_of(v)), Box::new(vt_of(v)));
                self.note_held(&res);
                let (t, old) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    {} {t}; {} {old}; int {t}_ok = lust_at_cas_{}({}, {}, {}, {}, {}, &{old}, {weak});",
                    ctype(&res),
                    word(v),
                    width(v),
                    ptr(v),
                    arg(v, 1),
                    arg(v, 2),
                    ord(self.p, &vals[3], &tys[3]),
                    ord(self.p, &vals[4], &tys[4]),
                    // Its ordering panics report core's atomic.rs line (sync.c).
                    weak = u8::from(op == S::AtomicCompareExchangeWeak),
                );
                let vt = ctype(&vt_of(v));
                let ok_f = variant_field(self.p, &res, &t, 0, 0);
                let err_f = variant_field(self.p, &res, &t, 1, 0);
                let set_ok = disc_set(self.p, &res, &t, 0);
                let set_err = disc_set(self.p, &res, &t, 1);
                let _ = writeln!(self.out, "    if ({t}_ok) {{ {set_ok} {ok_f} = ({vt}){old}; }} else {{ {set_err} {err_f} = ({vt}){old}; }}");
                t
            }
            S::Fence => format!("(lust_at_fence({}, {loc}), ((lust_Unit){{}}))", ord(self.p, &vals[0], &tys[0])),
            S::CompilerFence => format!("(lust_at_compiler_fence({}, {loc}), ((lust_Unit){{}}))", ord(self.p, &vals[0], &tys[0])),
            S::SpinLoop => "((lust_Unit){})".into(),
            S::ArcNew
            | S::ArcStrongCount
            | S::ArcWeakCount
            | S::ArcPtrEq
            | S::ArcAsPtr
            | S::ArcDowngrade
            | S::ArcGetMut
            | S::ArcMakeMut
            | S::ArcTryUnwrap
            | S::ArcIntoInner
            | S::ArcUnwrapOrClone
            | S::ArcWeakNew
            | S::ArcWeakUpgrade
            | S::ArcWeakStrongCount
            | S::ArcWeakWeakCount
            | S::ArcWeakPtrEq => self.arc_builtin(op, vals, tys),
            S::ThreadSpawn | S::ScopeSpawn | S::ThreadScope => unreachable!("closure-taking thread calls go through thread_closure_call"),
            S::CatchUnwind => unreachable!("catch_unwind goes through catch_unwind_call"),
            // `resume_unwind` and `panic_any` (cgen/unwind.rs's runtime half).
            S::ResumeUnwind => format!("(lust_unw_resume_box({}), ((lust_Unit){{}}))", vals[0]),
            S::PanicAny => format!("(lust_panic_box({}, {loc}), ((lust_Unit){{}}))", vals[0]),
            // The runtime's hook slot: swap a value of the slot's type in.
            S::PanicHookSwap => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {} {t} = {}; lust_hook_swap(&{t}, sizeof {t});", ctype(&tys[0]), vals[0]);
                t
            }
            S::PanicHookRef => "lust_hook_slot()".into(),
            S::PanicHookPayload => "lust_hook_payload()".into(),
            S::PanicHookLocation => "lust_hook_location()".into(),
            S::ThreadCurrent => "lust_thread_current()".into(),
            S::ThreadYieldNow => "(lust_thread_yield(), ((lust_Unit){}))".into(),
            // True while a panic unwinds, and in a panic hook (both modes).
            S::ThreadPanicking => "lust_unw_panicking()".into(),
            S::JoinHandleJoin => {
                // `Ok(value)`: the result sits right after the header.
                let el = match &tys[0] {
                    CTy::Sync(_, e) => (**e).clone(),
                    other => unreachable!("a JoinHandle operand, found {other:?}"),
                };
                // `Err(payload)` when the thread panicked (W-UNWIND).
                let res = CTy::Result(Box::new(el.clone()), Box::new(CTy::BoxDyn));
                self.note_held(&res);
                let (t, h) = (self.tmp(), self.tmp());
                let f = variant_field(self.p, &res, &t, 0, 0);
                let e = variant_field(self.p, &res, &t, 1, 0);
                let _ = writeln!(
                    self.out,
                    "    lust_JoinHdr *{h} = {}; lust_thread_join({h}); {} {t}; if ({h}->panicked) {{ {} {e} = {h}->payload; {h}->panicked = 0; }} else {{ {} {f} = ((struct {{ lust_JoinHdr h; {} ret; }} *){h})->ret; }} lust_join_free({h});",
                    vals[0],
                    ctype(&res),
                    disc_set(self.p, &res, &t, 1),
                    disc_set(self.p, &res, &t, 0),
                    ctype(&el)
                );
                t
            }
            S::JoinHandleThread => format!("(&(*{})->th)", vals[0]),
            S::JoinHandleIsFinished => format!("((uint8_t)lust_join_is_finished(*{}))", vals[0]),
            S::ThreadGetId => format!("((*{})->id)", vals[0]),
            S::ThreadGetName => {
                let opt = CTy::Option(Box::new(CTy::Ref(Box::new(CTy::Str))));
                self.note_held(&opt);
                let (t, th) = (self.tmp(), self.tmp());
                let f = variant_field(self.p, &opt, &t, 1, 0);
                let _ = writeln!(
                    self.out,
                    "    lust_ThreadInfo *{th} = *{}; {} {t}; if ({th}->name) {{ {} {f} = (lust_str){{(uint8_t*){th}->name, {th}->name_len}}; }} else {{ {} }}",
                    vals[0],
                    ctype(&opt),
                    disc_set(self.p, &opt, &t, 1),
                    disc_set(self.p, &opt, &t, 0)
                );
                t
            }
            S::Channel | S::SyncChannel => unreachable!("channel calls go through channel_new"),
            // An mpsc iterator: a one-field tuple of the receiver (or a
            // reference to it).
            S::RecvMakeIter(u) => {
                let el = match deref_cty(&tys[0]) {
                    CTy::Sync(_, e) => *e,
                    other => unreachable!("a Receiver operand, found {other:?}"),
                };
                let rx = CTy::Sync(SyncTy::Receiver, Box::new(el));
                let field = if u == 2 { rx } else { CTy::Ref(Box::new(rx)) };
                let it = CTy::Tuple(vec![field]);
                self.note_held(&it);
                let t = self.tmp();
                let _ = writeln!(self.out, "    {} {t}; {t}.f0 = {};", ctype(&it), vals[0]);
                t
            }
            S::RecvNext(block) => {
                let el = match deref_cty(&tys[0]) {
                    CTy::Sync(_, e) => *e,
                    other => unreachable!("a Receiver operand, found {other:?}"),
                };
                let opt = CTy::Option(Box::new(el));
                self.note_held(&opt);
                let t = self.tmp();
                let f = variant_field(self.p, &opt, &t, 1, 0);
                let _ = writeln!(
                    self.out,
                    "    {} {t}; if (lust_chan_recv(*{}, &{f}, {}) == 0) {{ {} }} else {{ {} }}",
                    ctype(&opt),
                    vals[0],
                    u8::from(block),
                    disc_set(self.p, &opt, &t, 1),
                    disc_set(self.p, &opt, &t, 0)
                );
                t
            }
            S::DurNew => format!("lust_dur_new({}, {}, {loc})", vals[0], vals[1]),
            S::DurFrom(u) => {
                let per = [1u64, 1_000, 1_000_000, 1_000_000_000][u as usize & 3];
                let v = &vals[0];
                if per == 1 {
                    format!("((lust_Duration){{{v}, 0}})")
                } else {
                    format!("((lust_Duration){{({v}) / {per}u, (uint32_t)((({v}) % {per}u) * {}u)}})", 1_000_000_000 / per)
                }
            }
            S::DurAs(0) => format!("({})->secs", vals[0]),
            S::DurAs(u) => {
                let per = [1u64, 1_000, 1_000_000, 1_000_000_000][u as usize & 3];
                format!("lust_dur_as(*({}), {per}u, {}u)", vals[0], 1_000_000_000 / per)
            }
            S::DurSubsec(u) => format!("(({})->nanos / {}u)", vals[0], [1_000_000_000u64, 1_000_000, 1_000, 1][u as usize & 3]),
            S::DurIsZero => format!("((uint8_t)(({0})->secs == 0 && ({0})->nanos == 0))", vals[0]),
            // A std source `core::time::Duration` (W-STD-C) is the struct
            // `{ secs: u64, nanos: u32 }`: rebuild the runtime's value.
            S::ThreadSleep if matches!(tys.first(), Some(CTy::Adt(_))) => {
                format!("(lust_thread_sleep(((lust_Duration){{ ({0}).f0, ({0}).f1 }})), ((lust_Unit){{}}))", vals[0])
            }
            S::ThreadSleep => format!("(lust_thread_sleep({}), ((lust_Unit){{}}))", vals[0]),
            // `thread::Builder` (TRIAGE T5): a plain struct value.
            S::BuilderNew => "((lust_ThreadBuilder){0})".into(),
            S::BuilderName => {
                let (t, v) = (self.tmp(), self.tmp());
                self.want(Glue::Drop, &CTy::String);
                let _ = writeln!(
                    self.out,
                    "    lust_ThreadBuilder {t} = {}; lust_String {v} = {}; if ({t}.has_name) drop_{}(&{t}.name); {t}.name = {v}; {t}.has_name = 1;",
                    vals[0],
                    vals[1],
                    mangle(&CTy::String)
                );
                t
            }
            S::BuilderStackSize => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    lust_ThreadBuilder {t} = {}; {t}.stack = {}; {t}.has_stack = 1;", vals[0], vals[1]);
                t
            }
            S::ChanSend => {
                let el = match deref_cty(&tys[0]) {
                    CTy::Sync(_, e) => *e,
                    other => unreachable!("a Sender operand, found {other:?}"),
                };
                let res = CTy::Result(Box::new(CTy::Unit), Box::new(CTy::Sync(SyncTy::SendError, Box::new(el.clone()))));
                self.note_held(&res);
                let (t, v) = (self.tmp(), self.tmp());
                let err = variant_field(self.p, &res, &t, 1, 0);
                let _ = writeln!(
                    self.out,
                    "    {} {v} = {}; {} {t}; if (lust_chan_send(*{}, &{v})) {{ {} {err} = {v}; }} else {{ {} }}",
                    ctype(&el),
                    vals[1],
                    ctype(&res),
                    vals[0],
                    disc_set(self.p, &res, &t, 1),
                    disc_set(self.p, &res, &t, 0)
                );
                t
            }
            S::ChanRecv | S::ChanTryRecv => {
                let el = match deref_cty(&tys[0]) {
                    CTy::Sync(_, e) => *e,
                    other => unreachable!("a Receiver operand, found {other:?}"),
                };
                let def = if op == S::ChanRecv { crate::check::generics::recv_error_def() } else { crate::check::generics::try_recv_error_def() };
                let et = self.p.tys.local_adt_of(def).map_or(CTy::Unit, CTy::Adt);
                let res = CTy::Result(Box::new(el.clone()), Box::new(et.clone()));
                self.note_held(&res);
                let (t, r) = (self.tmp(), self.tmp());
                let ok = variant_field(self.p, &res, &t, 0, 0);
                let err = variant_field(self.p, &res, &t, 1, 0);
                // try_recv: 1 is `Empty` (variant 0), 2 `Disconnected`.
                let err_val = if op == S::ChanRecv {
                    zero_c(&err)
                } else {
                    format!("{} if ({r} == 2) {{ {} }} else {{ {} }}", zero_c(&err), disc_set(self.p, &et, &err, 1), disc_set(self.p, &et, &err, 0))
                };
                let _ = writeln!(
                    self.out,
                    "    {} {t}; int {r} = lust_chan_recv(*{}, &{ok}, {}); if ({r} == 0) {{ {} }} else {{ {} {err_val} }}",
                    ctype(&res),
                    vals[0],
                    u8::from(op == S::ChanRecv),
                    disc_set(self.p, &res, &t, 0),
                    disc_set(self.p, &res, &t, 1)
                );
                t
            }
            // `recv_timeout`: the runtime's 1 is `Timeout` (variant 0),
            // 2 `Disconnected` (tf-p6 R09).
            S::ChanRecvTimeout => {
                let el = match deref_cty(&tys[0]) {
                    CTy::Sync(_, e) => *e,
                    other => unreachable!("a Receiver operand, found {other:?}"),
                };
                let et = self.p.tys.local_adt_of(crate::check::generics::recv_timeout_error_def()).map_or(CTy::Unit, CTy::Adt);
                let res = CTy::Result(Box::new(el.clone()), Box::new(et.clone()));
                self.note_held(&res);
                let (secs, nanos) =
                    if matches!(tys[1], CTy::Adt(_)) { (format!("({}).f0", vals[1]), format!("({}).f1", vals[1])) } else { (format!("({}).secs", vals[1]), format!("({}).nanos", vals[1])) };
                let (t, r) = (self.tmp(), self.tmp());
                let ok = variant_field(self.p, &res, &t, 0, 0);
                let err = variant_field(self.p, &res, &t, 1, 0);
                let _ = writeln!(
                    self.out,
                    "    {} {t}; int {r} = lust_chan_recv_timeout(*{}, &{ok}, {secs}, {nanos}); if ({r} == 0) {{ {} }} else {{ {} {} if ({r} == 2) {{ {} }} else {{ {} }} }}",
                    ctype(&res),
                    vals[0],
                    disc_set(self.p, &res, &t, 0),
                    disc_set(self.p, &res, &t, 1),
                    zero_c(&err),
                    disc_set(self.p, &et, &err, 1),
                    disc_set(self.p, &et, &err, 0)
                );
                t
            }
            _ => self.lock_builtin(op, vals, tys),
        }
    }

    /// `SyncSender::try_send` (TRIAGE T5): like `ChanSend`, with
    /// the runtime's full/disconnected codes selecting the
    /// `TrySendError` variant of the destination Result.
    pub(super) fn chan_try_send(&mut self, args: &[Operand], dest: &CTy, loc: &str, post: &mut Vec<String>) -> String {
        let (chan, _) = self.operand(&args[0], loc, post);
        let (v, vt) = self.operand(&args[1], loc, post);
        let et = match dest {
            CTy::Result(_, e) => (**e).clone(),
            _ => CTy::Unit,
        };
        let (t, vv, r) = (self.tmp(), self.tmp(), self.tmp());
        let err = variant_field(self.p, dest, &t, 1, 0);
        let full = variant_field(self.p, &et, &err, 0, 0);
        let disc = variant_field(self.p, &et, &err, 1, 0);
        let _ = writeln!(
            self.out,
            "    {} {vv} = {}; {} {t}; int {r} = lust_chan_try_send(*{}, &{vv}); if ({r} == 0) {{ {} }} else {{ {} if ({r} == 2) {{ {disc} = {vv}; {} }} else {{ {full} = {vv}; {} }} }}",
            ctype(&vt),
            v,
            ctype(dest),
            chan,
            disc_set(self.p, dest, &t, 0),
            disc_set(self.p, dest, &t, 1),
            disc_set(self.p, &et, &err, 1),
            disc_set(self.p, &et, &err, 0)
        );
        t
    }

    /// `Mutex::try_lock`, `RwLock::try_read` and `try_write` (`write`):
    /// `Ok(guard)`, `Err(WouldBlock)` when the lock is held, and
    /// `Err(Poisoned(PoisonError(guard)))` when it was taken but is
    /// poisoned (panic=unwind only). As in std, the poisoned case keeps
    /// the lock: dropping the guard inside the error unlocks it. A
    /// write guard records the panic state as `lock` does.
    pub(super) fn try_lock(&mut self, write: bool, args: &[Operand], dest: &CTy, loc: &str, post: &mut Vec<String>) -> String {
        let (o, ot) = self.operand(&args[0], loc, post);
        let (call, enter) = match deref_cty(&ot) {
            CTy::Sync(SyncTy::Mutex, _) => ("lust_mutex_trylock", true),
            _ if write => ("lust_rw_trywrite", true),
            _ => ("lust_rw_tryread", false),
        };
        let et = match dest {
            CTy::Result(_, e) => (**e).clone(),
            other => unreachable!("try_lock returns a Result, found {other:?}"),
        };
        let t = self.tmp();
        let (ok, err) = (variant_field(self.p, dest, &t, 0, 0), variant_field(self.p, dest, &t, 1, 0));
        let poisoned = variant_field(self.p, &et, &err, 0, 0);
        let enter = if enter { format!(" lust_poison_enter(&({o})->poison);") } else { String::new() };
        let _ = writeln!(
            self.out,
            "    {} {t}; if ({call}(&({o})->st)) {{{enter} if (({o})->poison & 1) {{ {} {} {poisoned} = {o}; {} }} else {{ {} {ok} = {o}; }} }} else {{ {} {} {} }}",
            ctype(dest),
            disc_set(self.p, dest, &t, 1),
            zero_c(&err),
            disc_set(self.p, &et, &err, 0),
            disc_set(self.p, dest, &t, 0),
            disc_set(self.p, dest, &t, 1),
            zero_c(&err),
            disc_set(self.p, &et, &err, 1),
        );
        t
    }

    /// `Arc::new_cyclic(data_fn)` (TRIAGE T5) and `Rc::new_cyclic`
    /// (`atomic` false): allocate the counted header with strong
    /// count 0 (so `upgrade` inside `data_fn` fails, as in std), run
    /// the closure with a Weak to it, store its value, then publish
    /// strong count 1; the Weak's count becomes the strong refs'
    /// implicit one. A panic in `data_fn` under unwind leaves the
    /// allocation uninitialized with strong 0: std drops it once
    /// the last Weak goes; lust's weak drop only frees through the
    /// header, so it can leak in that case.
    pub(super) fn new_cyclic(&mut self, ops: &[Operand], loc: &str, post: &mut Vec<String>, atomic: bool) -> String {
        let callee = self.callee_of(&ops[0]);
        let once = !matches!(callee, Callee::Closure(_, false));
        let (env, env_ty) = self.operand(&ops[0], loc, post);
        self.note_held(&env_ty);
        let ret = self.callee_ret(&callee);
        self.note_held(&ret);
        let it = format!("RcI_{}", mangle(&ret));
        let (h, ev, w) = (self.tmp(), self.tmp(), self.tmp());
        let _ = writeln!(
            self.out,
            "    {it} *{h} = ({it}*)lust_alloc({}, _Alignof({it})); {h}->strong = 0; {h}->weak = 1;{} {} {ev} = {env}; {it} *{w} = {h};",
            super::rc_size(&it, &ret),
            if atomic { format!(" lust_arc_downgrade((uint64_t*){h});") } else { String::new() },
            ctype(&env_ty)
        );
        let mut body = String::new();
        let v = self.callee_call_c(&mut body, &callee, &ev, &[format!("&{w}")]);
        self.out.push_str(&body);
        if !once && needs_drop_c(self.p, &env_ty) {
            self.want(Glue::Drop, &env_ty);
            let _ = writeln!(self.out, "    drop_{}(&{ev});", mangle(&env_ty));
        }
        let hv = super::rc_value(&h, &ret);
        if atomic {
            let _ = writeln!(self.out, "    {hv} = {v}; lust_arc_inc(&({h})->strong); (void)lust_arc_dec(&({h})->weak);");
        } else {
            let _ = writeln!(self.out, "    {hv} = {v}; {h}->strong = 1;");
        }
        let _ = loc;
        format!("({h})")
    }

    /// `thread::available_parallelism` (TRIAGE T5): Ok of the
    /// count as a NonZero, or Err of the errno as an io::Error
    /// (its Repr::Os form, like fmt's io_result_of), or std's
    /// `UNKNOWN_THREAD_COUNT` (runtime/sync.c lust_avail_parallelism).
    pub(super) fn avail_par(&mut self, dest: &CTy, loc: &str, post: &mut Vec<String>) -> String {
        let _ = (loc, post);
        let (nz, err_a) = match dest {
            CTy::Result(a, b) => ((**a).clone(), (**b).clone()),
            _ => return "0".into(),
        };
        let CTy::Adt(err_id) = err_a else { return "0".into() };
        let repr_ty = self.p.adt(err_id).variants[0].fields[0].ty;
        let repr_cty = cty(&self.p.tys, repr_ty);
        let CTy::Adt(repr_a) = repr_cty else { return "0".into() };
        let os = self.p.adt(repr_a).variants.iter().position(|v| self.p.interner.get(v.name) == "Os").expect("io::Error Repr has an Os variant");
        let (t, e, n) = (self.tmp(), self.tmp(), self.tmp());
        let okv = variant_field(self.p, dest, &t, 0, 0);
        let errv = variant_field(self.p, dest, &t, 1, 0);
        let osf = variant_field(self.p, &repr_cty, &format!("{errv}.f0"), os, 0);
        let _ = writeln!(
            self.out,
            "    int32_t {e} = 0; uint64_t {n} = lust_avail_parallelism(&{e}); {} {t}; if ({n} > 0) {{ {} {okv} = ({}){{ {n} }}; }} else {{ {} {errv} = ({}){{ }}; }}",
            ctype(dest),
            disc_set(self.p, dest, &t, 0),
            ctype(&nz),
            disc_set(self.p, dest, &t, 1),
            ctype(&err_a),
        );
        let repr_place = format!("{errv}.f0");
        // `*err == -1` is std's `io::Error::UNKNOWN_THREAD_COUNT`: a
        // SimpleMessage of kind NotFound.
        let simple = self.p.adt(repr_a).variants.iter().position(|v| self.p.interner.get(v.name) == "SimpleMessage").expect("io::Error Repr has a SimpleMessage variant");
        let kind_cty = cty(&self.p.tys, self.p.adt(repr_a).variants[simple].fields[0].ty);
        let CTy::Adt(kind_a) = kind_cty else { return "0".into() };
        let not_found = self.p.adt(kind_a).variants.iter().position(|v| self.p.interner.get(v.name) == "NotFound").expect("ErrorKind has NotFound");
        let kf = variant_field(self.p, &repr_cty, &repr_place, simple, 0);
        let mf = variant_field(self.p, &repr_cty, &repr_place, simple, 1);
        let msg = "the number of hardware threads is not known for the target platform";
        let _ = writeln!(
            self.out,
            "    if ({n} == 0 && {e} == -1) {{ {} {mf} = ((lust_str){{(uint8_t*){}, {}}}); {} }} else if ({n} == 0) {{ {osf} = {e}; {} }}",
            disc_set(self.p, &kind_cty, &kf, not_found),
            c_string_lit(msg.as_bytes()),
            msg.len(),
            disc_set(self.p, &repr_cty, &repr_place, simple),
            disc_set(self.p, &repr_cty, &repr_place, os)
        );
        t
    }

    /// `mpsc::channel()` or `sync_channel(cap)` into the C pair type
    /// `pair` (`(Sender<T>, Receiver<T>)`): one runtime channel that both
    /// ends point at, with `T`'s drop glue for values left queued.
    pub(super) fn channel_new(&mut self, pair: &CTy, cap: &str) -> String {
        let el = match pair {
            CTy::Tuple(es) => match es.first() {
                Some(CTy::Sync(_, e)) => (**e).clone(),
                _ => CTy::Unit,
            },
            _ => CTy::Unit,
        };
        // Both ends are pointers; the channel sizes the element (`sizeof`).
        self.note_held(pair);
        self.note_held(&el);
        let drop = if needs_drop_c(self.p, &el) {
            self.want(Glue::Drop, &el);
            format!("(void (*)(void *))drop_{}", mangle(&el))
        } else {
            "0".into()
        };
        let (t, c) = (self.tmp(), self.tmp());
        let _ = writeln!(
            self.out,
            "    lust_Chan *{c} = lust_chan_new(sizeof({0}), _Alignof({0}), {cap}, {drop}); {1} {t}; {t}.f0 = {c}; {t}.f1 = {c};",
            ctype(&el),
            ctype(pair)
        );
        t
    }

    /// `a.fetch_update(set_order, fetch_order, f)`, as std writes it: load
    /// with `fetch_order`, then while `f(prev)` gives `Some(next)`, a
    /// compare-exchange of `prev` for `next` (`Ok(prev)` on success; a
    /// failure reloads `prev`); `Err(prev)` once `f` gives `None`.
    fn atomic_fetch_update(&mut self, ops: &[Operand], loc: &str, post: &mut Vec<String>) -> String {
        let callee = self.callee_of(&ops[3]);
        let (a, at) = self.operand(&ops[0], loc, post);
        let (so, sot) = self.operand(&ops[1], loc, post);
        let (fo, fot) = self.operand(&ops[2], loc, post);
        let v = atomic_of_ref(&at);
        let w = width(v);
        let word = format!("uint{}_t", w * 8);
        let vt = vt_of(v);
        let (env, env_ty) = self.operand(&ops[3], loc, post);
        self.note_held(&env_ty);
        let ev = self.tmp();
        let _ = writeln!(self.out, "    {} {ev} = {env};", ctype(&env_ty));
        let res = CTy::Result(Box::new(vt.clone()), Box::new(vt.clone()));
        let opt = CTy::Option(Box::new(vt.clone()));
        self.note_held(&res);
        self.note_held(&opt);
        let (t, prev, old) = (self.tmp(), self.tmp(), self.tmp());
        let (sord, ford) = (ord(self.p, &so, &sot), ord(self.p, &fo, &fot));
        let _ = writeln!(self.out, "    {} {t}; {word} {prev} = lust_at_load_{w}(({word}*)({a}), {ford}, {loc});", ctype(&res));
        let mut body = String::new();
        let r = self.callee_call_c(&mut body, &callee, &ev, &[format!("(({}){prev})", ctype(&vt))]);
        let ok_f = variant_field(self.p, &res, &t, 0, 0);
        let err_f = variant_field(self.p, &res, &t, 1, 0);
        let (set_ok, set_err) = (disc_set(self.p, &res, &t, 0), disc_set(self.p, &res, &t, 1));
        let nx = self.tmp();
        let _ = writeln!(body, "  {} {nx} = {r};", ctype(&opt));
        let some = variant_field(self.p, &opt, &nx, 1, 0);
        let is_none = format!("{} == 0", disc_call(self.p, &opt, &format!("(&{nx})")));
        let _ = writeln!(body, "  if ({is_none}) {{ {set_err} {err_f} = ({}){prev}; break; }}", ctype(&vt));
        let _ = writeln!(body, "  {word} {old};");
        let _ = writeln!(
            body,
            "  if (lust_at_cas_{w}(({word}*)({a}), {prev}, ({word})({some}), {sord}, {ford}, &{old}, 1)) {{ {set_ok} {ok_f} = ({}){prev}; break; }}",
            ctype(&vt)
        );
        let _ = writeln!(body, "  {prev} = {old};");
        let drop_env = if needs_drop_c(self.p, &env_ty) {
            self.want(Glue::Drop, &env_ty);
            format!("drop_{}(&{ev});", mangle(&env_ty))
        } else {
            String::new()
        };
        let _ = writeln!(self.out, "    for (;;) {{\n{body}    }}\n    {drop_env}");
        t
    }

    /// `cv.wait_while(guard, f)`: waits while `f(&mut *guard)` holds; and
    /// `once.get_or_init(f)`: runs `f` only in the call that sets the
    /// value (a closure that never runs still drops its env).
    fn closure_wait_or_init(&mut self, op: SyncOp, ops: &[Operand], ci: usize, loc: &str, post: &mut Vec<String>) -> String {
        let callee = self.callee_of(&ops[ci]);
        let once = !matches!(callee, Callee::Closure(_, false));
        let target = self.operand(&ops[0], loc, post).0;
        let guard = matches!(op, SyncOp::CondvarWaitWhile | SyncOp::CondvarWaitTimeoutWhile).then(|| self.operand(&ops[1], loc, post));
        // `wait_timeout_while`: the duration, then std's loop over
        // `dur.checked_sub(start.elapsed())` (the runtime's `lust_cv_left`).
        let dur = (op == SyncOp::CondvarWaitTimeoutWhile).then(|| self.operand(&ops[2], loc, post));
        let (env, env_ty) = self.operand(&ops[ci], loc, post);
        self.note_held(&env_ty);
        let ev = self.tmp();
        let _ = writeln!(self.out, "    {} {ev} = {env};", ctype(&env_ty));
        let drop_env = if needs_drop_c(self.p, &env_ty) {
            self.want(Glue::Drop, &env_ty);
            format!("drop_{}(&{ev});", mangle(&env_ty))
        } else {
            String::new()
        };
        let mut body = String::new();
        if let (Some((g, gt)), Some((d, dt))) = (guard.clone(), dur) {
            let (secs, nanos) = if matches!(dt, CTy::Adt(_)) { (format!("({d}).f0"), format!("({d}).f1")) } else { (format!("({d}).secs"), format!("({d}).nanos")) };
            let (start, timed, rs, rn) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
            let _ = writeln!(self.out, "    long {start}[2]; lust_cv_start({start}); uint8_t {timed} = 0; uint64_t {rs}; uint32_t {rn};");
            let r = self.callee_call_c(&mut body, &callee, &ev, &[format!("&({g})->v")]);
            let _ = writeln!(body, "  if (!{r}) break;");
            let _ = writeln!(body, "  if (!lust_cv_left({start}, {secs}, {nanos}, &{rs}, &{rn})) {{ {timed} = 1; break; }}");
            let _ = writeln!(body, "  (void)lust_cv_wait_timeout({target}, &({g})->st, {rs}, {rn});");
            let _ = writeln!(self.out, "    for (;;) {{\n{body}    }}\n    {drop_env}");
            let wtr = self.p.tys.local_adt_of(crate::check::generics::wait_timeout_result_def()).map_or(CTy::Unit, CTy::Adt);
            let pair = CTy::Tuple(vec![gt.clone(), wtr.clone()]);
            let res = CTy::Result(Box::new(pair.clone()), Box::new(CTy::Sync(SyncTy::PoisonError, Box::new(pair.clone()))));
            self.note_held(&res);
            let (pv, t) = (self.tmp(), self.tmp());
            let _ = writeln!(self.out, "    {} {pv}; {pv}.f0 = {g}; {pv}.f1 = ({}){{ {timed} }};", ctype(&pair), ctype(&wtr));
            let f = variant_field(self.p, &res, &t, 0, 0);
            let _ = writeln!(self.out, "    {} {t}; {} {f} = {pv};", ctype(&res), disc_set(self.p, &res, &t, 0));
            return t;
        }
        if let Some((g, gt)) = guard {
            let r = self.callee_call_c(&mut body, &callee, &ev, &[format!("&({g})->v")]);
            let _ = writeln!(body, "  if (!{r}) break; lust_cv_wait({target}, &({g})->st);");
            let _ = writeln!(self.out, "    for (;;) {{\n{body}    }}\n    {drop_env}");
            let res = CTy::Result(Box::new(gt.clone()), Box::new(CTy::Sync(SyncTy::PoisonError, Box::new(gt))));
            self.note_held(&res);
            let t = self.tmp();
            let f = variant_field(self.p, &res, &t, 0, 0);
            let _ = writeln!(self.out, "    {} {t}; {} {f} = {g};", ctype(&res), disc_set(self.p, &res, &t, 0));
            return t;
        }
        let v = self.callee_call_c(&mut body, &callee, &ev, &[]);
        let after = if once { String::new() } else { drop_env.clone() };
        // panic=unwind: an init closure that panicked sets nothing. A
        // by-ref env drops first, with the exception held aside (a call
        // made while one is pending returns at once), as std drops `f`
        // inside the call; a panic in that drop aborts, as in cleanup.
        // Then the lock is empty again and the `lust_once_abort`
        // statement takes the call's unwind check (`unwind::wrap_calls`;
        // the `(void)` statements before it take none).
        let set = format!("({target})->v = {v}; lust_once_finish(&({target})->st); {after}");
        if self.p.unwind_tables {
            // Unwind tables: a guard at the top of the init block drops a by-ref env and
            // empties the lock again when the init panics (runtime `lust_once_guard_end`).
            let (dfn, denv) = if after.is_empty() {
                ("0".to_string(), "0".to_string())
            } else {
                (format!("(void (*)(void *))drop_{}", mangle(&env_ty)), format!("(void *)&{ev}"))
            };
            let g = self.tmp();
            let _ = writeln!(
                self.out,
                "    if (lust_once_begin(&({target})->st)) {{\n    struct lust_once_guard {g} __attribute__((cleanup(lust_once_guard_end))) = {{ &({target})->st, {denv}, {dfn}, 1 }};\n{body}  {g}.armed = 0; {set}\n    }} else {{ {drop_env} }}"
            );
            return format!("(&({target})->v)");
        }
        let set = if self.p.unwind {
            let env = if after.is_empty() {
                String::new()
            } else {
                let x = self.tmp();
                format!("lust_exc {x}; (void)lust_unw_take(&{x}); (void){after} if (lust_unw_mine()) (void)lust_unw_cleanup_abort(); (void)lust_unw_resume(&{x});")
            };
            format!("if (lust_unw_pending && lust_unw_mine()) {{ {env} lust_once_abort(&({target})->st); }} else {{ {set} }}")
        } else {
            set
        };
        let _ = writeln!(self.out, "    if (lust_once_begin(&({target})->st)) {{\n{body}  {set}\n    }} else {{ {drop_env} }}");
        format!("(&({target})->v)")
    }

    /// What a callable operand calls: a closure's body fn (and whether it
    /// takes its env by value), a fn item's instance, a fn pointer, or a
    /// `dyn Fn*` object. Behind one reference (`catch_unwind(&f)`,
    /// `spawn_scoped(scope, &work)`) a closure's body takes the
    /// reference value as its `&self`/`&mut self` env, so it is passed
    /// as is (the by-value form); a fn item has no value to read; a
    /// reference to a `dyn Fn*` is `Callee::DynRef`. Any other reference
    /// (to a fn pointer) is `bad_callable`.
    pub(super) fn callee_of(&self, o: &Operand) -> Callee {
        let t = self.callable_place_ty(o);
        if let TyKind::Ref(_, _, i) = self.body.tys.kind(t) {
            return match self.body.tys.kind(i) {
                TyKind::Closure(def, _) => Callee::Closure(self.p.gx.closures[&def].body_fn, true),
                TyKind::FnDef(..) => self.callee_of_ty(i),
                _ => self.callee_of_ty(t),
            };
        }
        self.callee_of_ty(t)
    }

    /// The type of the place a callable operand reads.
    pub(super) fn callable_place_ty(&self, o: &Operand) -> Ty {
        let (Operand::Move(pl) | Operand::Copy(pl)) = o else { panic!("internal: a callable argument is a place") };
        // The callable may sit in a field: a closure held in a local
        // is a field of the enclosing closure's env, and a tuple or
        // struct field holds it the same way. Walk the place at the
        // type level, as `FnGen::place` walks it at the C level.
        let tys = &self.body.tys;
        let mut t = self.body.locals[pl.local as usize].ty;
        let mut variant = 0usize;
        for pr in &pl.proj {
            t = match pr {
                Proj::Deref => match tys.kind(t) {
                    TyKind::Ref(_, _, i) | TyKind::RawPtr(_, i) => i,
                    _ => tys.smart_elem(t).unwrap_or(ERROR),
                },
                Proj::Downcast(v) => {
                    variant = *v as usize;
                    t
                }
                Proj::Field(i) => {
                    let i = *i as usize;
                    match tys.kind(t) {
                        TyKind::Tuple(ts) => tys.tys_of(ts).get(i).copied().unwrap_or(ERROR),
                        TyKind::Closure(_, a) => tys.args(a).get(i).and_then(|g| g.as_ty()).unwrap_or(ERROR),
                        _ if let Some(e) = tys.option_elem(t) => e,
                        _ if let Some((ok, err)) = tys.result_args(t) => {
                            if variant == 0 {
                                ok
                            } else {
                                err
                            }
                        }
                        _ => match tys.local_adt(t) {
                            Some(a) => self.p.adt(a).variants.get(variant).and_then(|v| v.fields.get(i)).map_or(ERROR, |f| f.ty),
                            None => ERROR,
                        },
                    }
                }
                Proj::Index(_) => match tys.kind(t) {
                    TyKind::Array(e, _) | TyKind::Slice(e) => e,
                    _ => tys.vec_elem(t).unwrap_or(ERROR),
                },
            };
        }
        t
    }

    /// The callee a closure, fn item or fn pointer type calls (also a
    /// `Box<dyn FnOnce>` and a reference to a `dyn Fn`/`FnMut`). Any
    /// other type sets `bad_callable`, which `gen_fn` reports as an
    /// error, and gives a placeholder callee.
    pub(super) fn callee_of_ty(&self, t: Ty) -> Callee {
        match self.body.tys.kind(t) {
            TyKind::Closure(def, _) => {
                let entry = &self.p.gx.closures[&def];
                Callee::Closure(entry.body_fn, entry.kind == crate::check::closure::ClosureKind::FnOnce)
            }
            TyKind::FnDef(def, fargs) => {
                let Some(f) = self.p.local_def(def.hash) else { return self.uncallable(t) };
                let gargs: Vec<GenericArg> = self.body.tys.args(fargs).to_vec();
                let f = if gargs.is_empty() { f } else { crate::check::generics::instance_for(self.p, &self.body.tys, f, &gargs).expect("internal: no fn instance") };
                Callee::Fn(f)
            }
            TyKind::FnPtr(_) => Callee::Ptr(cty(&self.body.tys, t)),
            _ if let Some(d) = self.body.tys.boxed_elem(t)
                && let Some(pr) = crate::check::object::principal_of(&self.body.tys, d)
                && pr.def == self.p.gx.lang.fn_once =>
            {
                let lang = &self.p.gx.lang;
                let out_def = lang.output_of(lang.fn_once).expect("internal: FnOnce has an Output");
                let out = self.body.tys.bindings(pr.bindings).iter().find(|(d, _)| *d == out_def).and_then(|(_, g)| g.as_ty()).unwrap_or(UNIT);
                // The Fn family's call entry is the first after the header
                // (check/closure.rs, a `dyn Fn*` call).
                Callee::DynOnce(cty(&self.body.tys, out), crate::check::object::VT_HEADER)
            }
            TyKind::Ref(_, m, d) if let Some((ret, params)) = self.dyn_fn_sig(d, m == Mut::Mut) => Callee::DynRef(ret, params),
            _ => self.uncallable(t),
        }
    }

    /// A callable type the builtin calls cannot call: records it in
    /// `bad_callable` (the first one wins; `gen_fn` reports it) and
    /// gives a placeholder callee whose code is never used.
    fn uncallable(&self, t: Ty) -> Callee {
        if self.bad_callable.get().is_none() {
            self.bad_callable.set(Some(t));
        }
        Callee::DynRef(CTy::Unit, Vec::new())
    }

    /// The C return and parameter types of `dyn Fn(..) -> R` (or of `dyn
    /// FnMut(..) -> R` when `mutable`, a `&mut` to it): the object types
    /// a reference to which is a callable (`Callee::DynRef`).
    fn dyn_fn_sig(&self, d: Ty, mutable: bool) -> Option<(CTy, Vec<CTy>)> {
        let tys = &self.body.tys;
        if !matches!(tys.kind(d), TyKind::Dyn(..)) {
            return None;
        }
        let pr = crate::check::object::principal_of(tys, d)?;
        let lang = &self.p.gx.lang;
        if pr.def != lang.fn_ && !(mutable && pr.def == lang.fn_mut) {
            return None;
        }
        let out_def = lang.output_of(lang.fn_once)?;
        let out = tys.bindings(pr.bindings).iter().find(|(d, _)| *d == out_def).and_then(|(_, g)| g.as_ty()).unwrap_or(UNIT);
        let params = match tys.args(pr.args).get(1).and_then(|g| g.as_ty()).map(|t| tys.kind(t)) {
            Some(TyKind::Tuple(ts)) => tys.tys_of(ts).iter().map(|&t| cty(tys, t)).collect(),
            _ => Vec::new(),
        };
        Some((cty(tys, out), params))
    }

    /// The C return type of a call of `callee`.
    pub(super) fn callee_ret(&self, callee: &Callee) -> CTy {
        match callee {
            Callee::Closure(f, _) | Callee::Fn(f) => cty(&self.p.tys, self.p.fn_info(*f).ret),
            Callee::Ptr(CTy::FnPtr(_, r)) => (**r).clone(),
            Callee::DynOnce(r, _) | Callee::DynRef(r, _) => r.clone(),
            Callee::Ptr(_) => unreachable!("a fn pointer type"),
        }
    }

    /// A call of `callee` (its env or fn pointer value at `env`) with the
    /// argument expressions, into a fresh variable written to `out`.
    pub(super) fn callee_call_c(&mut self, out: &mut String, callee: &Callee, env: &str, args: &[String]) -> String {
        match callee {
            Callee::Closure(f, once) => {
                let e = if *once { env.to_string() } else { format!("&{env}") };
                self.closure_call_c(out, *f, &e, args).0
            }
            Callee::Fn(f) => {
                let rt = cty(&self.p.tys, self.p.fn_info(*f).ret);
                self.note_held(&rt);
                for &t in &self.p.fn_info(*f).params {
                    self.note_held(&cty(&self.p.tys, t));
                }
                self.note_callee(*f);
                let mut args = args.to_vec();
                let pts: Vec<CTy> = self.p.fn_info(*f).params.iter().map(|&t| cty(&self.p.tys, t)).collect();
                self.spill_by_ptr(out, &pts, &mut args);
                let v = self.tmp();
                let call = self.slots.callee(self.p, *f);
                if ret_is_large(self.p, *f) {
                    let pre: String = args.iter().map(|a| format!(", {a}")).collect();
                    let _ = writeln!(out, "  {} {v}; {call}(&{v}{pre});", ctype(&rt));
                } else {
                    let _ = writeln!(out, "  {} {v} = {call}({});", ctype(&rt), args.join(", "));
                }
                v
            }
            Callee::DynOnce(r, word) => {
                self.note_held(r);
                let v = self.tmp();
                let rt = ctype(r);
                if ret_by_out(self.p, r) {
                    let _ = writeln!(out, "  {rt} {v}; ((void (*)({rt} *, void *))({env}.vt[{word}]))(&{v}, {env}.data);");
                } else {
                    let _ = writeln!(out, "  {rt} {v} = (({rt} (*)(void *))({env}.vt[{word}]))({env}.data);");
                }
                v
            }
            Callee::DynRef(r, params) => {
                self.note_held(r);
                // A zero-sized parameter is not in the entry's C
                // signature (`param_dropped`), so its argument is not
                // passed either. One the entry takes by pointer
                // (`param_by_ptr`) gets the address of a fresh copy.
                let mut kept: Vec<CTy> = Vec::new();
                let mut vals: Vec<String> = Vec::new();
                for (t, a) in params.iter().zip(args) {
                    self.note_held(t);
                    if !param_dropped(self.p, t) {
                        kept.push(t.clone());
                        vals.push(a.clone());
                    }
                }
                self.spill_by_ptr(out, &kept, &mut vals);
                let mut tys = vec!["void *".to_string()];
                tys.extend(kept.iter().map(|t| param_ctype(self.p, t)));
                let pre: String = vals.iter().map(|a| format!(", {a}")).collect();
                let (v, rt, k, tys) = (self.tmp(), ctype(r), crate::check::object::VT_HEADER, tys.join(", "));
                if ret_by_out(self.p, r) {
                    let _ = writeln!(out, "  {rt} {v}; ((void (*)({rt} *, {tys}))({env}.vt[{k}]))(&{v}, {env}.data{pre});");
                } else {
                    let _ = writeln!(out, "  {rt} {v} = (({rt} (*)({tys}))({env}.vt[{k}]))({env}.data{pre});");
                }
                v
            }
            Callee::Ptr(ft) => {
                let CTy::FnPtr(ps, r) = ft else { unreachable!("a fn pointer type") };
                let mut args = args.to_vec();
                self.spill_by_ptr(out, ps, &mut args);
                let v = self.tmp();
                if ret_by_out(self.p, r) {
                    let pre: String = args.iter().map(|a| format!(", {a}")).collect();
                    let _ = writeln!(out, "  {} {v}; {env}(&{v}{pre});", ctype(r));
                } else {
                    let _ = writeln!(out, "  {} {v} = {env}({});", ctype(r), args.join(", "));
                }
                v
            }
        }
    }

    /// The thread calls that take a closure: `thread::spawn(f)` and
    /// `scope.spawn(f)` build a packet { header, result, closure env } on
    /// the heap and a trampoline (in this fn's prelude) that calls the
    /// closure's body on the new thread and stores its result;
    /// `thread::scope(f)` calls the closure on a fresh scope here, then
    /// waits for every packet of the scope.
    pub(super) fn thread_closure_call(&mut self, op: SyncOp, ops: &[Operand], loc: &str, post: &mut Vec<String>) -> String {
        let ci = match op {
            SyncOp::ScopeSpawn | SyncOp::OnceGetOrInit | SyncOp::BuilderSpawn => 1,
            SyncOp::CondvarWaitWhile | SyncOp::BuilderSpawnScoped => 2,
            SyncOp::CondvarWaitTimeoutWhile => 3,
            _ => 0,
        };
        if op == SyncOp::AtomicFetchUpdate {
            return self.atomic_fetch_update(ops, loc, post);
        }
        if matches!(op, SyncOp::CondvarWaitWhile | SyncOp::CondvarWaitTimeoutWhile | SyncOp::OnceGetOrInit) {
            return self.closure_wait_or_init(op, ops, ci, loc, post);
        }
        // A thread's `&F` of a `Fn` closure (`spawn_scoped(scope, &work)`;
        // check/traitpath.rs allows no other reference) passes the
        // reference as the body's env (`callee_of`).
        let callee = self.callee_of(&ops[ci]);
        let once = !matches!(callee, Callee::Closure(_, false));
        let scope = match op {
            SyncOp::ScopeSpawn => self.operand(&ops[0], loc, post).0,
            SyncOp::BuilderSpawnScoped => self.operand(&ops[1], loc, post).0,
            _ => "0".into(),
        };
        let (env, env_ty) = self.operand(&ops[ci], loc, post);
        self.note_held(&env_ty);
        let ret = self.callee_ret(&callee);
        self.note_held(&ret);
        let drop_env = |this: &mut Self, out: &mut String, e: &str| {
            if !once && needs_drop_c(this.p, &env_ty) {
                this.want(Glue::Drop, &env_ty);
                let _ = writeln!(out, "  drop_{}(&{e});", mangle(&env_ty));
            }
        };
        if op == SyncOp::ThreadScope {
            let (sc, ev) = (self.tmp(), self.tmp());
            let _ = writeln!(self.out, "    lust_Scope {sc}; {sc}.live = 0; {sc}.panicked = 0; {} {ev} = {env};", ctype(&env_ty));
            let mut call = String::new();
            let v = self.callee_call_c(&mut call, &callee, &ev, &[format!("&{sc}")]);
            drop_env(self, &mut call, &ev);
            let _ = writeln!(call, "  lust_scope_wait(&{sc});");
            // A scoped thread that panicked and was not joined: the scope
            // panics after every thread ended, at its call (W-UNWIND).
            let _ = writeln!(call, "  if ({sc}.panicked) lust_panic_cstr(\"a scoped thread panicked\", {loc});");
            self.out.push_str(&call);
            return v;
        }
        // Convert packet pointers through `void *` below: a second
        // anonymous `pk` type in an initializer cast is a distinct
        // type to strict C compilers, not the declared variable's type.
        let pk = format!("struct {{ lust_JoinHdr h; {} ret; {} env; }}", ctype(&ret), ctype(&env_ty));
        let n = self.adapters;
        self.adapters += 1;
        let slot = super::names::fn_tag(self.slots.of(self.body.fn_id));
        let (run, drop) = (format!("lust_thr_{slot}_{n}"), format!("lust_thrdrop_{slot}_{n}"));
        let mut body = String::new();
        let v = self.callee_call_c(&mut body, &callee, "k->env", &[]);
        let _ = writeln!(body, "  k->ret = {v};");
        drop_env(self, &mut body, "k->env");
        let drop_ret = if needs_drop_c(self.p, &ret) {
            self.want(Glue::Drop, &ret);
            format!("drop_{}(&(({pk} *)hp)->ret);", mangle(&ret))
        } else {
            "(void)hp;".into()
        };
        let _ = writeln!(self.prelude, "static void {run}(lust_JoinHdr *hp) {{\n  {pk} *k = (void *)hp;\n{body}}}");
        let _ = writeln!(self.prelude, "static void {drop}(lust_JoinHdr *hp) {{ {drop_ret} }}");
        let h = self.tmp();
        if matches!(op, SyncOp::BuilderSpawn | SyncOp::BuilderSpawnScoped) {
            // `Builder::spawn` (TRIAGE T5) and `spawn_scoped`: the
            // io::Result of the handle, or of the errno the spawn failed
            // with (the packet and env drop then, as std drops the closure).
            let (bv, _) = self.operand(&ops[0], loc, post);
            let hk = if op == SyncOp::BuilderSpawn { SyncTy::JoinHandle } else { SyncTy::ScopedJoinHandle };
            let jh = CTy::Sync(hk, Box::new(ret.clone()));
            let err_a = AdtId(
                self.p
                    .adts
                    .iter()
                    .position(|a| self.p.interner.get(a.name).ends_with("$io$Error") && self.p.display_path(a.name) == "std::io::Error")
                    .expect("Builder::spawn only lowers when std::io is loaded") as u32,
            );
            let res = CTy::Result(Box::new(jh), Box::new(CTy::Adt(err_a)));
            self.note_held(&res);
            let (t, e2) = (self.tmp(), self.tmp());
            let okv = variant_field(self.p, &res, &t, 0, 0);
            let errv = variant_field(self.p, &res, &t, 1, 0);
            let repr_ty = self.p.adt(err_a).variants[0].fields[0].ty;
            let repr_cty = cty(&self.p.tys, repr_ty);
            let CTy::Adt(repr_a) = repr_cty else { return "0".into() };
            let os = self.p.adt(repr_a).variants.iter().position(|v| self.p.interner.get(v.name) == "Os").expect("io::Error Repr has an Os variant");
            let osf = variant_field(self.p, &repr_cty, &format!("{errv}.f0"), os, 0);
            let drop_env2 = if needs_drop_c(self.p, &env_ty) {
                self.want(Glue::Drop, &env_ty);
                format!("drop_{}(&{h}->env); ", mangle(&env_ty))
            } else {
                String::new()
            };
            let _ = writeln!(
                self.out,
                "    {pk} *{h} = (void *)lust_alloc(sizeof({pk}), _Alignof({pk})); {h}->h.run = {run}; {h}->h.drop_ret = {drop}; {h}->h.scope = {scope}; {h}->env = {env}; lust_ThreadBuilder bv_ = {bv}; int32_t {e2} = lust_thread_spawn_builder(&{h}->h, &bv_); drop_{}(&bv_); {} {t}; if ({e2} == 0) {{ {} {okv} = &{h}->h; }} else {{ {drop_env2}lust_dealloc((void*){h}, sizeof({pk}), _Alignof({pk})); {} {errv} = ({}){{ }}; {osf} = {e2}; {} }}",
                mangle(&CTy::Sync(SyncTy::ThreadBuilder, Box::new(CTy::Unit))),
                ctype(&res),
                disc_set(self.p, &res, &t, 0),
                disc_set(self.p, &res, &t, 1),
                ctype(&CTy::Adt(err_a)),
                disc_set(self.p, &repr_cty, &format!("{errv}.f0"), os),
            );
            return t;
        }
        let _ = writeln!(
            self.out,
            "    {pk} *{h} = (void *)lust_alloc(sizeof({pk}), _Alignof({pk})); {h}->h.run = {run}; {h}->h.drop_ret = {drop}; {h}->h.scope = {scope}; {h}->env = {env}; lust_thread_spawn(&{h}->h, {loc});"
        );
        format!("(&{h}->h)")
    }

    /// The lock calls: `Mutex` and `RwLock` (over the runtime's futex
    /// locks) and `PoisonError`'s accessors. A lock is poisoned only
    /// under panic=unwind (a write guard dropped by a panic); a
    /// `LockResult` is then `Err(PoisonError(..))`.
    fn lock_builtin(&mut self, op: SyncOp, vals: &[String], tys: &[CTy]) -> String {
        use SyncOp as S;
        let (k, elem) = match op {
            S::LockNew(k) | S::LockFrom(k) => (k, tys[0].clone()),
            S::LockDefault(_) | S::PoisonNew | S::SyncNew(_) => (SyncTy::PoisonError, CTy::Unit),
            _ => match deref_cty(&tys[0]) {
                CTy::Sync(k, e) => (k, *e),
                other => unreachable!("a lock operand, found {other:?}"),
            },
        };
        // `Ok(v)` of a `LockResult<V>` (a `Result<V, V>` in C).
        let ok = |this: &mut Self, v_ty: CTy, v: String| -> String {
            let res = CTy::Result(Box::new(v_ty.clone()), Box::new(CTy::Sync(SyncTy::PoisonError, Box::new(v_ty))));
            collect_types(&res, &mut this.sig_types);
            let t = this.tmp();
            let f = variant_field(this.p, &res, &t, 0, 0);
            let _ = writeln!(this.out, "    {} {t}; {} {f} = {v};", ctype(&res), disc_set(this.p, &res, &t, 0));
            t
        };
        // `Ok(v)`, or `Err(PoisonError(v))` when the lock at `lock` (a
        // pointer) is poisoned.
        let ok_or_poisoned = |this: &mut Self, v_ty: CTy, v: String, lock: &str| -> String {
            let res = CTy::Result(Box::new(v_ty.clone()), Box::new(CTy::Sync(SyncTy::PoisonError, Box::new(v_ty))));
            collect_types(&res, &mut this.sig_types);
            let t = this.tmp();
            let (f, e) = (variant_field(this.p, &res, &t, 0, 0), variant_field(this.p, &res, &t, 1, 0));
            let _ = writeln!(
                this.out,
                "    {} {t}; if (({lock})->poison & 1) {{ {} {e} = {v}; }} else {{ {} {f} = {v}; }}",
                ctype(&res),
                disc_set(this.p, &res, &t, 1),
                disc_set(this.p, &res, &t, 0)
            );
            t
        };
        match op {
            S::LockNew(_) | S::LockFrom(_) => {
                let lock = CTy::Sync(k, Box::new(elem));
                self.note_held(&lock);
                let t = self.tmp();
                let set = if k == SyncTy::OnceLock { format!(" {t}.st = 2;") } else { String::new() };
                let _ = writeln!(self.out, "    {} {t}; {} {t}.v = {};{set}", ctype(&lock), zero_c(&t), vals[0]);
                t
            }
            S::LockDefault(_) => unreachable!("LockDefault calls the Default glue"),
            S::MutexLock | S::RwLockRead | S::RwLockWrite => {
                let (gk, call) = match op {
                    S::MutexLock => (SyncTy::MutexGuard, "lust_mutex_lock"),
                    S::RwLockRead => (SyncTy::RwLockReadGuard, "lust_rw_read"),
                    _ => (SyncTy::RwLockWriteGuard, "lust_rw_write"),
                };
                let g = self.tmp();
                let guard = CTy::Sync(gk, Box::new(elem.clone()));
                let enter = if op == S::RwLockRead { String::new() } else { format!(" lust_poison_enter(&{g}->poison);") };
                let _ = writeln!(self.out, "    {} {g} = {}; {call}(&{g}->st);{enter}", ctype(&guard), vals[0]);
                ok_or_poisoned(self, guard, g.clone(), &g)
            }
            S::LockGetMut => {
                let r = CTy::Ref(Box::new(elem.clone()));
                ok_or_poisoned(self, r, format!("(&({})->v)", vals[0]), &vals[0])
            }
            S::LockIntoInner => ok_or_poisoned(self, elem, format!("({}).v", vals[0]), &format!("(&({}))", vals[0])),
            S::LockIsPoisoned => format!("((uint8_t)(({})->poison & 1))", vals[0]),
            S::LockClearPoison => format!("((({})->poison &= ~1), ((lust_Unit){{}}))", vals[0]),
            S::PoisonNew => vals[0].clone(),
            S::SyncNew(SyncTy::Barrier) => format!("((lust_Barrier){{0, 0, 0, 0, {}}})", vals[0]),
            S::SyncNew(_) => "((uint32_t)0)".into(),
            S::CondvarWait => {
                let guard = tys[1].clone();
                let _ = writeln!(self.out, "    lust_cv_wait({}, &({})->st);", vals[0], vals[1]);
                ok(self, guard, vals[1].clone())
            }
            S::CondvarWaitTimeout | S::CondvarWaitTimeoutMs => {
                // The pair value: the guard back, plus the
                // WaitTimeoutResult aggregate over the runtime's flag.
                let guard = tys[1].clone();
                let wtr = if op == S::CondvarWaitTimeoutMs {
                    CTy::Bool
                } else {
                    self.p.tys.local_adt_of(crate::check::generics::wait_timeout_result_def()).map_or(CTy::Unit, CTy::Adt)
                };
                let pair = CTy::Tuple(vec![guard.clone(), wtr.clone()]);
                self.note_held(&pair);
                let (tv, pv) = (self.tmp(), self.tmp());
                let (secs, nanos) = if op == S::CondvarWaitTimeoutMs {
                    (format!("({} / 1000)", vals[2]), format!("((uint32_t)({} % 1000) * 1000000u)", vals[2]))
                } else if matches!(tys[2], CTy::Adt(_)) {
                    (format!("({}).f0", vals[2]), format!("({}).f1", vals[2]))
                } else {
                    (format!("({}).secs", vals[2]), format!("({}).nanos", vals[2]))
                };
                let flag = format!("(uint8_t)lust_cv_wait_timeout({}, &({})->st, {secs}, {nanos})", vals[0], vals[1]);
                // The deprecated ms form's bool is the inverse:
                // true when the wait did not time out.
                let f1 = if op == S::CondvarWaitTimeoutMs { format!("(uint8_t)!({flag})") } else { format!("({}){{ {flag} }}", ctype(&wtr)) };
                let _ = writeln!(self.out, "    {} {pv}; {pv}.f0 = {}; {pv}.f1 = {f1};", ctype(&pair), vals[1]);
                let _ = tv;
                ok(self, pair, pv)
            }
            S::CondvarNotifyOne | S::CondvarNotifyAll => format!("(lust_cv_notify({}, {}), ((lust_Unit){{}}))", vals[0], u8::from(op == S::CondvarNotifyAll)),
            S::BarrierWait => format!("((uint8_t)lust_barrier_wait({}))", vals[0]),
            S::BarrierIsLeader => format!("(*{})", vals[0]),
            S::OnceGet | S::OnceGetMut => {
                let opt = CTy::Option(Box::new(CTy::Ref(Box::new(elem.clone()))));
                self.note_held(&opt);
                let t = self.tmp();
                let f = variant_field(self.p, &opt, &t, 1, 0);
                let o = &vals[0];
                let _ = writeln!(
                    self.out,
                    "    {} {t}; if (lust_once_is_done(&({o})->st)) {{ {} {f} = &({o})->v; }} else {{ {} }}",
                    ctype(&opt),
                    disc_set(self.p, &opt, &t, 1),
                    disc_set(self.p, &opt, &t, 0),
                );
                t
            }
            S::OnceSet => {
                let res = CTy::Result(Box::new(CTy::Unit), Box::new(elem.clone()));
                self.note_held(&res);
                let (t, v) = (self.tmp(), self.tmp());
                let err = variant_field(self.p, &res, &t, 1, 0);
                let o = &vals[0];
                let _ = writeln!(
                    self.out,
                    "    {} {v} = {}; {} {t}; if (lust_once_begin(&({o})->st)) {{ ({o})->v = {v}; lust_once_finish(&({o})->st); {} }} else {{ {} {err} = {v}; }}",
                    ctype(&elem),
                    vals[1],
                    ctype(&res),
                    disc_set(self.p, &res, &t, 0),
                    disc_set(self.p, &res, &t, 1),
                );
                t
            }
            S::OnceIntoInner | S::OnceTake => {
                let opt = CTy::Option(Box::new(elem.clone()));
                self.note_held(&opt);
                let (t, o) = (self.tmp(), self.tmp());
                let f = variant_field(self.p, &opt, &t, 1, 0);
                let (decl, reset) = if op == S::OnceTake {
                    (format!("{} *{o} = {};", ctype(&tys[0]).trim_end_matches('*'), vals[0]), format!(" {o}->st = 0;"))
                } else {
                    (format!("{0} {o}_v = {1}; {0} *{o} = &{o}_v;", ctype(&tys[0]), vals[0]), String::new())
                };
                let _ = writeln!(
                    self.out,
                    "    {decl} {} {t}; if ({o}->st == 2) {{ {} {f} = {o}->v;{reset} }} else {{ {} }}",
                    ctype(&opt),
                    disc_set(self.p, &opt, &t, 1),
                    disc_set(self.p, &opt, &t, 0),
                );
                t
            }
            S::PoisonIntoInner => vals[0].clone(),
            S::PoisonGetRef | S::PoisonGetMut => vals[0].clone(),
            _ => unreachable!("lock_builtin takes the lock ops"),
        }
    }

    /// `Arc` and `sync::Weak` calls, after alloc::sync: every count moves
    /// through the runtime's atomic `lust_arc_*` functions.
    fn arc_builtin(&mut self, op: SyncOp, vals: &[String], tys: &[CTy]) -> String {
        use SyncOp as S;
        // `Arc::as_ptr` of an `Arc<[T]>`, `Arc<str>` or `Arc<dyn Tr>`: the
        // owning value is the fat view of its data (tf-fatptr).
        if op == S::ArcAsPtr && super::owning_fat_ref(&tys[0]) {
            return format!("(*{})", vals[0]);
        }
        // The element type of the first operand (`Arc<T>`, `&Arc<T>`,
        // `&mut Arc<T>`, `&Weak<T>`), or the operand itself for `new`.
        let elem = match op {
            S::ArcNew => tys[0].clone(),
            S::ArcWeakNew => CTy::Unit,
            _ => match deref_cty(&tys[0]) {
                CTy::Sync(_, e) => *e,
                other => unreachable!("an Arc or Weak operand, found {other:?}"),
            },
        };
        let it = format!("RcI_{}", mangle(&elem));
        let arc = CTy::Sync(SyncTy::Arc, Box::new(elem.clone()));
        self.note_held(&arc);
        let h = |v: &str| format!("((uint64_t*){v})");
        let free = |v: &str| format!("if (lust_arc_dec(&{v}->weak)) lust_rc_free({v}, _Alignof({it}));");
        let val = |v: &str| super::rc_value(v, &elem);
        let clone_of = |this: &mut Self, src: &str| -> String {
            if is_copy_c(this.p, &elem) {
                src.to_string()
            } else {
                this.want(Glue::Clone, &elem);
                format!("clone_{}(&{src})", mangle(&elem))
            }
        };
        match op {
            S::ArcNew => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {it} *{t} = ({it}*)lust_alloc({}, _Alignof({it})); {t}->strong = 1; {t}->weak = 1; {} = {};", super::rc_size(&it, &elem), val(&t), vals[0]);
                t
            }
            S::ArcStrongCount => format!("lust_arc_load(&(*{})->strong)", vals[0]),
            S::ArcWeakCount => format!("lust_arc_weak_count({})", h(&format!("*{}", vals[0]))),
            S::ArcPtrEq | S::ArcWeakPtrEq => format!("(*{} == *{})", vals[0], vals[1]),
            // `Arc::as_ptr` (w-cinterop): the payload address.
            S::ArcAsPtr => super::rc_ptr(&format!("(*{})", vals[0]), &elem),
            S::ArcDowngrade => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {it} *{t} = *{}; lust_arc_downgrade({});", vals[0], h(&t));
                t
            }
            S::ArcGetMut => {
                let opt = CTy::Option(Box::new(CTy::Ref(Box::new(elem.clone()))));
                self.note_held(&opt);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let v = &vals[0];
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(self.out, "    if (lust_arc_is_unique({})) {{ {field} = {}; {some} }}", h(&format!("*{v}")), super::rc_ptr(&format!("(*{v})"), &elem));
                t
            }
            S::ArcMakeMut => {
                // 0: shared, clone into a fresh Arc and drop this one's
                // count; 1: Weaks only, move the value to a fresh Arc and
                // give up the implicit weak; 2: unique already.
                let v = &vals[0];
                let (st, n, old) = (self.tmp(), self.tmp(), self.tmp());
                // A fresh block's size, and the value moved or cloned into it.
                self.note_held(&elem);
                let cloned = clone_of(self, &val(&format!("(*{v})")));
                self.want(Glue::Drop, &arc);
                let am = mangle(&arc);
                let _ = writeln!(self.out, "    int {st} = lust_arc_make_mut_state({});", h(&format!("*{v}")));
                let _ = writeln!(
                    self.out,
                    "    if ({st} != 2) {{ {it} *{n} = ({it}*)lust_alloc({}, _Alignof({it})); {n}->strong = 1; {n}->weak = 1; {it} *{old} = *{v};",
                    super::rc_size(&it, &elem)
                );
                let _ = writeln!(self.out, "      if ({st} == 0) {{ {} = {cloned}; drop_{am}(&{old}); }} else {{ {} = {}; {} }}", val(&n), val(&n), val(&old), free(&old));
                let _ = writeln!(self.out, "      *{v} = {n}; }}");
                super::rc_ptr(&format!("(*{v})"), &elem)
            }
            S::ArcTryUnwrap => {
                let res = CTy::Result(Box::new(elem.clone()), Box::new(arc.clone()));
                self.note_held(&res);
                let t = self.tmp();
                let v = &vals[0];
                let ok_f = variant_field(self.p, &res, &t, 0, 0);
                let err_f = variant_field(self.p, &res, &t, 1, 0);
                let set_ok = disc_set(self.p, &res, &t, 0);
                let set_err = disc_set(self.p, &res, &t, 1);
                let _ = writeln!(self.out, "    {} {t};", ctype(&res));
                let _ = writeln!(
                    self.out,
                    "    if (lust_arc_take_unique({})) {{ {set_ok} {ok_f} = {}; {} }} else {{ {set_err} {err_f} = {v}; }}",
                    h(v),
                    val(v),
                    free(v)
                );
                t
            }
            S::ArcIntoInner | S::ArcUnwrapOrClone => {
                // The last strong Arc gives up its value; any other drops
                // its count (into_inner answers None, unwrap_or_clone a
                // clone taken before the count drops).
                let v = self.tmp();
                let _ = writeln!(self.out, "    {it} *{v} = {};", vals[0]);
                let t = self.tmp();
                if op == S::ArcIntoInner {
                    let opt = CTy::Option(Box::new(elem.clone()));
                    self.note_held(&opt);
                    let (f, some, none) = (variant_field(self.p, &opt, &t, 1, 0), disc_set(self.p, &opt, &t, 1), disc_set(self.p, &opt, &t, 0));
                    let _ = writeln!(
                        self.out,
                        "    {} {t}; if (lust_arc_dec(&{v}->strong)) {{ {f} = {}; {some} {} }} else {{ {none} }}",
                        ctype(&opt),
                        val(&v),
                        free(&v)
                    );
                } else {
                    self.note_held(&elem);
                    let c = clone_of(self, &val(&v));
                    self.want(Glue::Drop, &arc);
                    let am = mangle(&arc);
                    let _ = writeln!(
                        self.out,
                        "    {} {t}; if (lust_arc_take_unique({})) {{ {t} = {}; {} }} else {{ {t} = {c}; drop_{am}(&{v}); }}",
                        ctype(&elem),
                        h(&v),
                        val(&v),
                        free(&v)
                    );
                }
                t
            }
            S::ArcWeakNew => "((void*)~(uint64_t)0)".into(),
            S::ArcWeakUpgrade => {
                let opt = CTy::Option(Box::new(arc.clone()));
                self.note_held(&opt);
                let (t, w) = (self.tmp(), self.tmp());
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {it} *{w} = *{}; if ({w} != ({it}*)~(uint64_t)0 && lust_arc_upgrade({})) {{ {field} = {w}; {some} }}",
                    vals[0],
                    h(&w)
                );
                t
            }
            S::ArcWeakStrongCount => format!("(*{0} == (void*)~(uint64_t)0 ? (uint64_t)0 : lust_arc_load(&(*{0})->strong))", vals[0]),
            S::ArcWeakWeakCount => format!("(*{0} == (void*)~(uint64_t)0 ? (uint64_t)0 : lust_arc_weak_weak_count({1}))", vals[0], h(&format!("*{}", vals[0]))),
            _ => unreachable!("arc_builtin takes the Arc ops"),
        }
    }
}

/// zero_c: C that zeroes the lvalue `place` byte by byte. It needs no declaration, so units
/// that do not include <string.h> stay valid C for gcc 14, which rejects an implicit `memset`.
fn zero_c(place: &str) -> String {
    format!("{{ unsigned char *lust_z_ = (unsigned char *)&({place}); for (unsigned long lust_i_ = 0; lust_i_ < sizeof({place}); lust_i_++) lust_z_[lust_i_] = 0; }}")
}
