// Format strings and the Debug/Display glue over the runtime Formatter
// (src/runtime/fmt.h; W-STD-B owns this file, W-CGEN reviews).
//
// Every format argument becomes one C int expression (0 Ok, 1 Err)
// that formats a value through a `lust_Formatter *`: leaves call the
// runtime's Rust ports directly, compound types call `dbg_*` glue
// (`int dbg_<m>(lust_Formatter *f, T *p)`), which writes through the
// Debug builders exactly as Rust's derived and std impls do, so width,
// fill, `#?` pretty printing, and `x?` flags reach every leaf.
use super::*;

/// The C int expression that formats the value `v` points at (a
/// `ctype(t)*` expression) with the trait of `kind`, into the
/// Formatter pointer expression `f`. Compound types ask for glue
/// through `need`.
pub(super) fn fmt_expr(t: &CTy, kind: FmtKind, f: &str, v: &str, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let debug = kind == FmtKind::Debug;
    match t {
        // `{:p}`: the address a thin pointer holds (check admits no other).
        _ if kind == FmtKind::Pointer => format!("lust_f_pointer({f}, (const void*)(*{v}))"),
        CTy::Int(i) => int_expr(*i, kind, f, &format!("(*{v})")),
        CTy::Float(fl) => {
            let mode = match kind {
                FmtKind::Debug => 1,
                FmtKind::LowerExp => 2,
                FmtKind::UpperExp => 3,
                _ => 0,
            };
            format!("lust_f_{}({f}, *{v}, {mode})", fl.name())
        }
        CTy::Bool => format!("lust_f_bool({f}, *{v})"),
        CTy::Char if debug => format!("lust_f_dbg_char({f}, *{v})"),
        CTy::Char => format!("lust_f_char({f}, *{v})"),
        CTy::Str => str_expr(debug, f, &format!("(*{v})")),
        CTy::Ref(inner) if **inner == CTy::Str => str_expr(debug, f, &format!("(*{v})")),
        CTy::String => str_expr(debug, f, &format!("lust_string_as_str({v})")),
        // `fmt::Arguments`: core's Display and Debug both format the
        // parts through a fresh Formatter over `f`'s sink (`fmt::write`),
        // so `f`'s width, fill, and precision do not apply.
        CTy::Fmt(crate::ty::fmt::FmtTy::Arguments) => format!("lust_f_args({f}, {v})"),
        CTy::Unit => format!("lust_f_unit({f})"),
        CTy::FnPtr(..) => format!("lust_f_fnptr({f}, (const void*)(*{v}))"),
        // A raw pointer's Debug is its address (w-cinterop).
        CTy::Ptr(_) => format!("lust_f_fnptr({f}, (const void*)(*{v}))"),
        CTy::Ref(inner) | CTy::Boxed(inner) => fmt_expr(inner, kind, f, &format!("(*{v})"), need),
        // An owning fat pointer formats its pointee through the same fat value (cgen/own.rs).
        CTy::Own(_, inner) => fmt_expr(inner, kind, f, v, need),
        CTy::Rc(inner) | CTy::Sync(crate::ty::sync::SyncTy::Arc, inner) => fmt_expr(inner, kind, f, &super::rc_ptr(&format!("(*{v})"), inner), need),
        // A `RefCell` guard formats its value (W-STD-A).
        CTy::Guard(inner, _) => fmt_expr(inner, kind, f, &format!("(&(*{v})->f1)"), need),
        // A lock guard formats its value (W-THREADS).
        CTy::Sync(k, inner) if k.guard().is_some() => fmt_expr(inner, kind, f, &format!("(&(*{v})->v)"), need),
        // An atomic's Debug formats a relaxed load of its value (W-THREADS).
        CTy::Sync(k, _) if let Some(a) = k.atomic_value() => {
            let load = format!("(({})lust_at_load_{}((uint{}_t*){v}, 0, 0))", ctype(&super::sync::vt_of(a)), a.bytes(), a.bytes() * 8);
            match a {
                crate::ty::sync::AtomicVal::Bool => format!("lust_f_bool({f}, {load})"),
                crate::ty::sync::AtomicVal::Int(i) => int_expr(i, kind, f, &load),
            }
        }
        // A guard over a dyn value keeps the `dyn Any` rendering: std
        // prints `Any { .. }` for every flag set.
        CTy::DynGuard(_) | CTy::DynLock(true) if debug => format!("lust_f_write_str({f}, {})", lit("Any { .. }")),
        // A dyn value whose principal trait has a Debug or Display
        // supertrait formats through the vtable's fmt shim (the
        // concrete type's own fmt glue). With no shim the only Debug
        // dyn type left is `dyn Any`: std prints `Any { .. }`.
        CTy::Dyn | CTy::BoxDyn | CTy::RcDyn => {
            if kind == FmtKind::Display {
                let w = crate::check::object::VT_FMT_DISPLAY;
                format!("((int (*)(void *, lust_Formatter *))((*{v}).vt[{w}]))((*{v}).data, {f})")
            } else {
                let w = crate::check::object::VT_FMT_DEBUG;
                format!(
                    "((*{v}).vt[{w}] ? ((int (*)(void *, lust_Formatter *))((*{v}).vt[{w}]))((*{v}).data, {f}) : lust_f_write_str({f}, {}))",
                    lit("Any { .. }")
                )
            }
        }
        _ if debug => {
            need(Glue::Debug, t);
            format!("dbg_{}({f}, {v})", mangle(t))
        }
        _ => {
            need(Glue::Display, t);
            format!("disp_{}({f}, {v})", mangle(t))
        }
    }
}

fn str_expr(debug: bool, f: &str, s: &str) -> String {
    if debug { format!("lust_f_dbg_str({f}, {s})") } else { format!("lust_f_pad({f}, {s})") }
}

/// The mask that keeps a signed value's bits at its type width, for
/// the radix formats (`{:x}` of `-1i8` is `ff`).
fn width_mask(i: IntTy) -> &'static str {
    match i.bits() {
        8 => "0xffull",
        16 => "0xffffull",
        32 => "0xffffffffull",
        _ => "0xffffffffffffffffull",
    }
}

fn int_expr(i: IntTy, kind: FmtKind, f: &str, e: &str) -> String {
    let mode = match kind {
        FmtKind::LowerHex => 1,
        FmtKind::UpperHex => 2,
        FmtKind::Octal => 3,
        FmtKind::Binary => 4,
        _ => 0,
    };
    if mode != 0 {
        return if is128(i) {
            format!("lust_f_radix({f}, ({e}).lo, ({e}).hi, {mode})")
        } else {
            format!("lust_f_radix({f}, (uint64_t){e} & {}, 0, {mode})", width_mask(i))
        };
    }
    let dbg = if kind == FmtKind::Debug { "dbg_" } else { "" };
    if is128(i) {
        format!("lust_f_{dbg}{}({f}, {e})", if i.signed() { "i128" } else { "u128" })
    } else if i.signed() && kind == FmtKind::Debug {
        format!("lust_f_dbg_i64({f}, (int64_t){e}, {})", width_mask(i))
    } else if i.signed() {
        format!("lust_f_i64({f}, (int64_t){e})")
    } else {
        format!("lust_f_{dbg}u64({f}, (uint64_t){e})")
    }
}

/// A `lust_str` literal for `s`.
fn lit(s: &str) -> String {
    format!("(lust_str){{(uint8_t*){}, {}}}", c_string_lit(s.as_bytes()), s.len())
}

/// Builder code: one `debug_tuple`/`debug_struct` value of the fields
/// (name, value pointer expression, type), returning its result. A
/// named shape with no fields writes the bare name, as derived Debug.
fn builder_fields(name: &str, named: bool, fields: &[(String, String, CTy)], need: &mut dyn FnMut(Glue, &CTy)) -> String {
    if fields.is_empty() {
        return format!("return lust_f_write_str(f, {});", lit(name));
    }
    let (ty, kind) = if named { ("lust_DebugStruct", "dstruct") } else { ("lust_DebugTuple", "dtuple") };
    let mut s = format!("{{ {ty} b; lust_fmt_slot s; lust_Formatter *w; lust_{kind}_new(&b, f, {});", lit(name));
    for (fname, v, ft) in fields {
        let e = fmt_expr(ft, FmtKind::Debug, "w", v, need);
        let begin = if named { format!("lust_dstruct_field(&b, &s, {})", lit(fname)) } else { "lust_dtuple_field(&b, &s)".to_string() };
        let _ = write!(s, " if ((w = {begin})) lust_{kind}_field_end(&b, &s, {e});");
    }
    let _ = write!(s, " return lust_{kind}_finish(&b); }}");
    s
}

/// Builder code for `debug_list` over `n` elements at `elem(i)`.
fn builder_list(n: &str, elem: &str, et: &CTy, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let e = fmt_expr(et, FmtKind::Debug, "w", elem, need);
    format!(
        "{{ lust_DebugList b; lust_fmt_slot s; lust_Formatter *w; lust_dlist_new(&b, f, 0); for (uint64_t i = 0; i < {n}; i++) if ((w = lust_dlist_entry(&b, &s))) lust_dlist_entry_end(&b, &s, {e}); return lust_dlist_finish(&b); }}"
    )
}

/// The `CTy::Range` code of a `core::ops` range kind.
fn range_code(k: crate::ty::iter::IterKind) -> Option<u8> {
    use crate::ty::iter::IterKind as K;
    Some(match k {
        K::Range => 0,
        K::RangeFrom => 1,
        K::RangeTo => 2,
        K::RangeToInclusive => 3,
        K::RangeFull => 4,
        K::RangeInclusive => 5,
        _ => return None,
    })
}

/// The CTy that formats `t` with `{:?}`: `cty`, with each range (in the
/// shapes `check::collect::has_debug` admits a range under: references,
/// `Box`, `Option`, `Result`, `Vec`, arrays, slices, tuples) marked as a
/// `CTy::Range`, so its Debug glue writes core's range text (`1..3`)
/// where the tuple's would write `(1, 3)`.
pub(super) fn dbg_cty(tys: &impl TyIntern, t: Ty) -> CTy {
    let c = cty(tys, t);
    if !crate::check::collect::contains_range(tys, t) {
        return c;
    }
    let b = |e: Ty| Box::new(dbg_cty(tys, e));
    if let Some((k, _)) = crate::ty::iter::iter_parts(tys, t)
        && let Some(code) = range_code(k)
    {
        return CTy::Range(code, Box::new(c));
    }
    match (tys.kind(t), c) {
        (TyKind::Ref(_, _, e), CTy::Ref(_)) => CTy::Ref(b(e)),
        (TyKind::Ref(_, _, e), CTy::Slice(_)) | (TyKind::Slice(e), CTy::Slice(_)) => match tys.kind(e) {
            TyKind::Slice(el) => CTy::Slice(b(el)),
            _ => CTy::Slice(b(e)),
        },
        (TyKind::Array(e, _), CTy::Array(_, n)) => CTy::Array(b(e), n),
        (TyKind::Tuple(ts), CTy::Tuple(_)) => CTy::Tuple(tys.tys_of(ts).iter().map(|&e| dbg_cty(tys, e)).collect()),
        (_, CTy::Option(_)) => CTy::Option(b(tys.option_elem(t).unwrap_or(ERROR))),
        (_, CTy::Vec(_)) => CTy::Vec(b(tys.vec_elem(t).unwrap_or(ERROR))),
        (_, CTy::Boxed(_)) => CTy::Boxed(b(tys.boxed_elem(t).unwrap_or(ERROR))),
        (_, CTy::Result(..)) => {
            let (a, e) = tys.result_args(t).unwrap_or((ERROR, ERROR));
            CTy::Result(b(a), b(e))
        }
        (_, c) => c,
    }
}

/// The body of `dbg_<m>` for a range: core 1.99's Debug for the six
/// `core::ops` kinds formats each bound with `f` (its flags and width)
/// and writes the separators plain (`write!(f, "..")`), and
/// `RangeInclusive` adds " (exhausted)" when its flag is set.
fn range_glue_body(code: u8, inner: &CTy, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let es: Vec<CTy> = match inner {
        CTy::Tuple(es) => es.clone(),
        _ => Vec::new(),
    };
    let mut bound = |i: usize| match es.get(i) {
        Some(e) => fmt_expr(e, FmtKind::Debug, "f", &format!("(&p->f{i})"), need),
        None => "0".to_string(),
    };
    let sep = |s: &str| format!("lust_f_write_str(f, {})", lit(s));
    let steps: Vec<String> = match code {
        0 => vec![bound(0), sep(".."), bound(1)],
        1 => vec![bound(0), sep("..")],
        2 => vec![sep(".."), bound(0)],
        3 => vec![sep("..="), bound(0)],
        4 => vec![sep("..")],
        _ => vec![bound(0), sep("..="), bound(1), format!("(p->f2 ? {} : 0)", sep(" (exhausted)"))],
    };
    let mut body = String::from("  (void)p;\n");
    for s in steps {
        let _ = writeln!(body, "  if ({s}) return 1;");
    }
    body.push_str("  return 0;\n");
    body
}

/// The body of `dbg_<m>`: Rust's Debug for `t`, through the builders.
pub(super) fn debug_glue_body(p: &Program, t: &CTy, slots: &Slots, need: &mut dyn FnMut(Glue, &CTy), types: &mut Vec<CTy>) -> String {
    if let CTy::Range(code, inner) = t {
        return range_glue_body(*code, inner, need);
    }
    // A key with range marks inside (`Option<Range<T>>`): the plain type
    // for the C accessors, `t` itself for the elements' glue.
    let lt = crate::cgen::strip_ranges(t);
    // `PhantomData<T>`: core's `write!(f, "PhantomData<{}>", type_name::<T>())`,
    // which ignores the width and fill. Check admits only a `T` lust can
    // name (`collect::phantom_debug_text`).
    if let CTy::Adt(a) = t
        && p.is_phantom_adt(*a)
    {
        let text = p.tys.full_adt_ty(*a).and_then(|ty| crate::check::collect::phantom_debug_text(p, &p.tys, ty));
        let text = text.expect("internal: Debug glue for a PhantomData whose type name check did not admit");
        return format!("  (void)p;\n  return lust_f_write_str(f, {});\n", lit(&text));
    }
    // `NonZero<T>` prints its integer, with no wrapper name.
    if let CTy::Adt(a) = t
        && p.def_of_adt(*a) == crate::ty::nonzero_def()
    {
        let inner = cty(&p.tys, p.adt(*a).variants[0].fields[0].ty);
        return format!("  return {};\n", fmt_expr(&inner, FmtKind::Debug, "f", "(&p->f0)", need));
    }
    // `TrySendError`'s Debug hides the value: `TrySendError::Full(..)`.
    if let CTy::Adt(a) = t
        && p.def_of_adt(*a) == crate::check::generics::try_send_error_def()
    {
        let disc = disc_call(p, t, "p");
        return format!("  return lust_f_write_str(f, ({disc}) ? {} : {});\n", lit("TrySendError::Disconnected(..)"), lit("TrySendError::Full(..)"));
    }
    // `TryLockError`'s Debug is a str's Debug: `"Poisoned(..)"` or
    // `"WouldBlock"`, quoted.
    if let CTy::Adt(a) = t
        && p.def_of_adt(*a) == crate::check::generics::try_lock_error_def()
    {
        let disc = disc_call(p, t, "p");
        return format!("  return lust_f_dbg_str(f, ({disc}) ? {} : {});\n", lit("WouldBlock"), lit("Poisoned(..)"));
    }
    // `Cow<B>` prints the `B` it derefs to, with no variant name.
    if let Some((rb, decl)) = cow_view(p, t, "p", "v_") {
        return format!("  {decl}\n  return {};\n", fmt_expr(&rb, FmtKind::Debug, "f", "(&v_)", need));
    }
    let disc_p = disc_call(p, &lt, "p");
    let mut body = String::new();
    match t {
        CTy::Option(inner) => {
            let some = builder_fields("Some", false, &[(String::new(), format!("&{}", variant_field(p, &lt, "(*p)", 1, 0)), (**inner).clone())], need);
            let _ = writeln!(body, "  if ({disc_p}) {some}\n  return lust_f_write_str(f, {});", lit("None"));
        }
        CTy::Result(a, b) => {
            let ok = builder_fields("Ok", false, &[(String::new(), format!("&{}", variant_field(p, &lt, "(*p)", 0, 0)), (**a).clone())], need);
            let err = builder_fields("Err", false, &[(String::new(), format!("&{}", variant_field(p, &lt, "(*p)", 1, 0)), (**b).clone())], need);
            let _ = writeln!(body, "  if ({disc_p}) {err}\n  {ok}");
        }
        CTy::Tuple(es) => {
            let fields: Vec<(String, String, CTy)> = es.iter().enumerate().map(|(i, e)| (String::new(), format!("&p->f{i}"), e.clone())).collect();
            // `()` has its own Debug (`f.pad("()")`); a tuple of fields
            // is a nameless debug_tuple.
            if fields.is_empty() {
                body.push_str("  return lust_f_unit(f);\n");
            } else {
                let _ = writeln!(body, "  {}", builder_fields("", false, &fields, need));
            }
        }
        CTy::Array(e, n) => {
            let _ = writeln!(body, "  {}", builder_list(&n.to_string(), "&p->v[i]", e, need));
        }
        CTy::Slice(e) | CTy::BoxSlice(e) => {
            let _ = writeln!(body, "  {}", builder_list("p->len", "&p->ptr[i]", e, need));
        }
        CTy::Vec(e) => {
            let et = ctype(e);
            let _ = writeln!(body, "  {}", builder_list("p->len", &format!("&(({et}*)p->ptr)[i]"), e, need));
        }
        // core's derived Debug of `option::IntoIter { inner: Item { opt } }`
        // and `result::IntoIter { inner }`.
        CTy::OptIter(result, e) => {
            let ot = CTy::Option(e.clone());
            let field = if *result {
                format!("lust_dstruct_field_end(&b, &s, {});", fmt_expr(&ot, FmtKind::Debug, "w", "(&p->f0)", need))
            } else {
                let opt = fmt_expr(&ot, FmtKind::Debug, "w2", "(&p->f0)", need);
                format!(
                    "{{ lust_DebugStruct b2; lust_fmt_slot s2; lust_Formatter *w2; lust_dstruct_new(&b2, w, {}); if ((w2 = lust_dstruct_field(&b2, &s2, {}))) lust_dstruct_field_end(&b2, &s2, {opt}); lust_dstruct_field_end(&b, &s, lust_dstruct_finish(&b2)); }}",
                    lit("Item"),
                    lit("opt")
                )
            };
            let _ = writeln!(
                body,
                "  {{ lust_DebugStruct b; lust_fmt_slot s; lust_Formatter *w; lust_dstruct_new(&b, f, {}); if ((w = lust_dstruct_field(&b, &s, {}))) {field} return lust_dstruct_finish(&b); }}",
                lit("IntoIter"),
                lit("inner")
            );
        }
        // alloc's `vec::IntoIter` Debug:
        // `f.debug_tuple("IntoIter").field(&self.as_slice()).finish()`.
        CTy::VecIter(e) => {
            let et = ctype(e);
            let st = CTy::Slice(e.clone());
            types.push(st.clone());
            let _ = writeln!(body, "  {} s_; s_.ptr = (({et}*)p->ptr) + p->front; s_.len = p->len - p->front;", ctype(&st));
            let _ = writeln!(body, "  {}", builder_fields("IntoIter", false, &[(String::new(), "(&s_)".to_string(), st)], need));
        }
        CTy::Unsized(a, _) => {
            let call = user_fmt_call(p, *a, FmtKind::Debug, slots, "*p", types).expect("an unsized newtype formatted with {:?} has a written Debug");
            let _ = writeln!(body, "  {call}");
        }
        // std's cell types (W-STD-A): `Weak` prints `(Weak)`, `Cell<T:
        // Copy>` and `RefCell` a struct of their value.
        CTy::Weak(_) => {
            let _ = writeln!(body, "  return lust_f_write_str(f, {});", lit("(Weak)"));
        }
        // `thread::AccessError` (W-TLS): a fieldless debug_struct, so
        // width and `#` do not change it.
        CTy::AccessError => {
            let _ = writeln!(body, "  (void)p; return lust_f_write_str(f, {});", lit("AccessError"));
        }
        // `ExitCode(unix_exit_status(N))`: std's tuple of the unix
        // status tuple, through the builders (W-STD-A).
        CTy::ExitCode => {
            let n = int_expr(IntTy::U8, FmtKind::Debug, "w2", "(*p)");
            let _ = writeln!(
                body,
                "  {{ lust_DebugTuple b; lust_fmt_slot s; lust_Formatter *w; lust_dtuple_new(&b, f, {}); if ((w = lust_dtuple_field(&b, &s))) {{ lust_DebugTuple b2; lust_fmt_slot s2; lust_Formatter *w2; lust_dtuple_new(&b2, w, {}); if ((w2 = lust_dtuple_field(&b2, &s2))) lust_dtuple_field_end(&b2, &s2, {n}); lust_dtuple_field_end(&b, &s, lust_dtuple_finish(&b2)); }} return lust_dtuple_finish(&b); }}",
                lit("ExitCode"),
                lit("unix_exit_status")
            );
        }
        CTy::Cell(e) => {
            // Rust formats a copy (`self.get()`), so a Debug impl that
            // sets the cell does not change what it prints.
            let _ = writeln!(body, "  {} v = *p;", ctype(e));
            let _ = writeln!(body, "  {}", builder_fields("Cell", true, &[("value".to_string(), "(&v)".to_string(), (**e).clone())], need));
        }
        // RefCell: Rust's try_borrow. A failed one prints `<borrowed>`;
        // else the shared borrow is held while the value formats, so a
        // Debug impl that borrows the cell mutably panics.
        CTy::RefCell(e) => {
            let _ = writeln!(
                body,
                "  if (p->f0 < 0 || p->f0 == 0x7fffffffffffffffLL) {{ lust_DebugStruct b; lust_fmt_slot s; lust_Formatter *w; lust_dstruct_new(&b, f, {}); if ((w = lust_dstruct_field(&b, &s, {}))) lust_dstruct_field_end(&b, &s, lust_f_write_str(w, {})); return lust_dstruct_finish(&b); }}",
                lit("RefCell"),
                lit("value"),
                lit("<borrowed>")
            );
            let v = fmt_expr(e, FmtKind::Debug, "w", "(&p->f1)", need);
            let _ = writeln!(
                body,
                "  {{ lust_DebugStruct b; lust_fmt_slot s; lust_Formatter *w; int r; p->f0++; lust_dstruct_new(&b, f, {}); if ((w = lust_dstruct_field(&b, &s, {}))) lust_dstruct_field_end(&b, &s, {v}); r = lust_dstruct_finish(&b); p->f0--; return r; }}",
                lit("RefCell"),
                lit("value")
            );
        }
        // HashMap: debug_map of (k, v) in bucket order; HashSet:
        // debug_set (std's Debug impls iterate the table).
        CTy::Hash(crate::ty::hash::HashTy::HashMap, a) => {
            let et = ctype(&CTy::Tuple(vec![a[0].clone(), a[1].clone()]));
            let ke = fmt_expr(&a[0], FmtKind::Debug, "w", &format!("(&(({et}*)e)->f0)"), need);
            let ve = fmt_expr(&a[1], FmtKind::Debug, "w", &format!("(&(({et}*)e)->f1)"), need);
            let _ = writeln!(
                body,
                "  {{ lust_DebugMap b; lust_fmt_slot s; lust_Formatter *w; lust_hash_iter it; void *e; lust_dmap_new(&b, f); lust_hash_iter_init(&it, &p->t);\n    while ((e = lust_hash_iter_next(&it, 0))) {{ if ((w = lust_dmap_key(&b, &s, 0))) lust_dmap_key_end(&b, &s, {ke}); if ((w = lust_dmap_value(&b, &s, 0))) lust_dmap_value_end(&b, &s, {ve}); }}\n    return lust_dmap_finish(&b, 0); }}"
            );
        }
        // std: `f.debug_struct("RandomState").finish_non_exhaustive()`.
        CTy::Hash(crate::ty::hash::HashTy::RandomState, _) => {
            let _ = writeln!(
                body,
                "  {{ lust_DebugStruct d; lust_dstruct_new(&d, f, {}); return lust_dstruct_finish_ne(&d); }}",
                lit("RandomState")
            );
        }
        CTy::Hash(crate::ty::hash::HashTy::HashSet, a) => {
            let et = ctype(&a[0]);
            let ee = fmt_expr(&a[0], FmtKind::Debug, "w", &format!("(({et}*)e)"), need);
            let _ = writeln!(
                body,
                "  {{ lust_DebugList b; lust_fmt_slot s; lust_Formatter *w; lust_hash_iter it; void *e; lust_dlist_new(&b, f, 1); lust_hash_iter_init(&it, &p->t);\n    while ((e = lust_hash_iter_next(&it, 0))) {{ if ((w = lust_dlist_entry(&b, &s))) lust_dlist_entry_end(&b, &s, {ee}); }}\n    return lust_dlist_finish(&b); }}"
            );
        }
        CTy::Adt(a) => {
            if let Some(call) = user_fmt_call(p, *a, FmtKind::Debug, slots, "p", types) {
                let _ = writeln!(body, "  {call}");
            } else {
                let adt = p.adt(*a);
                // The field print is the derive's. An Adt with no derive
                // and no written impl here is a checker gap: print
                // nothing rather than a guess (rule zero).
                assert!(p.derives_of(*a).debug, "internal: Debug glue for `{}`, which has no derive and no selected impl", p.display_name(adt.name));
                let variant = |v: &Variant, access: &dyn Fn(usize) -> String, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                    // The struct's pseudo-variant carries the flat name;
                    // rustc prints the source name.
                    let name = p.display_name(v.name);
                    let fields: Vec<(String, String, CTy)> =
                        v.fields.iter().enumerate().map(|(fi, fd)| (p.name(fd.name).to_string(), format!("&{}", access(fi)), dbg_cty(&p.tys, fd.ty))).collect();
                    builder_fields(name, v.shape == VariantShape::Named, &fields, need)
                };
                if adt.is_enum {
                    let _ = writeln!(body, "  switch ({disc_p}) {{");
                    for (vi, v) in adt.variants.iter().enumerate() {
                        let b = variant(v, &|fi| format!("p->u.v{vi}.f{fi}"), need);
                        let _ = writeln!(body, "  case {vi}: {b}");
                    }
                    body.push_str("  }\n  return 0;\n");
                } else {
                    let b = variant(&adt.variants[0], &|fi| format!("p->f{fi}"), need);
                    let _ = writeln!(body, "  {b}");
                }
            }
        }
        _ => {
            let e = fmt_expr(t, FmtKind::Debug, "f", "p", need);
            let _ = writeln!(body, "  return {e};");
        }
    }
    body
}

/// The body of `disp_<m>`: only types with a user Display impl reach
/// Display glue (every other Display type is a leaf in `fmt_expr`).
pub(super) fn display_glue_body(p: &Program, t: &CTy, slots: &Slots, need: &mut dyn FnMut(Glue, &CTy), types: &mut Vec<CTy>) -> String {
    // `NonZero<T>` displays its integer, with no wrapper name.
    if let CTy::Adt(a) = t
        && p.def_of_adt(*a) == crate::ty::nonzero_def()
    {
        let inner = cty(&p.tys, p.adt(*a).variants[0].fields[0].ty);
        return format!("  return {};\n", fmt_expr(&inner, FmtKind::Display, "f", "(&p->f0)", need));
    }
    // `TrySendError`'s Display is std's per-variant text.
    if let CTy::Adt(a) = t
        && p.def_of_adt(*a) == crate::check::generics::try_send_error_def()
    {
        let disc = disc_call(p, t, "p");
        return format!("  return lust_f_pad(f, ({disc}) ? {} : {});\n", lit("sending on a closed channel"), lit("sending on a full channel"));
    }
    // `TryLockError`'s Display is std's per-variant text.
    if let CTy::Adt(a) = t
        && p.def_of_adt(*a) == crate::check::generics::try_lock_error_def()
    {
        let disc = disc_call(p, t, "p");
        return format!(
            "  return lust_f_pad(f, ({disc}) ? {} : {});\n",
            lit("try_lock failed because the operation would block"),
            lit("poisoned lock: another task failed inside")
        );
    }
    // `Cow<B>` displays the `B` it derefs to (W-STD-B).
    if let Some((rb, decl)) = cow_view(p, t, "p", "v_") {
        return format!("  {decl}\n  return {};\n", fmt_expr(&rb, FmtKind::Display, "f", "(&v_)", need));
    }
    match t {
        // `impl Display for fmt::Error`: str Display of core's text.
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::fmt_error_def()) == Some(*a) => {
            format!("  return lust_f_pad(f, {});\n", lit("an error occurred when formatting an argument"))
        }
        // RefCell's try errors (W-STD-B): str Display of core's text.
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::borrow_error_def()) == Some(*a) => {
            format!("  (void)p; return lust_f_pad(f, {});\n", lit("RefCell already mutably borrowed"))
        }
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::borrow_mut_error_def()) == Some(*a) => {
            format!("  (void)p; return lust_f_pad(f, {});\n", lit("RefCell already borrowed"))
        }
        // core's conversion errors (fx-tryfrom): str Display of
        // core's texts, the kind's for `TryFromIntError`.
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::try_from_int_error_def()) == Some(*a) => {
            let kct = p.tys.local_adt_of(crate::check::generics::int_error_kind_def()).map_or(CTy::Unit, CTy::Adt);
            format!(
                "  return {} == 2 ? lust_f_pad(f, {}) : lust_f_pad(f, {});\n",
                disc_call(p, &kct, "(&(*p).f0)"),
                lit("number too large to fit in target type"),
                lit("number too small to fit in target type")
            )
        }
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::char_try_from_error_def()) == Some(*a) => {
            format!("  (void)p; return lust_f_pad(f, {});\n", lit("converted integer out of range for `char`"))
        }
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::try_from_char_error_def()) == Some(*a) => {
            format!("  (void)p; return lust_f_pad(f, {});\n", lit("unicode code point out of range"))
        }
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::try_from_slice_error_def()) == Some(*a) => {
            format!("  (void)p; return lust_f_pad(f, {});\n", lit("could not convert slice to array"))
        }
        // core's parse errors (tf-str): str Display of core's texts,
        // by the kind field's discriminant.
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::parse_int_error_def()) == Some(*a) => {
            let kct = p.tys.local_adt_of(crate::check::generics::int_error_kind_def()).map_or(CTy::Unit, CTy::Adt);
            let d = disc_call(p, &kct, "(&(*p).f0)");
            format!(
                "  return lust_f_pad(f, {d} == 0 ? {} : {d} == 1 ? {} : {d} == 2 ? {} : {d} == 3 ? {} : {});\n",
                lit("cannot parse integer from empty string"),
                lit("invalid digit found in string"),
                lit("number too large to fit in target type"),
                lit("number too small to fit in target type"),
                lit("number would be zero for non-zero type")
            )
        }
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::parse_float_error_def()) == Some(*a) => {
            let kct = p.tys.local_adt_of(crate::check::generics::float_error_kind_def()).map_or(CTy::Unit, CTy::Adt);
            format!(
                "  return {} ? lust_f_pad(f, {}) : lust_f_pad(f, {});\n",
                disc_call(p, &kct, "(&(*p).f0)"),
                lit("invalid float literal"),
                lit("cannot parse float from empty string")
            )
        }
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::parse_bool_error_def()) == Some(*a) => {
            format!("  (void)p; return lust_f_pad(f, {});\n", lit("provided string was not `true` or `false`"))
        }
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::parse_char_error_def()) == Some(*a) => {
            let kct = p.tys.local_adt_of(crate::check::generics::char_error_kind_def()).map_or(CTy::Unit, CTy::Adt);
            format!(
                "  return {} ? lust_f_pad(f, {}) : lust_f_pad(f, {});\n",
                disc_call(p, &kct, "(&(*p).f0)"),
                lit("too many characters in string"),
                lit("cannot parse char from empty string")
            )
        }
        // mpsc's errors (W-THREADS): str Display of std's text.
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::recv_error_def()) == Some(*a) => {
            format!("  (void)p; return lust_f_pad(f, {});\n", lit("receiving on a closed channel"))
        }
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::try_recv_error_def()) == Some(*a) => format!(
            "  return {} ? lust_f_pad(f, {}) : lust_f_pad(f, {});\n",
            disc_call(p, t, "p"),
            lit("receiving on a closed channel"),
            lit("receiving on an empty channel")
        ),
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::recv_timeout_error_def()) == Some(*a) => format!(
            "  return {} ? lust_f_pad(f, {}) : lust_f_pad(f, {});\n",
            disc_call(p, t, "p"),
            lit("channel is empty and sending half is closed"),
            lit("timed out waiting on channel")
        ),
        // std's UTF-8 errors (W-STD-A): their Display writes with
        // `write!`, a fresh default Formatter over the same sink, so the
        // caller's width and fill do not apply.
        // `std::panic::Location` (check/caller.rs): std's
        // `write!(f, "{}:{}:{}", file, line, col)`.
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::location_def()) == Some(*a) => format!(
            "  lust_Formatter g; lust_f_init(&g, f->buf);\n  return lust_f_write_str(&g, (*p).f0) || lust_f_write_str(&g, {c}) || lust_f_u64(&g, (*p).f1) || lust_f_write_str(&g, {c}) || lust_f_u64(&g, (*p).f2);\n",
            c = lit(":")
        ),
        CTy::Adt(_) if let Some(u) = utf8_error_part(p, t, "(*p)") => {
            let opt = CTy::Option(Box::new(CTy::Int(IntTy::U8)));
            types.push(opt.clone());
            let o = format!("{u}.f1");
            format!(
                "  lust_Formatter g; lust_f_init(&g, f->buf);\n  if ({}) return lust_f_write_str(&g, {}) || lust_f_u64(&g, {}) || lust_f_write_str(&g, {}) || lust_f_u64(&g, {u}.f0);\n  return lust_f_write_str(&g, {}) || lust_f_u64(&g, {u}.f0);\n",
                disc_call(p, &opt, &format!("&{o}")),
                lit("invalid utf-8 sequence of "),
                variant_field(p, &opt, &o, 1, 0),
                lit(" bytes from index "),
                lit("incomplete utf-8 byte sequence from index ")
            )
        }
        CTy::Adt(a) => match user_fmt_call(p, *a, FmtKind::Display, slots, "p", types) {
            Some(call) => format!("  {call}\n"),
            None => "  abort();\n".to_string(),
        },
        // `thread::AccessError` (W-TLS): std pads its text.
        CTy::AccessError => format!("  (void)p; return lust_f_pad(f, {});\n", lit("already destroyed")),
        _ => "  abort();\n".to_string(),
    }
}

/// The call of a user fmt impl's method instance for Adt `a`, as a C
/// statement that returns 0 or 1, when the program has one. `this` is
/// the `&self` argument: the glue's `p`, or `*p` for an unsized
/// newtype, whose reference is its fat value. Adds the method's
/// signature types to `types` (see `glue_callee`).
fn user_fmt_call(p: &Program, a: AdtId, kind: FmtKind, slots: &Slots, this: &str, types: &mut Vec<CTy>) -> Option<String> {
    let m = *p.gx.fmt_methods.get(&(a, kind as u8))?;
    let ret = cty(&p.tys, p.fn_info(m).ret);
    let rt = ctype(&ret);
    let callee = glue_callee(p, slots, m, types);
    let disc = disc_call(p, &ret, "(&r)");
    // An unsized newtype's receiver is its fat value (`*p`): a fresh copy when the method
    // takes it by pointer (`param_by_ptr`).
    let mut pre = String::new();
    let this = super::glue_args(p, m, &[this, "f"], &mut pre).swap_remove(0);
    let pre = pre.replace('\n', "");
    Some(if ret_is_large(p, m) {
        format!("{{{pre} {rt} r; {callee}(&r, {this}, f); return {disc} != 0; }}")
    } else {
        format!("{{{pre} {rt} r = {callee}({this}, f); return {disc} != 0; }}")
    })
}

impl FnGen<'_, '_> {
    /// Release C: the count and lock blocks `fmt_expr` opens on its way to the formatted
    /// value (an `Rc`'s `->v`, a guard's `->f1`) must be defined in the unit
    /// (`type_decls_with`); what they point at is only named.
    pub(super) fn note_fmt_opens(&mut self, t: &CTy, kind: FmtKind) {
        if !names::release() || kind == FmtKind::Pointer {
            return;
        }
        match t {
            CTy::Ref(inner) | CTy::Boxed(inner) | CTy::Own(_, inner) => self.note_fmt_opens(inner, kind),
            // An `Arc` shares the `Rc` count block (`RcI_<T>`).
            CTy::Rc(inner) | CTy::Sync(crate::ty::sync::SyncTy::Arc, inner) => {
                self.sig_types.insert(CTy::Rc(inner.clone()));
                collect_types(t, &mut self.sig_named);
                self.note_fmt_opens(inner, kind);
            }
            CTy::Guard(inner, _) => {
                self.sig_types.insert(CTy::RefCell(inner.clone()));
                collect_types(t, &mut self.sig_named);
                self.note_fmt_opens(inner, kind);
            }
            CTy::Sync(k, inner) if k.guard().is_some() => {
                collect_types(t, &mut self.sig_types);
                self.note_fmt_opens(inner, kind);
            }
            _ => {}
        }
    }

    /// True for an unsized format argument (`str`, `[T]`, or an unsized
    /// newtype such as `Path`): it arrives as its fat value, and the
    /// formatters take a pointer to it.
    fn unsized_arg(&self, ty: crate::ty::Ty) -> bool {
        match self.body.tys.kind(ty) {
            TyKind::Str | TyKind::Slice(_) => true,
            TyKind::Adt(d, _) => self.body.tys.unsized_field(d).is_some(),
            _ => false,
        }
    }
}

/// True when formatting a value of `t` can fail (reach a user fmt impl
/// that may return Err): it holds an Adt somewhere. Other values only
/// write to a String sink, which never fails.
fn may_fail(t: &CTy) -> bool {
    match t {
        CTy::Adt(_) => true,
        CTy::Vec(e) | CTy::Option(e) | CTy::Ref(e) | CTy::Array(e, _) | CTy::Slice(e) | CTy::Boxed(e) | CTy::Rc(e) => may_fail(e),
        CTy::Sync(crate::ty::sync::SyncTy::Arc, e) => may_fail(e),
        // The locks and their guards format their value (W-THREADS).
        CTy::Sync(k, e) if k.is_cell_struct() || k.guard().is_some() => may_fail(e),
        // std's cells and boxed slices (W-STD-A) format their contents.
        CTy::Cell(e) | CTy::RefCell(e) | CTy::Guard(e, _) | CTy::BoxSlice(e) | CTy::Own(_, e) => may_fail(e),
        CTy::Unsized(..) => true,
        CTy::Result(a, b) => may_fail(a) || may_fail(b),
        CTy::Tuple(es) => es.iter().any(may_fail),
        CTy::Range(_, e) => may_fail(e),
        // A `format_args!` value formats its own arguments.
        CTy::Fmt(crate::ty::fmt::FmtTy::Arguments) => true,
        _ => false,
    }
}

/// The runtime option words of one spec: (fill, align, flags, width,
/// precision), as `lust_f_set` takes them.
fn spec_words(spec: &FmtSpec) -> (u32, u32, u32, u32, u32) {
    let align = match spec.align {
        b'<' => 0,
        b'>' => 1,
        b'^' => 2,
        _ => 3,
    };
    let mut flags = 0u32;
    if spec.plus {
        flags |= 1;
    }
    if spec.minus {
        flags |= 2;
    }
    if spec.alt {
        flags |= 4;
    }
    if spec.zero {
        flags |= 8;
    }
    match spec.debug_hex {
        1 => flags |= 16,
        2 => flags |= 32,
        _ => {}
    }
    if spec.width.is_some() {
        flags |= 64;
    }
    if spec.precision.is_some() {
        flags |= 128;
    }
    let fill = if spec.fill == 0 { ' ' as u32 } else { spec.fill };
    (fill, align, flags, spec.width.unwrap_or(0), spec.precision.unwrap_or(0))
}

/// `fmt::Arguments::estimated_capacity` for these parts (the literal
/// pieces' length, doubled when there are arguments; nothing when the
/// string starts with an argument and the pieces are short). With no
/// arguments the text is `as_str()`, copied with exact capacity.
pub(super) fn estimated_capacity(parts: &[FmtPart]) -> usize {
    let pieces: usize = parts.iter().map(|p| if let FmtPart::Lit(s) = p { s.len() } else { 0 }).sum();
    let args = parts.iter().any(|p| matches!(p, FmtPart::Arg { .. }));
    if !args {
        pieces
    } else if matches!(parts.first(), Some(FmtPart::Arg { .. })) && pieces < 16 {
        0
    } else {
        pieces.saturating_mul(2)
    }
}

impl FnGen<'_, '_> {
    /// `spec_words` with a width or precision taken from an argument:
    /// C expressions that read the `&usize` operand when the placeholder
    /// is formatted (`lust_f_count` panics past `u16::MAX`, as std does).
    fn spec_words_dyn(
        &mut self,
        spec: &FmtSpec,
        width: &Option<Operand>,
        prec: &Option<Operand>,
        env: Option<Local>,
        loc: &str,
        post: &mut Vec<String>,
    ) -> (u32, u32, u32, String, String) {
        let (fill, align, mut flags, w, p) = spec_words(spec);
        let mut count = |this: &mut Self, c: &Option<Operand>, lit: u32, flag: u32| match c {
            Some(c) => {
                flags |= flag;
                let (v, _) = this.fmt_operand(c, env, loc, post);
                format!("lust_f_count(*{v}, {loc})")
            }
            None => lit.to_string(),
        };
        let w = count(self, width, w, 64);
        let p = count(self, prec, p, 128);
        (fill, align, flags, w, p)
    }

    /// Emits the formatting of `parts` into a new String temp (with
    /// Rust's capacity for `format!`) and returns the temp's name. A
    /// fmt impl error panics with the message of `what` (see
    /// `lust_fmt_failed`; 4 is a panic message, where std ignores the
    /// error).
    pub(super) fn format(&mut self, parts: &[FmtPart], loc: &str, post: &mut Vec<String>, what: u32) -> String {
        let s = self.tmp();
        let cap = estimated_capacity(parts);
        let _ = writeln!(self.out, "    lust_String {s} = lust_string_with_capacity({cap});");
        if !parts.iter().any(|p| matches!(p, FmtPart::Arg { .. })) {
            for part in parts {
                if let FmtPart::Lit(text) = part
                    && !text.is_empty()
                {
                    let _ = writeln!(self.out, "    lust_string_push_bytes(&{s}, {}, {});", c_string_lit(text.as_bytes()), text.len());
                }
            }
            return s;
        }
        let _ = writeln!(self.out, "    lust_sink {s}k; lust_sink_string(&{s}k, &{s}); lust_Formatter {s}f; lust_f_init(&{s}f, &{s}k); int {s}e = 0;");
        if self.format_parts(parts, &s, None, loc, post) && what != 4 {
            let _ = writeln!(self.out, "    if ({s}e) lust_fmt_failed({what}, {loc});");
        }
        s
    }

    /// `Rvalue::FormatArgs`: the C value of an `fmt::Arguments`
    /// (`lust_Arguments`, src/runtime/fmt.h). With arguments it is this
    /// site's formatter fn, emitted ahead of the function, and the
    /// pointer to the arguments temporary that `env` borrows. The fn
    /// writes the parts through a fresh Formatter over the sink it is
    /// given (core's `fmt::write`), reading each argument reference
    /// from the temporary, so the arguments format at each use, as in
    /// rustc. With no argument it is the literal text. The value also
    /// keeps `estimated_capacity`, for `to_string`.
    pub(super) fn format_args_value(&mut self, env: Option<&Operand>, parts: &[FmtPart], loc: &str, post: &mut Vec<String>) -> String {
        let cap = estimated_capacity(parts);
        let Some(env) = env else {
            let text: String = parts.iter().map(|p| if let FmtPart::Lit(s) = p { s.as_str() } else { "" }).collect();
            return format!("((lust_Arguments){{ NULL, NULL, {}, {}, {cap} }})", c_string_lit(text.as_bytes()), text.len());
        };
        let (e, et) = self.operand(env, loc, post);
        let CTy::Ref(env_ct) = et else { unreachable!("a format_args! env is a reference") };
        let Some(env_local) = parts.iter().find_map(|p| match p {
            FmtPart::Arg { value: Operand::Copy(pl), .. } => Some(pl.local),
            _ => None,
        }) else {
            unreachable!("a format_args! value with an env has an argument")
        };
        // rustc converts each width and precision argument when the
        // value is made (`Argument::from_usize`): an out-of-range count
        // panics here, at the `format_args!` site, and never in the
        // formatter fn (which has no caller location to report).
        for part in parts {
            if let FmtPart::Arg { width, prec, .. } = part {
                for c in width.iter().chain(prec) {
                    let Operand::Copy(pl) = c else { unreachable!("a count reads the env") };
                    let [Proj::Field(i)] = pl.proj[..] else { unreachable!("a count reads the env") };
                    let _ = writeln!(self.out, "    lust_f_count(*({e})->f{i}, {loc});");
                }
            }
        }
        let name = format!("lust_fa_{}_{}", super::names::fn_tag(self.slots.of(self.body.fn_id)), self.adapters);
        self.adapters += 1;
        let outer = std::mem::take(&mut self.out);
        let _ = writeln!(self.out, "    const {} *env = (const {0} *)envp;", ctype(&env_ct));
        let _ = writeln!(self.out, "    lust_Formatter xf; lust_f_init(&xf, k); int xe = 0;");
        let mut inner_post = Vec::new();
        self.format_parts(parts, "x", Some(env_local), "0u", &mut inner_post);
        debug_assert!(inner_post.is_empty(), "argument reads leave no cleanup");
        let body = std::mem::replace(&mut self.out, outer);
        let _ = writeln!(self.prelude, "static int {name}(const void *envp, lust_sink *k) {{\n{body}    return xe;\n}}");
        format!("((lust_Arguments){{ {name}, (const void *){e}, NULL, 0, {cap} }})")
    }

    /// An argument operand of format parts. Inside a `format_args!`
    /// formatter fn (`env` is the arguments temporary's local) a read
    /// of the temporary's field `i` is `env->f<i>` through the fn's
    /// `env` pointer; every other operand is the function's own.
    fn fmt_operand(&mut self, o: &Operand, env: Option<Local>, loc: &str, post: &mut Vec<String>) -> (String, CTy) {
        if let (Some(l), Operand::Copy(pl)) = (env, o)
            && pl.local == l
            && let [Proj::Field(i)] = pl.proj[..]
        {
            let CTy::Tuple(es) = &self.local_cty[l as usize] else { unreachable!("a format_args! env is a tuple") };
            return (format!("(env->f{i})"), es[i as usize].clone());
        }
        self.operand(o, loc, post)
    }

    /// Emits `print!` (`eprint!` with `stderr`; `newline` for the `ln`
    /// forms). As in std, each piece goes to the locked stream as it is
    /// formatted: a print inside a fmt impl comes out between the pieces
    /// around it, and the pieces before a fmt impl error stay written.
    pub(super) fn print(&mut self, parts: &[FmtPart], newline: bool, stderr: bool, loc: &str, post: &mut Vec<String>) {
        let s = self.tmp();
        let fd = u8::from(stderr);
        let _ = writeln!(self.out, "    lust_sink {s}k; lust_print_begin(&{s}k, {fd}); lust_Formatter {s}f; lust_f_init(&{s}f, &{s}k); int {s}e = 0;");
        let fallible = self.format_parts(parts, &s, None, loc, post);
        let guard = if fallible { format!("if (!{s}e) ") } else { String::new() };
        if newline {
            let _ = writeln!(self.out, "    {guard}lust_f_write(&{s}f, \"\\n\", 1);");
        }
        // panic=unwind: unlock first, so a panic that leaves for cleanup
        // does not keep the stream locked.
        if self.p.unwind {
            let _ = writeln!(self.out, "    lust_print_end({fd});");
        }
        if fallible {
            let _ = writeln!(self.out, "    if ({s}e) lust_fmt_failed(2, {loc});");
        }
        if !self.p.unwind {
            let _ = writeln!(self.out, "    lust_print_end({fd});");
        }
    }

    /// Emits the writes of `parts` through the Formatter `{s}f` the
    /// caller set up, with its error flag `{s}e`: after a fmt impl
    /// error nothing more is written, as `fmt::write` stops. Returns
    /// whether any argument's impl can fail. `env`: see `fmt_operand`.
    fn format_parts(&mut self, parts: &[FmtPart], s: &str, env: Option<Local>, loc: &str, post: &mut Vec<String>) -> bool {
        let mut fallible = false;
        for part in parts {
            match part {
                FmtPart::Lit(text) => {
                    if !text.is_empty() {
                        let guard = if fallible { format!("if (!{s}e) ") } else { String::new() };
                        let _ = writeln!(self.out, "    {guard}lust_f_write(&{s}f, {}, {});", c_string_lit(text.as_bytes()), text.len());
                    }
                }
                FmtPart::Arg { value, ty, spec, width, prec, .. } => {
                    let (v, vt) = self.fmt_operand(value, env, loc, post);
                    let t = if spec.kind == FmtKind::Debug { dbg_cty(&self.body.tys, *ty) } else { cty(&self.body.tys, *ty) };
                    // An unsized `str` or `[T]` argument arrives as its
                    // fat value; the formatters take a pointer to it.
                    let ptr = if self.unsized_arg(*ty) {
                        let tmp = self.tmp();
                        let _ = writeln!(self.out, "    {} {tmp} = {v};", ctype(&vt));
                        format!("(&{tmp})")
                    } else {
                        v
                    };
                    let mut want: Vec<(Glue, CTy)> = Vec::new();
                    self.note_fmt_opens(&crate::cgen::strip_ranges(&t), spec.kind);
                    let e = fmt_expr(&t, spec.kind, &format!("(&{s}f)"), &ptr, &mut |g, t| want.push((g, t.clone())));
                    for (g, t) in want {
                        self.want(g, &t);
                    }
                    let (fill, align, flags, width, prec) = self.spec_words_dyn(spec, width, prec, env, loc, post);
                    let guard = if fallible { format!("if (!{s}e) ") } else { String::new() };
                    let _ = writeln!(self.out, "    {guard}{{ lust_f_set(&{s}f, {fill}, {align}, {flags}, {width}, {prec}); {s}e = {e}; }}");
                    fallible |= may_fail(&t);
                    // panic=unwind: a fmt impl that panicked stops the
                    // formatting like an error, and a print still writes
                    // the pieces before it (Rust writes as it formats).
                    if self.p.unwind && may_fail(&t) {
                        let _ = writeln!(self.out, "    if (lust_unw_pending && lust_unw_mine()) {s}e = 1;");
                    }
                }
            }
        }
        fallible
    }
}

/// `$signed::MAX.ilog10() + 1`: the capacity Rust's signed `to_string`
/// specialization starts from (one more for a negative value).
fn signed_digits(i: IntTy) -> u32 {
    match i.bits() {
        8 => 3,
        16 => 5,
        32 => 10,
        64 => 19,
        _ => 39,
    }
}

impl FnGen<'_, '_> {
    /// `ToString::to_string` of the value `v` points at (Self type `t`),
    /// with Rust 1.99's capacity rules: signed integers preallocate
    /// their widest decimal form, unsigned integers, `char`, `bool`,
    /// `String`, `str`, and `&str` copy exactly, and everything else
    /// writes Display into `String::new()`.
    pub(super) fn to_string_value(&mut self, t: &CTy, v: &str, loc: &str) -> String {
        let s = self.tmp();
        match t {
            CTy::String => {
                let _ = writeln!(self.out, "    lust_String {s} = lust_string_from(lust_string_as_str({v}));");
                return s;
            }
            // `fmt::Arguments::to_string` in alloc (`fmt::format`): a
            // String of `estimated_capacity` that the parts format into,
            // or `as_str()` copied for literal-only text.
            CTy::Fmt(crate::ty::fmt::FmtTy::Arguments) => {
                let _ = writeln!(self.out, "    lust_String {s} = lust_args_to_string({v});");
                return s;
            }
            CTy::Str => {
                let _ = writeln!(self.out, "    lust_String {s} = lust_string_from(*{v});");
                return s;
            }
            CTy::Ref(inner) if **inner == CTy::Str => {
                let _ = writeln!(self.out, "    lust_String {s} = lust_string_from(*{v});");
                return s;
            }
            _ => {}
        }
        let exact = matches!(t, CTy::Int(i) if !i.signed()) || matches!(t, CTy::Char | CTy::Bool);
        let start = match t {
            CTy::Int(i) if i.signed() => {
                let neg = if is128(*i) { format!("((int64_t)(*{v}).hi < 0)") } else { format!("(*{v} < 0)") };
                let n = signed_digits(*i);
                format!("lust_string_with_capacity({neg} ? {} : {n})", n + 1)
            }
            _ => "lust_string_new()".to_string(),
        };
        let buf = if exact { self.tmp() } else { s.clone() };
        let mut want: Vec<(Glue, CTy)> = Vec::new();
        let e = fmt_expr(t, FmtKind::Display, &format!("(&{buf}f)"), v, &mut |g, t| want.push((g, t.clone())));
        for (g, t) in want {
            self.want(g, &t);
        }
        let _ = writeln!(
            self.out,
            "    lust_String {buf} = {start}; lust_sink {buf}k; lust_sink_string(&{buf}k, &{buf}); lust_Formatter {buf}f; lust_f_init(&{buf}f, &{buf}k);"
        );
        if may_fail(t) {
            let _ = writeln!(self.out, "    if ({e}) lust_fmt_failed(1, {loc});");
        } else {
            let _ = writeln!(self.out, "    (void)({e});");
        }
        if exact {
            let _ = writeln!(self.out, "    lust_String {s} = lust_string_from(lust_string_as_str(&{buf})); lust_string_drop(&{buf});");
        }
        s
    }
}

/// The C form of `fmt::Result` (`Result<(), fmt::Error>`).
fn fmt_result_cty(p: &Program) -> CTy {
    let e = p.tys.local_adt_of(crate::check::generics::fmt_error_def()).map_or(CTy::Unit, CTy::Adt);
    CTy::Result(Box::new(CTy::Unit), Box::new(e))
}

impl FnGen<'_, '_> {
    /// The `fmt::Result` value of a runtime result int.
    fn fmt_result_of(&mut self, e: &str) -> String {
        let t = fmt_result_cty(self.p);
        let err_ty = match &t {
            CTy::Result(_, b) => (**b).clone(),
            _ => CTy::Unit,
        };
        let ok = self.make_variant(&t, 0, &["((lust_Unit){})".to_string()]);
        let err = self.make_variant(&t, 1, &[zero_lit(self.p, &err_ty)]);
        format!("(({e}) ? {err} : {ok})")
    }

    /// The `io::Result<()>` value of a stream write whose first write
    /// error's errno is the C int `code` (0 for none): `Ok(())`, or
    /// `Err` of an `io::Error` with its `Os` representation, as
    /// `Error::from_raw_os_error` builds it in the std source.
    fn io_result_of(&mut self, code: &str) -> String {
        let p = self.p;
        let err_a = AdtId(
            p.adts
                .iter()
                .position(|a| {
                    p.interner.get(a.name).ends_with("$io$Error") && p.display_path(a.name) == "std::io::Error"
                })
                .expect("a stream write_fmt only lowers when std::io is loaded") as u32,
        );
        let repr_ty = p.adt(err_a).variants[0].fields[0].ty;
        let repr_cty = cty(&p.tys, repr_ty);
        let CTy::Adt(repr_a) = repr_cty else { return "0".into() };
        let os = p.adt(repr_a).variants.iter().position(|v| p.interner.get(v.name) == "Os").expect("io::Error's Repr has an Os variant");
        let t = CTy::Result(Box::new(CTy::Unit), Box::new(CTy::Adt(err_a)));
        let repr = self.make_variant(&repr_cty, os, &[code.to_string()]);
        let err = self.make_variant(&t, 1, &[format!("(({}){{ .f0 = {repr} }})", super::names::adt(err_a))]);
        let ok = self.make_variant(&t, 0, &["((lust_Unit){})".to_string()]);
        format!("(({code}) ? {err} : {ok})")
    }

    /// One `core::fmt` builtin call (check/fmt.rs) over the operand
    /// values and C types, or None for every other builtin.
    pub(super) fn fmt_builtin(&mut self, b: Builtin, vals: &[String], tys: &[CTy], loc: &str) -> Option<String> {
        use crate::ty::fmt::FmtTy as F;
        use Builtin as B;
        let opt_usize = CTy::Option(Box::new(CTy::Int(IntTy::Usize)));
        let recv_kind = match tys.first() {
            Some(CTy::Ref(inner)) => match &**inner {
                CTy::Fmt(k) => Some(*k),
                _ => None,
            },
            _ => None,
        };
        let mut want: Vec<(Glue, CTy)> = Vec::new();
        let value = |i: usize, f: &str, want: &mut Vec<(Glue, CTy)>| -> String {
            let inner = match &tys[i] {
                CTy::Ref(inner) => (**inner).clone(),
                t => t.clone(),
            };
            fmt_expr(&inner, FmtKind::Debug, f, &vals[i], &mut |g, t| want.push((g, t.clone())))
        };
        let on_string = matches!(tys.first(), Some(CTy::Ref(inner)) if **inner == CTy::String);
        let out = match b {
            // `<String as fmt::Write>`: append, always Ok.
            B::FmtWriteStr if on_string => self.fmt_result_of(&format!("(lust_string_push_str({}, {}), 0)", vals[0], vals[1])),
            B::FmtWriteChar if on_string => self.fmt_result_of(&format!("(lust_string_push_char({}, {}), 0)", vals[0], vals[1])),
            B::FmtWriteStr => self.fmt_result_of(&format!("lust_f_write_str({}, {})", vals[0], vals[1])),
            B::FmtWriteChar => self.fmt_result_of(&format!("lust_f_write_char({}, {})", vals[0], vals[1])),
            B::FmtPad => self.fmt_result_of(&format!("lust_f_pad({}, {})", vals[0], vals[1])),
            B::FmtPadIntegral => self.fmt_result_of(&format!("lust_f_pad_integral({}, {}, {}, {})", vals[0], vals[1], vals[2], vals[3])),
            B::FmtWidth | B::FmtPrecision => {
                let (flag, field) = if b == B::FmtWidth { ("LUST_FLAG_WIDTH", "width") } else { ("LUST_FLAG_PREC", "prec") };
                let some = self.make_variant(&opt_usize, 1, &[format!("(uint64_t){}->{field}", vals[0])]);
                let none = self.make_variant(&opt_usize, 0, &[]);
                format!("(({}->flags & {flag}) ? {some} : {none})", vals[0])
            }
            B::FmtFill => format!("({}->fill)", vals[0]),
            B::FmtAlternate => format!("(({}->flags & LUST_FLAG_ALT) != 0)", vals[0]),
            B::FmtSignPlus => format!("(({}->flags & LUST_FLAG_PLUS) != 0)", vals[0]),
            B::FmtSignMinus => format!("(({}->flags & LUST_FLAG_MINUS) != 0)", vals[0]),
            B::FmtSignAwareZeroPad => format!("(({}->flags & LUST_FLAG_ZERO) != 0)", vals[0]),
            B::FmtDebugStruct | B::FmtDebugTuple | B::FmtDebugList | B::FmtDebugSet | B::FmtDebugMap => {
                let t = self.tmp();
                let line = match b {
                    B::FmtDebugStruct => format!("lust_DebugStruct {t}; lust_dstruct_new(&{t}, {}, {});", vals[0], vals[1]),
                    B::FmtDebugTuple => format!("lust_DebugTuple {t}; lust_dtuple_new(&{t}, {}, {});", vals[0], vals[1]),
                    B::FmtDebugList => format!("lust_DebugList {t}; lust_dlist_new(&{t}, {}, 0);", vals[0]),
                    B::FmtDebugSet => format!("lust_DebugList {t}; lust_dlist_new(&{t}, {}, 1);", vals[0]),
                    _ => format!("lust_DebugMap {t}; lust_dmap_new(&{t}, {});", vals[0]),
                };
                let _ = writeln!(self.out, "    {line}");
                t
            }
            B::DsField => {
                let e = value(2, "w", &mut want);
                let _ = writeln!(
                    self.out,
                    "    {{ lust_fmt_slot s; lust_Formatter *w = lust_dstruct_field({}, &s, {}); if (w) lust_dstruct_field_end({}, &s, {e}); }}",
                    vals[0], vals[1], vals[0]
                );
                vals[0].clone()
            }
            B::DtField | B::DlEntry => {
                let e = value(1, "w", &mut want);
                let (begin, end) = if b == B::DtField { ("dtuple_field", "dtuple_field_end") } else { ("dlist_entry", "dlist_entry_end") };
                let _ = writeln!(
                    self.out,
                    "    {{ lust_fmt_slot s; lust_Formatter *w = lust_{begin}({}, &s); if (w) lust_{end}({}, &s, {e}); }}",
                    vals[0], vals[0]
                );
                vals[0].clone()
            }
            B::DmKey | B::DmValue | B::DmEntry => {
                let steps: &[(usize, &str)] = match b {
                    B::DmKey => &[(1, "key")],
                    B::DmValue => &[(1, "value")],
                    _ => &[(1, "key"), (2, "value")],
                };
                for &(i, which) in steps {
                    let e = value(i, "w", &mut want);
                    let _ = writeln!(
                        self.out,
                        "    {{ lust_fmt_slot s; lust_Formatter *w = lust_dmap_{which}({}, &s, {loc}); if (w) lust_dmap_{which}_end({}, &s, {e}); }}",
                        vals[0], vals[0]
                    );
                }
                vals[0].clone()
            }
            B::FmtFinish | B::FmtFinishNonExhaustive => {
                let ne = if b == B::FmtFinishNonExhaustive { "_ne" } else { "" };
                let call = match recv_kind {
                    Some(F::DebugStruct) => format!("lust_dstruct_finish{ne}({})", vals[0]),
                    Some(F::DebugTuple) => format!("lust_dtuple_finish{ne}({})", vals[0]),
                    Some(F::DebugMap) => format!("lust_dmap_finish{ne}({}, {loc})", vals[0]),
                    _ => format!("lust_dlist_finish{ne}({})", vals[0]),
                };
                self.fmt_result_of(&call)
            }
            // `Cow` (check/cow.rs, W-STD-B).
            B::CowDeref => {
                let cow = match &tys[0] {
                    CTy::Ref(inner) => (**inner).clone(),
                    t => t.clone(),
                };
                cow_view_expr(self.p, &cow, &vals[0]).map(|(_, e)| e)?
            }
            B::CowIntoOwned | B::CowToMut => {
                let (cow, ptr) = match &tys[0] {
                    CTy::Ref(inner) => ((**inner).clone(), vals[0].clone()),
                    t => {
                        let c = self.tmp();
                        let _ = writeln!(self.out, "    {} {c} = {};", ctype(t), vals[0]);
                        (t.clone(), format!("(&{c})"))
                    }
                };
                let CTy::Adt(a) = &cow else { return None };
                let oc = cty(&self.p.tys, self.p.adt(*a).variants[1].fields[0].ty);
                let (rb, view) = cow_view_expr(self.p, &cow, &ptr)?;
                let disc = disc_call(self.p, &cow, &ptr);
                let f1 = variant_field(self.p, &cow, &format!("(*{ptr})"), 1, 0);
                let o = self.tmp();
                // `<B as ToOwned>::to_owned` of the borrowed view: str to
                // an exact String, `[T]` to an exact Vec of clones.
                let want_clone = |this: &mut Self, t: &CTy, x: &str| -> String {
                    if is_copy_c(this.p, t) {
                        x.to_string()
                    } else {
                        this.want(Glue::Clone, t);
                        format!("clone_{}(&{x})", mangle(t))
                    }
                };
                let to_owned = match &rb {
                    CTy::Ref(inner) if **inner == CTy::Str => format!("    {} {o} = lust_string_from({view});", ctype(&oc)),
                    CTy::Slice(e) => {
                        let et = ctype(e);
                        let c = want_clone(self, e, "s_.ptr[i_]");
                        format!(
                            "    {} {o}; {{ {} s_ = {view}; {o} = lust_vec_with_capacity(s_.len, sizeof({et}), _Alignof({et})); for (uint64_t i_ = 0; i_ < s_.len; i_++) (({et}*){o}.ptr)[i_] = {c}; {o}.len = s_.len; }}",
                            ctype(&oc),
                            ctype(&rb)
                        )
                    }
                    // An unsized slice newtype (Path, OsStr): an exact
                    // Vec of the view's elements, wrapped in the Owned
                    // type's single-field struct chain (PathBuf).
                    CTy::Unsized(..) => {
                        let owned_ty = self.p.adt(*a).variants[1].fields[0].ty;
                        let Some((suffix, e)) = owned_vec_path(self.p, owned_ty) else { return None };
                        let ec = cty(&self.p.tys, e);
                        let et = ctype(&ec);
                        let c = want_clone(self, &ec, "s_.ptr[i_]");
                        format!(
                            "    {} {o} = {{0}}; {{ {} s_ = {view}; lust_Vec v_ = lust_vec_with_capacity(s_.len, sizeof({et}), _Alignof({et})); for (uint64_t i_ = 0; i_ < s_.len; i_++) (({et}*)v_.ptr)[i_] = {c}; v_.len = s_.len; {o}{suffix} = v_; }}",
                            ctype(&oc),
                            ctype(&rb)
                        )
                    }
                    CTy::Ref(inner) => {
                        let c = want_clone(self, inner, &format!("(*{view})"));
                        format!("    {} {o} = {c};", ctype(&oc))
                    }
                    _ => return None,
                };
                if b == B::CowIntoOwned {
                    let r = self.tmp();
                    let _ = writeln!(self.out, "    {} {r}; if ({disc}) {r} = {f1}; else {{\n{to_owned}\n    {r} = {o}; }}", ctype(&oc));
                    r
                } else {
                    let set = self.make_variant(&cow, 1, &[o.clone()]);
                    let _ = writeln!(self.out, "    if (!({disc})) {{\n{to_owned}\n    *{ptr} = {set}; }}");
                    format!("(&{f1})")
                }
            }
            // `Cow<str>` addition (check/cow.rs): make the Cow owned
            // as `to_mut` does, then push the right-hand `&str`. The
            // by-value form's Cow operand was copied into the temp
            // `ptr` names, exactly as `CowIntoOwned` copies it.
            B::CowAddStr | B::CowAddAssignStr => {
                let (cow, ptr, val) = match &tys[0] {
                    CTy::Ref(inner) => ((**inner).clone(), vals[0].clone(), String::new()),
                    t => {
                        let c = self.tmp();
                        let _ = writeln!(self.out, "    {} {c} = {};", ctype(t), vals[0]);
                        (t.clone(), format!("(&{c})"), c)
                    }
                };
                let CTy::Adt(a) = &cow else { return None };
                let oc = cty(&self.p.tys, self.p.adt(*a).variants[1].fields[0].ty);
                let (_, view) = cow_view_expr(self.p, &cow, &ptr)?;
                let disc = disc_call(self.p, &cow, &ptr);
                let f1 = variant_field(self.p, &cow, &format!("(*{ptr})"), 1, 0);
                let o = self.tmp();
                let set = self.make_variant(&cow, 1, &[o.clone()]);
                // A Cow right side (the method forms; lowering of the
                // operators already took its view) reads through its
                // own view and drops after the push, as the consumed
                // argument of std's `Add<Cow>` impl does.
                let (rhs, drop_rhs) = match &tys[1] {
                    CTy::Adt(_) => {
                        let rc = self.tmp();
                        let _ = writeln!(self.out, "    {} {rc} = {};", ctype(&tys[1]), vals[1]);
                        let (_, v) = cow_view_expr(self.p, &tys[1].clone(), &format!("(&{rc})"))?;
                        self.want(Glue::Drop, &tys[1].clone());
                        (v, format!("\n    drop_{}(&{rc});", mangle(&tys[1])))
                    }
                    _ => (vals[1].clone(), String::new()),
                };
                let _ = writeln!(
                    self.out,
                    "    if (!({disc})) {{\n    {} {o} = lust_string_from({view});\n    *{ptr} = {set}; }}\n    lust_string_push_str(&{f1}, {rhs});{drop_rhs}",
                    ctype(&oc)
                );
                if b == B::CowAddStr { val } else { "((lust_Unit){})".into() }
            }
            // Conversion trait methods (check/convert.rs).
            B::ConvIdent => vals[0].clone(),
            B::ConvDeref => format!("(*{})", vals[0]),
            B::ConvRcInner => format!("(&(*{})->v)", vals[0]),
            B::ConvStrBytes | B::ConvArraySlice => {
                let (elem, ptr, len) = match &tys[0] {
                    CTy::Ref(inner) => match &**inner {
                        CTy::Array(e, n) => ((**e).clone(), format!("{}->v", vals[0]), format!("((uint64_t){n})")),
                        _ => (CTy::Int(IntTy::U8), format!("{}.ptr", vals[0]), format!("{}.len", vals[0])),
                    },
                    _ => (CTy::Int(IntTy::U8), format!("{}.ptr", vals[0]), format!("{}.len", vals[0])),
                };
                let sl = CTy::Slice(Box::new(elem));
                let t = self.tmp();
                let _ = writeln!(self.out, "    {} {t} = {{ {ptr}, {len} }};", ctype(&sl));
                t
            }
            B::FmtCallDisplay | B::FmtCallDebug => {
                let kind = if b == B::FmtCallDisplay { FmtKind::Display } else { FmtKind::Debug };
                // `fmt_expr` reads its value through a pointer. A sized
                // receiver is `&T` (a C pointer); a `&str` (`Ref(Str)`,
                // C `lust_str`), `&[T]`, or `&dyn` receiver is the fat
                // value itself, so it goes through a pointer to a copy
                // (`s.as_str().fmt(f)`).
                let (inner, v) = match &tys[0] {
                    CTy::Ref(inner) if **inner != CTy::Str => ((**inner).clone(), vals[0].clone()),
                    t => {
                        let tmp = self.tmp();
                        let _ = writeln!(self.out, "    {} {tmp} = {};", ctype(t), vals[0]);
                        (t.clone(), format!("(&{tmp})"))
                    }
                };
                let e = fmt_expr(&inner, kind, &vals[1], &v, &mut |g, t| want.push((g, t.clone())));
                self.fmt_result_of(&e)
            }
            _ => return None,
        };
        for (g, t) in want {
            self.want(g, &t);
        }
        Some(out)
    }

    /// `Rvalue::WriteFmt`: the parts into `dst`'s sink through a fresh
    /// Formatter (Formatter::write_fmt and `<String as fmt::Write>`),
    /// stopping at the first error; the value is the `fmt::Result`.
    /// With `stream` set the sink is the locked stdout or stderr
    /// stream (the `dst` operand only carries the borrow): a write
    /// error becomes the `io::Result`'s `Err`, and a fmt impl error
    /// with no write error panics as std's `io::Write::write_fmt` does.
    pub(super) fn write_fmt(&mut self, dst: &Operand, parts: &[FmtPart], stream: Option<bool>, loc: &str, post: &mut Vec<String>) -> String {
        let (d, dt) = self.operand(dst, loc, post);
        let s = self.tmp();
        if let Some(stderr) = stream {
            let fd = u8::from(stderr);
            let _ = writeln!(self.out, "    lust_io_sink {s}k; lust_io_begin(&{s}k, {fd}); lust_Formatter {s}f; lust_f_init(&{s}f, &{s}k.base); int {s}e = 0;");
        } else if matches!(&dt, CTy::Ref(inner) if **inner == CTy::String) {
            let _ = writeln!(self.out, "    lust_sink {s}k; lust_sink_string(&{s}k, {d}); lust_Formatter {s}f; lust_f_init(&{s}f, &{s}k); int {s}e = 0;");
        } else {
            let _ = writeln!(self.out, "    lust_Formatter {s}f; lust_f_init(&{s}f, ({d})->buf); int {s}e = 0;");
        }
        for part in parts {
            match part {
                FmtPart::Lit(text) => {
                    if !text.is_empty() {
                        let _ = writeln!(self.out, "    if (!{s}e) {s}e = lust_f_write(&{s}f, {}, {});", c_string_lit(text.as_bytes()), text.len());
                    }
                }
                FmtPart::Arg { value, ty, spec, width, prec, .. } => {
                    let (v, vt) = self.operand(value, loc, post);
                    let t = if spec.kind == FmtKind::Debug { dbg_cty(&self.body.tys, *ty) } else { cty(&self.body.tys, *ty) };
                    let ptr = if self.unsized_arg(*ty) {
                        let tmp = self.tmp();
                        let _ = writeln!(self.out, "    {} {tmp} = {v};", ctype(&vt));
                        format!("(&{tmp})")
                    } else {
                        v
                    };
                    let mut want: Vec<(Glue, CTy)> = Vec::new();
                    self.note_fmt_opens(&crate::cgen::strip_ranges(&t), spec.kind);
                    let e = fmt_expr(&t, spec.kind, &format!("(&{s}f)"), &ptr, &mut |g, t| want.push((g, t.clone())));
                    for (g, t) in want {
                        self.want(g, &t);
                    }
                    let (fill, align, flags, width, prec) = self.spec_words_dyn(spec, width, prec, None, loc, post);
                    let _ = writeln!(self.out, "    if (!{s}e) {{ lust_f_set(&{s}f, {fill}, {align}, {flags}, {width}, {prec}); {s}e = {e}; }}");
                    // As in `print`: a fmt impl that panicked under
                    // unwind stops the formatting; the parts before it
                    // are already on the stream.
                    if stream.is_some() && self.p.unwind && may_fail(&t) {
                        let _ = writeln!(self.out, "    if (lust_unw_pending && lust_unw_mine()) {s}e = 1;");
                    }
                }
            }
        }
        if let Some(stderr) = stream {
            let fd = u8::from(stderr);
            // Unlock before the fmt-error panic under unwind, as
            // `print` does, so cleanup does not keep the stream locked.
            if self.p.unwind {
                let _ = writeln!(self.out, "    lust_print_end({fd});");
            }
            let _ = writeln!(self.out, "    if ({s}e && !{s}k.err) lust_fmt_failed(2, {loc});");
            if !self.p.unwind {
                let _ = writeln!(self.out, "    lust_print_end({fd});");
            }
            // Read the sink's errno once, for the result value.
            let r = self.tmp();
            let _ = writeln!(self.out, "    int32_t {r}e = {s}k.err;");
            return self.io_result_of(&format!("{r}e"));
        }
        self.fmt_result_of(&format!("{s}e"))
    }
}

/// For a `Cow<'a, B>` instance Adt (W-STD-B): the C type of `&B` and a
/// declaration of local `name` holding the `&B` the Cow at `ptr` (a
/// pointer) derefs to: the borrowed reference, or a view of the owned
/// value (`String` as `str`, `Vec<T>` as `[T]`, `T` by address). None
/// for every other type.
pub(super) fn cow_view(p: &Program, t: &CTy, ptr: &str, name: &str) -> Option<(CTy, String)> {
    let (rb, e) = cow_view_expr(p, t, ptr)?;
    Some((rb.clone(), format!("{} {name} = {e};", ctype(&rb))))
}

/// The slice element type an unsized slice newtype (`Path`,
/// `OsStr`, a user `struct S { inner: [T] }`) lays out as, following
/// its unsized fields. None for any other type, and for a generic
/// newtype whose field still names a parameter.
pub(super) fn unsized_slice_elem(p: &Program, mut b: Ty) -> Option<Ty> {
    loop {
        match p.tys.kind(b) {
            TyKind::Slice(e) => return Some(e),
            TyKind::Adt(d, a) => {
                let mut f = p.tys.unsized_field(d)?;
                if !p.tys.args(a).is_empty() && p.tys.flags(f).contains_param() {
                    f = p.tys.unsized_inst_field(d, a)?;
                }
                b = f;
            }
            _ => return None,
        }
    }
}

/// The C field path from an Owned value to the `Vec` buffer at its
/// single-field struct chain's end (`PathBuf` to its `OsString`'s
/// Vec: ".f0.f0"), and that Vec's element type. None when the chain
/// is not single-field structs over one Vec.
pub(super) fn owned_vec_path(p: &Program, mut t: Ty) -> Option<(String, Ty)> {
    let mut path = String::new();
    loop {
        if let Some(e) = p.tys.vec_elem(t) {
            return Some((path, e));
        }
        let a = p.tys.local_adt(t)?;
        let adt = p.adt(a);
        if adt.is_enum || adt.variants[0].fields.len() != 1 {
            return None;
        }
        let f = adt.variants[0].fields[0].ty;
        let (_, args) = p.tys.adt_parts(t)?;
        if !p.tys.args(args).is_empty() && p.tys.flags(f).contains_param() {
            return None;
        }
        path.push_str(".f0");
        t = f;
    }
}

/// `cow_view` as one C expression (the `&B` value).
pub(super) fn cow_view_expr(p: &Program, t: &CTy, ptr: &str) -> Option<(CTy, String)> {
    let CTy::Adt(a) = t else { return None };
    let (def, args) = p.gx.adt_instance_of.get(a.0 as usize).copied().flatten()?;
    if def != crate::check::generics::cow_def() {
        return None;
    }
    let b = p.tys.args(args).iter().find_map(|g| g.as_ty())?;
    let (f0, f1) = (variant_field(p, t, &format!("(*{ptr})"), 0, 0), variant_field(p, t, &format!("(*{ptr})"), 1, 0));
    let (rb, owned) = match p.tys.kind(b) {
        TyKind::Str => (CTy::Ref(Box::new(CTy::Str)), format!("lust_string_as_str(&{f1})")),
        TyKind::Slice(e) => {
            let sl = CTy::Slice(Box::new(cty(&p.tys, e)));
            let view = format!("(({}){{ ({}*)({f1}).ptr, ({f1}).len }})", ctype(&sl), ctype(&cty(&p.tys, e)));
            (sl, view)
        }
        // An unsized slice newtype (`Cow<Path>`, `Cow<OsStr>`): the
        // view's C type is the newtype's fat slice form, and the
        // owned value views as the slice of its Vec buffer.
        TyKind::Adt(..) if unsized_slice_elem(p, b).is_some() => {
            let e = unsized_slice_elem(p, b)?;
            let rb = cty(&p.tys, b);
            let owned_ty = p.adt(*a).variants[1].fields[0].ty;
            let (suffix, _) = owned_vec_path(p, owned_ty)?;
            let buf = format!("{f1}{suffix}");
            let view = format!("(({}){{ ({}*)({buf}).ptr, ({buf}).len }})", ctype(&rb), ctype(&cty(&p.tys, e)));
            (rb, view)
        }
        _ => (CTy::Ref(Box::new(cty(&p.tys, b))), format!("(&{f1})")),
    };
    let disc = disc_call(p, t, ptr);
    Some((rb, format!("(({disc}) ? {owned} : {f0})")))
}
