// The hashed collections in C (W-STD-B; ty/hash.rs, runtime/hash.h).
//
// A `HashMap<K, V, S>` is `{ lust_hash_table t; S s; }` over elements
// `(K, V)` (a `HashSet<T, S>` over `T`), laid out by the hashbrown-exact
// core. Hashing runs Rust's byte streams: `hv_*` glue feeds a value to a
// hasher exactly as core's `Hash` impls and derives do (str adds 0xff,
// slices a length prefix, enums an `isize` discriminant), through the
// hasher's own methods (a user `impl Hasher`, with core's defaults for
// the methods it leaves out) or the SipHash-1-3 of `DefaultHasher`.
use super::*;
use crate::check::hashmap::HASHER_METHODS;
use crate::ty::hash::HashTy;

/// True for the two table types (`HashMap`, `HashSet`).
pub(super) fn is_table(k: HashTy) -> bool {
    matches!(k, HashTy::HashMap | HashTy::HashSet)
}

/// True for the hash types cgen declares a struct for: the tables and
/// `Entry`.
pub(super) fn has_struct(k: HashTy) -> bool {
    matches!(k, HashTy::HashMap | HashTy::HashSet | HashTy::Entry | HashTy::OccupiedEntry | HashTy::VacantEntry) || k.is_iter_form()
}

/// The member list of a declared hash struct: a table and its builder,
/// or an Entry (the table, the key's hash, the found element or NULL,
/// and the key moved in).
pub(super) fn struct_fields(t: &CTy) -> String {
    match t {
        CTy::Hash(HashTy::Entry | HashTy::OccupiedEntry | HashTy::VacantEntry, a) => format!("lust_hash_table *t; uint64_t hash; void *slot; {} key;", ctype(&a[0])),
        // An owning iterator's `it.t` points at its own `t`: re-pointed
        // before each use, since the struct moves.
        CTy::Hash(k, _) if k.is_owning_iter() => "lust_hash_table t; lust_hash_iter it;".to_string(),
        // A drain also keeps the map's table slot, to put the table back.
        CTy::Hash(k, _) if k.is_drain() => "lust_hash_table t; lust_hash_table *orig; lust_hash_iter it;".to_string(),
        CTy::Hash(k, _) if k.is_iter_form() => "lust_hash_iter it;".to_string(),
        _ => format!("lust_hash_table t; {} s;", ctype(&builder_cty(t))),
    }
}

/// The C type name of one hash type.
pub(super) fn hash_ctype(k: HashTy, mangled: &str) -> String {
    match k {
        HashTy::HashMap | HashTy::HashSet => format!("HT_{mangled}"),
        HashTy::RandomState => "lust_random_state".into(),
        HashTy::DefaultHasher => "lust_sip13".into(),
        HashTy::BuildHasherDefault => "lust_Unit".into(),
        HashTy::Entry | HashTy::OccupiedEntry | HashTy::VacantEntry => format!("HE_{mangled}"),
        _ => format!("HI_{mangled}"),
    }
}

/// The element type of a table: `(K, V)` for a map and its Entry, `T`
/// for a set.
pub(super) fn elem_cty(t: &CTy) -> CTy {
    match t {
        CTy::Hash(HashTy::HashMap | HashTy::Entry | HashTy::OccupiedEntry | HashTy::VacantEntry, a) => CTy::Tuple(vec![a[0].clone(), a[1].clone()]),
        CTy::Hash(HashTy::HashSet, a) => a[0].clone(),
        CTy::Hash(k, a) if k.is_iter_form() && a.len() == 2 => CTy::Tuple(vec![a[0].clone(), a[1].clone()]),
        CTy::Hash(k, a) if k.is_iter_form() => a[0].clone(),
        _ => CTy::Unit,
    }
}

/// The key type of a table.
pub(super) fn key_cty(t: &CTy) -> CTy {
    match t {
        CTy::Hash(_, a) if !a.is_empty() => a[0].clone(),
        _ => CTy::Unit,
    }
}

/// The `S` (BuildHasher) type of a table.
pub(super) fn builder_cty(t: &CTy) -> CTy {
    match t {
        CTy::Hash(_, a) => a.last().cloned().unwrap_or(CTy::Unit),
        _ => CTy::Unit,
    }
}

/// The key's place inside an element pointer expression `e`.
fn key_of(t: &CTy, e: &str) -> String {
    match t {
        CTy::Hash(HashTy::HashMap, _) => format!("(&({e})->f0)"),
        _ => format!("({e})"),
    }
}

/// The `Hasher` a `BuildHasher` builds: DefaultHasher for RandomState,
/// `H` for BuildHasherDefault<H>, a user impl's `Hasher` assoc type.
pub(super) fn hasher_cty(p: &Program, s: &CTy) -> CTy {
    match s {
        CTy::Hash(HashTy::RandomState, _) => CTy::Hash(HashTy::DefaultHasher, Vec::new()),
        CTy::Hash(HashTy::BuildHasherDefault, a) => a.first().cloned().unwrap_or(CTy::Unit),
        CTy::Adt(a) => p.gx.build_hashers.get(a).map_or(CTy::Unit, |&(_, h)| cty(&p.tys, h)),
        _ => CTy::Unit,
    }
}

/// The C expression of a fresh hasher from the builder at `s` (a
/// `S*`): `BuildHasher::build_hasher`.
fn build_expr(p: &Program, slots: &Slots, s_cty: &CTy, s: &str, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    match s_cty {
        CTy::Hash(HashTy::RandomState, _) => format!("lust_sip13_new_with_keys(({s})->k0, ({s})->k1)"),
        CTy::Hash(HashTy::BuildHasherDefault, a) => match a.first() {
            Some(CTy::Hash(HashTy::DefaultHasher, _)) => "lust_sip13_new_with_keys(0, 0)".into(),
            Some(h) => {
                need(Glue::Default, h);
                format!("default_{}()", mangle(h))
            }
            None => "0".into(),
        },
        CTy::Adt(a) => match p.gx.build_hashers.get(a) {
            Some(&(f, _)) => format!("({}({s}))", slots.callee(p, f)),
            None => "0".into(),
        },
        _ => "0".into(),
    }
}

/// `H var = <build_expr>;`, or for a user `build_hasher` whose return is
/// passed through an out pointer (a large hasher, such as
/// DefaultHasher) the call that fills `var`.
fn build_into(p: &Program, slots: &Slots, s_cty: &CTy, s: &str, var: &str, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let ht = ctype(&hasher_cty(p, s_cty));
    if let CTy::Adt(a) = s_cty
        && let Some(&(f, _)) = p.gx.build_hashers.get(a)
        && super::ret_is_large(p, f)
    {
        return format!("{ht} {var}; ({}(&{var}, {s}));", slots.callee(p, f));
    }
    format!("{ht} {var} = {};", build_expr(p, slots, s_cty, s, need))
}

/// The C type of the bytes argument of `Hasher::write` (`&[u8]`).
fn bytes_cty() -> CTy {
    CTy::Slice(Box::new(CTy::Int(IntTy::U8)))
}

/// One Hasher method call on `h` (an `H*`) with argument `arg` (a C
/// value of the method's argument type, or "" for `finish`), as a C
/// statement (`finish`: an expression). A user hasher calls its own
/// method, else core's default for it: `write_<uint>` writes the
/// value's native-endian bytes, `write_<int>` defers to the unsigned
/// method of the same width.
fn hasher_call(p: &Program, slots: &Slots, hc: &CTy, m: usize, h: &str, arg: &str) -> String {
    let name = HASHER_METHODS[m];
    let int_of = |m: usize| crate::check::hashmap::hasher_write_arg(HASHER_METHODS[m]).flatten();
    match hc {
        CTy::Hash(HashTy::DefaultHasher, _) => match name {
            "finish" => format!("lust_sip13_finish({h})"),
            "write" => format!("{{ {} b_ = {arg}; lust_sip13_write({h}, b_.ptr, b_.len); }}", ctype(&bytes_cty())),
            _ => {
                let it = int_of(m).unwrap_or(IntTy::U8);
                format!("{{ {} v_ = {arg}; lust_sip13_write({h}, &v_, sizeof v_); }}", int_c(it))
            }
        },
        CTy::Adt(a) => {
            if let Some(&f) = p.gx.hasher_methods.get(&(*a, m as u8)) {
                // `finish` takes only the hasher; a `write*` argument whose parameter goes by
                // pointer (`param_by_ptr`) is a fresh copy, so that call is a block.
                let mut pre = String::new();
                let arg = if arg.is_empty() { String::new() } else { super::glue_args(p, f, &[h, arg], &mut pre).swap_remove(1) };
                let call =
                    format!("({}({h}{}{arg}))", slots.callee(p, f), if arg.is_empty() { "" } else { ", " });
                return if name == "finish" {
                    call
                } else if pre.is_empty() {
                    format!("{call};")
                } else {
                    format!("{{{} {call}; }}", pre.replace('\n', ""))
                };
            }
            match name {
                "finish" | "write" => "0".into(),
                _ => {
                    let it = int_of(m).unwrap_or(IntTy::U8);
                    if it.signed() {
                        // write_iN(x) is write_uN(x as uN): the same bits,
                        // read through a pointer (128-bit values are structs).
                        let u = unsigned_of(it);
                        let call = hasher_call(p, slots, hc, write_int(u), h, &format!("(*({}*)&s_)", int_c(u)));
                        format!("{{ {} s_ = {arg}; {call} }}", int_c(it))
                    } else {
                        let w = HASHER_METHODS.iter().position(|n| *n == "write").unwrap_or(1);
                        let bytes = format!("(({}){{ (uint8_t*)&v_, sizeof v_ }})", ctype(&bytes_cty()));
                        format!("{{ {} v_ = {arg}; {} }}", int_c(it), hasher_call(p, slots, hc, w, h, &bytes))
                    }
                }
            }
        }
        _ => "0".into(),
    }
}

/// The unsigned integer type of the same width.
fn unsigned_of(i: IntTy) -> IntTy {
    match i {
        IntTy::I8 => IntTy::U8,
        IntTy::I16 => IntTy::U16,
        IntTy::I32 => IntTy::U32,
        IntTy::I64 => IntTy::U64,
        IntTy::Isize => IntTy::Usize,
        IntTy::I128 => IntTy::U128,
        u => u,
    }
}

/// The HASHER_METHODS index of `write_<i>`.
fn write_int(i: IntTy) -> usize {
    HASHER_METHODS.iter().position(|n| *n == format!("write_{}", i.name())).unwrap_or(2)
}

/// The glue key of the hash value glue for values of `t` fed to a
/// hasher of `hc`. The key tuple carries `&[u8]` so the glue's units
/// declare the bytes type the hasher calls take.
pub(super) fn hv_key(t: &CTy, hc: &CTy) -> CTy {
    CTy::Tuple(vec![t.clone(), hc.clone(), bytes_cty()])
}

/// C statements that hash the value `v` points at (a `ctype(t)*`) into
/// the hasher `h` (an `H*`), as core's `Hash` impl of `t` does.
fn hash_stmts(p: &Program, slots: &Slots, t: &CTy, hc: &CTy, h: &str, v: &str, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let call = |m: usize, arg: &str| hasher_call(p, slots, hc, m, h, arg);
    let write = HASHER_METHODS.iter().position(|n| *n == "write").unwrap_or(1);
    let bytes = |ptr: &str, len: &str| format!("(({}){{ (uint8_t*)({ptr}), {len} }})", ctype(&bytes_cty()));
    match t {
        CTy::Unit => String::new(),
        CTy::Int(i) => call(write_int(*i), &format!("(*{v})")),
        CTy::Bool => call(write_int(IntTy::U8), &format!("(uint8_t)(*{v})")),
        CTy::Char => call(write_int(IntTy::U32), &format!("(uint32_t)(*{v})")),
        // str: write(bytes), then write_u8(0xff) (Hasher::write_str's default).
        CTy::Str | CTy::String => {
            let s = if *t == CTy::String { format!("lust_string_as_str({v})") } else { format!("(*{v})") };
            format!("{{ lust_str s_ = {s}; {} {} }}", call(write, &bytes("s_.ptr", "s_.len")), call(write_int(IntTy::U8), "0xff"))
        }
        // A raw pointer or fn pointer hashes its address as a usize
        // (w-cinterop; core's `impl<F: FnPtr> Hash for F`).
        CTy::Ptr(_) | CTy::FnPtr(..) => call(write_int(IntTy::Usize), &format!("(uint64_t)(uintptr_t)(*{v})")),
        CTy::Ref(inner) if **inner == CTy::Str => hash_stmts(p, slots, &CTy::Str, hc, h, v, need),
        CTy::Ref(inner) | CTy::Boxed(inner) => hash_stmts(p, slots, inner, hc, h, &format!("(*{v})"), need),
        // Rc and Arc hash their value (`(**self).hash(state)`).
        CTy::Rc(inner) | CTy::Sync(crate::ty::sync::SyncTy::Arc, inner) => hash_stmts(p, slots, inner, hc, h, &super::rc_ptr(&format!("(*{v})"), inner), need),
        // An owning fat pointer hashes its pointee (cgen/own.rs).
        CTy::Own(_, inner) => hash_stmts(p, slots, inner, hc, h, v, need),
        CTy::Tuple(es) => es.iter().enumerate().map(|(i, e)| hash_stmts(p, slots, e, hc, h, &format!("(&({v})->f{i})"), need)).collect(),
        // [T], Box<[T]>, Vec<T>, [T; N]: write_length_prefix (write_usize), then
        // hash_slice: one write of all bytes for integers, else each.
        CTy::Slice(e) | CTy::BoxSlice(e) | CTy::Vec(e) | CTy::Array(e, _) => {
            let (ptr, len) = match t {
                CTy::Slice(_) | CTy::BoxSlice(_) => (format!("({v})->ptr"), format!("({v})->len")),
                CTy::Vec(_) => (format!("(({}*)({v})->ptr)", ctype(e)), format!("({v})->len")),
                CTy::Array(_, n) => (format!("({v})->v"), format!("((uint64_t){n})")),
                _ => unreachable!(),
            };
            let mut s = format!("{{ uint64_t n_ = {len}; {}", call(write_int(IntTy::Usize), "n_"));
            if let CTy::Int(_) = **e {
                let _ = write!(s, " {}", call(write, &bytes(&ptr, &format!("n_ * sizeof(*{ptr})"))));
            } else {
                need(Glue::HashValue, &hv_key(e, hc));
                let _ = write!(s, " for (uint64_t i_ = 0; i_ < n_; i_++) hv_{}({h}, &({ptr})[i_]);", mangle(&hv_key(e, hc)));
            }
            s.push_str(" }");
            s
        }
        _ => {
            need(Glue::HashValue, &hv_key(t, hc));
            format!("hv_{}({h}, {v});", mangle(&hv_key(t, hc)))
        }
    }
}

/// The body of `void hv_<T,H>(H *h, T *p)`: Option and Result as
/// core derives them (an `isize` discriminant, then the payload), and a
/// derived Adt: a discriminant for an enum of more than one variant
/// (its repr type, `isize` by default; the variant's value), then the
/// fields in order. Everything else is `hash_stmts`.
pub(super) fn hash_value_body(p: &Program, slots: &Slots, key: &CTy, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let CTy::Tuple(parts) = key else { return String::new() };
    let (t, hc) = (&parts[0], &parts[1]);
    let isize_call = |disc: &str| hasher_call(p, slots, hc, write_int(IntTy::Isize), "h", &format!("(int64_t)({disc})"));
    let mut body = String::new();
    // `Cow<B>` hashes as the `B` it derefs to (std: `Hash::hash(&**self)`).
    if let Some((rb, decl)) = super::fmt::cow_view(p, t, "p", "v_") {
        let (bt, bp) = match rb {
            CTy::Ref(inner) if *inner != CTy::Str => (*inner, "v_".to_string()),
            CTy::Ref(_) => (CTy::Str, "(&v_)".to_string()),
            sl => (sl, "(&v_)".to_string()),
        };
        let _ = writeln!(body, "  {decl}\n  {}", hash_stmts(p, slots, &bt, hc, "h", &bp, need));
        return body;
    }
    match t {
        CTy::Option(e) => {
            let disc = disc_call(p, t, "p");
            let _ = writeln!(body, "  {}", isize_call(&disc));
            let f = format!("&{}", variant_field(p, t, "(*p)", 1, 0));
            let _ = writeln!(body, "  if ({disc}) {{ {} }}", hash_stmts(p, slots, e, hc, "h", &f, need));
        }
        CTy::Result(a, b) => {
            let disc = disc_call(p, t, "p");
            let _ = writeln!(body, "  {}", isize_call(&disc));
            let fa = format!("&{}", variant_field(p, t, "(*p)", 0, 0));
            let fb = format!("&{}", variant_field(p, t, "(*p)", 1, 0));
            let _ = writeln!(
                body,
                "  if ({disc}) {{ {} }} else {{ {} }}",
                hash_stmts(p, slots, b, hc, "h", &fb, need),
                hash_stmts(p, slots, a, hc, "h", &fa, need)
            );
        }
        // A written impl: its `hash::<H>` instance (`gx.hash_impls`).
        CTy::Adt(a) if let Some(&(_, f)) = p.gx.hash_impls.get(a).and_then(|v| v.iter().find(|(h, _)| cty(&p.tys, *h) == *hc)) => {
            let _ = writeln!(body, "  {}(p, h);", slots.callee(p, f));
        }
        // An unsized newtype (`Path`, `OsStr`): its written impl takes
        // `&self` as the fat value itself.
        CTy::Unsized(a, _) if let Some(&(_, f)) = p.gx.hash_impls.get(a).and_then(|v| v.iter().find(|(h, _)| cty(&p.tys, *h) == *hc)) => {
            let _ = writeln!(body, "  {}(*p, h);", slots.callee(p, f));
        }
        CTy::Adt(a) => {
            let adt = p.adt(*a);
            if adt.is_enum {
                let disc = disc_call(p, t, "p");
                let _ = writeln!(body, "  switch ({disc}) {{");
                for (vi, v) in adt.variants.iter().enumerate() {
                    let mut arm = String::new();
                    if adt.variants.len() > 1 {
                        let dv = v.disc;
                        let m = match adt.repr.int {
                            Some((bits, signed)) => {
                                let it =
                                    IntTy::ALL.iter().copied().find(|i| i.bits() == bits && i.signed() == signed).unwrap_or(IntTy::Isize);
                                (write_int(it), format!("({}){dv}", int_c(it)))
                            }
                            None => (write_int(IntTy::Isize), format!("(int64_t){dv}")),
                        };
                        arm.push_str(&hasher_call(p, slots, hc, m.0, "h", &m.1));
                    }
                    for (fi, fd) in v.fields.iter().enumerate() {
                        arm.push_str(&hash_stmts(p, slots, &cty(&p.tys, fd.ty), hc, "h", &format!("(&p->u.v{vi}.f{fi})"), need));
                    }
                    let _ = writeln!(body, "  case {vi}: {arm} break;");
                }
                body.push_str("  }\n");
            } else {
                for (fi, fd) in adt.variants[0].fields.iter().enumerate() {
                    let _ = writeln!(body, "  {}", hash_stmts(p, slots, &cty(&p.tys, fd.ty), hc, "h", &format!("(&p->f{fi})"), need));
                }
            }
        }
        _ => {
            let _ = writeln!(body, "  {}", hash_stmts(p, slots, t, hc, "h", "p", need));
        }
    }
    body
}

/// The C signature of the hash value glue of `key`.
pub(super) fn hash_value_sig(key: &CTy) -> String {
    let CTy::Tuple(parts) = key else { return String::new() };
    format!("void hv_{}({} *h, {} *p)", mangle(key), ctype(&parts[1]), ctype(&parts[0]))
}

/// The body of `uint64_t hk_<map>(S *s, K *k)`: one key hashed with a
/// fresh hasher from the map's builder, as `make_hash` does.
pub(super) fn hash_key_body(p: &Program, slots: &Slots, map: &CTy, k_cty: &CTy, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    hash_with_builder(p, slots, &builder_cty(map), k_cty, need)
}

/// The body that hashes the key at `k` (a `K*`) with a fresh hasher
/// from the builder at `s` (an `S*`): `make_hash`, and `hash_one`.
fn hash_with_builder(p: &Program, slots: &Slots, s_cty: &CTy, k_cty: &CTy, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let s_cty = s_cty.clone();
    let hc = hasher_cty(p, &s_cty);
    let build = build_into(p, slots, &s_cty, "s", "h", need);
    let stmts = hash_stmts(p, slots, k_cty, &hc, "(&h)", "k", need);
    let finish = hasher_call(p, slots, &hc, 0, "(&h)", "");
    let drop = if needs_drop_c(p, &hc) {
        need(Glue::Drop, &hc);
        format!(" drop_{}(&h);", mangle(&hc))
    } else {
        String::new()
    };
    format!("  {build}\n  {stmts}\n  uint64_t r = {finish};{drop}\n  return r;\n")
}

/// The hasher type a hash glue body builds (`H h = build_hasher(s)`),
/// which its key type does not name: a unit that defines the glue must
/// declare it (a user `BuildHasher`'s `Hasher` in another file's unit).
pub(super) fn glue_hasher(p: &Program, g: &Glue, t: &CTy) -> Option<CTy> {
    let s = match (g, t) {
        (Glue::HashKey, _) => builder_cty(t),
        (Glue::HashKeyQ, CTy::Tuple(parts)) => builder_cty(&parts[0]),
        (Glue::HashOne, CTy::Tuple(parts)) => parts[0].clone(),
        _ => return None,
    };
    Some(hasher_cty(p, &s))
}

/// One hash glue function: (signature, body).
pub(super) fn glue(p: &Program, slots: &Slots, g: &Glue, t: &CTy, need: &mut dyn FnMut(Glue, &CTy)) -> (String, String) {
    let m = mangle(t);
    match g {
        Glue::HashValue => (hash_value_sig(t), hash_value_body(p, slots, t, need)),
        Glue::HashKey => {
            let s = ctype(&builder_cty(t));
            let k = ctype(&key_cty(t));
            (format!("uint64_t hk_{m}({s} *s, {k} *k)"), hash_key_body(p, slots, t, &key_cty(t), need))
        }
        Glue::HashOf => {
            need(Glue::HashKey, t);
            let (s, k, e) = (ctype(&builder_cty(t)), ctype(&key_cty(t)), ctype(&elem_cty(t)));
            let key = key_of(t, &format!("({e}*)elem"));
            (format!("uint64_t hof_{m}(void *ctx, const void *elem)"), format!("  return hk_{m}(({s}*)ctx, ({k}*){key});\n"))
        }
        Glue::HashEq => {
            let (k_cty, e) = (key_cty(t), ctype(&elem_cty(t)));
            let key = key_of(t, &format!("({e}*)elem"));
            let eq = eq_expr(p, &k_cty, &format!("({}*)ctx", ctype(&k_cty)), &format!("({}*){key}", ctype(&k_cty)), need);
            (format!("int heq_{m}(void *ctx, const void *elem)"), format!("  return {eq};\n"))
        }
        Glue::HashEqEntry => {
            // `rustc_entry` compares `stored == probe` (the other
            // lookups put the probe key on the left).
            let (k_cty, e) = (key_cty(t), ctype(&elem_cty(t)));
            let key = key_of(t, &format!("({e}*)elem"));
            let eq = eq_expr(p, &k_cty, &format!("({}*){key}", ctype(&k_cty)), &format!("({}*)ctx", ctype(&k_cty)), need);
            (format!("int heqe_{m}(void *ctx, const void *elem)"), format!("  return {eq};\n"))
        }
        Glue::HashDrop => {
            let ec = elem_cty(t);
            need(Glue::Drop, &ec);
            (format!("void hdr_{m}(void *ctx, void *elem)"), format!("  (void)ctx; drop_{}(({}*)elem);\n", mangle(&ec), ctype(&ec)))
        }
        Glue::HashClone => {
            let ec = elem_cty(t);
            let e = ctype(&ec);
            let body = if is_copy_c(p, &ec) {
                format!("  (void)ctx; *({e}*)dst = *({e}*)src;\n")
            } else {
                need(Glue::Clone, &ec);
                format!("  (void)ctx; *({e}*)dst = clone_{}(({e}*)src);\n", mangle(&ec))
            };
            (format!("void hcl_{m}(void *ctx, void *dst, const void *src)"), body)
        }
        Glue::HashOne => {
            let CTy::Tuple(parts) = t else { return (String::new(), String::new()) };
            let (s, x) = (&parts[0], &parts[1]);
            (format!("uint64_t hone_{m}({} *s, {} *k)", ctype(s), ctype(x)), hash_with_builder(p, slots, s, x, need))
        }
        Glue::HashKeyQ | Glue::HashEqQ => {
            let CTy::Tuple(parts) = t else { return (String::new(), String::new()) };
            let (map, q) = (&parts[0], &parts[1]);
            let qc = ctype(q);
            if *g == Glue::HashKeyQ {
                let s = ctype(&builder_cty(map));
                let body = match dyn_key(p, map, q) {
                    Some(dk) => dyn_hash_body(p, slots, map, dk, need),
                    None => hash_key_body(p, slots, map, q, need),
                };
                (format!("uint64_t hkq_{m}({s} *s, {qc} *k)"), body)
            } else if let Some(dk) = dyn_key(p, map, q) {
                // `<dyn K as PartialEq>::eq(probe, stored.borrow())`: both are
                // fat values passed by value (the fns take `&self`, `&Self`).
                let (k_cty, e) = (key_cty(map), ctype(&elem_cty(map)));
                let key = key_of(map, &format!("({e}*)elem"));
                let borrowed = borrow_expr(p, slots, &k_cty, q, &format!("({}*){key}", ctype(&k_cty)));
                let mut pre = String::new();
                let args = super::glue_args(p, dk.eq, &["*(lust_dyn*)ctx", &format!("*{borrowed}")], &mut pre).join(", ");
                let call = format!("{}({args})", slots.callee(p, dk.eq));
                (format!("int heqq_{m}(void *ctx, const void *elem)"), format!("{pre}  return {call};\n"))
            } else {
                let (k_cty, e) = (key_cty(map), ctype(&elem_cty(map)));
                let key = key_of(map, &format!("({e}*)elem"));
                let borrowed = borrow_expr(p, slots, &k_cty, q, &format!("({}*){key}", ctype(&k_cty)));
                let eq = eq_expr(p, q, &format!("({qc}*)ctx"), &borrowed, need);
                (format!("int heqq_{m}(void *ctx, const void *elem)"), format!("  return {eq};\n"))
            }
        }
        _ => (String::new(), String::new()),
    }
}

/// The dyn lookup of a map whose key is a local Adt with a
/// `Borrow<dyn K>` impl, when `q` is that dyn form (`gx.dyn_keys`).
fn dyn_key<'p>(p: &'p Program, map: &CTy, q: &CTy) -> Option<&'p crate::check::generics::DynKey> {
    match (key_cty(map), q) {
        (CTy::Adt(a), CTy::Dyn) => p.gx.dyn_keys.get(&a),
        _ => None,
    }
}

/// The `hkq_` body of a dyn lookup: a fresh hasher, the written
/// `<dyn K as Hash>::hash::<H>` instance on the probe (a fat value), then
/// `finish`, as `make_hash` runs for any key.
fn dyn_hash_body(p: &Program, slots: &Slots, map: &CTy, dk: &crate::check::generics::DynKey, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let s_cty = builder_cty(map);
    let hc = hasher_cty(p, &s_cty);
    let Some(&(_, f)) = dk.hash_insts.iter().find(|&&(h, _)| cty(&p.tys, h) == hc) else {
        unreachable!("dyn key lookup: no hash instance for the map's hasher (check/hashmap.rs checks it)")
    };
    let build = build_into(p, slots, &s_cty, "s", "h", need);
    let finish = hasher_call(p, slots, &hc, 0, "(&h)", "");
    let drop = if needs_drop_c(p, &hc) {
        need(Glue::Drop, &hc);
        format!(" drop_{}(&h);", mangle(&hc))
    } else {
        String::new()
    };
    let mut pre = String::new();
    let args = super::glue_args(p, f, &["*k", "&h"], &mut pre).join(", ");
    let call = format!("{}({args});", slots.callee(p, f));
    format!("  {build}\n{pre}  {call}\n  uint64_t r = {finish};{drop}\n  return r;\n")
}

/// A `Q*` expression for `<K as Borrow<Q>>::borrow` of the key at `k`
/// (a `K*`): String to str, Vec<T> to [T], one deref of Box/Rc/&T, a
/// written impl's `borrow` (`gx.borrow_impls`), or the key itself. The
/// result points at a temporary for the fat forms.
fn borrow_expr(p: &Program, slots: &Slots, k: &CTy, q: &CTy, kp: &str) -> String {
    if k == q {
        return kp.to_string();
    }
    if let CTy::Adt(a) = k
        && let Some((_, &f)) = p.gx.borrow_impls.iter().find(|((b, t), _)| b == a && cty(&p.tys, *t) == *q)
    {
        let call = if super::ret_is_large(p, f) {
            // A return through the out pointer (`ret_by_out`): a statement expression.
            format!("({{ {} r_; {}(&r_, {kp}); r_; }})", ctype(&cty(&p.tys, p.fn_info(f).ret)), slots.callee(p, f))
        } else {
            format!("{}({kp})", slots.callee(p, f))
        };
        // `&str`, `&[T]`, `&dyn Tr` and `&Path` (an unsized newtype) come
        // back as fat values: point at a temporary.
        return match q {
            CTy::Str => format!("((lust_str[]){{ {call} }})"),
            CTy::Slice(_) | CTy::Dyn | CTy::Unsized(..) => format!("(({}[]){{ {call} }})", ctype(q)),
            _ => call,
        };
    }
    match (k, q) {
        (CTy::String, CTy::Str) => format!("((lust_str[]){{ lust_string_as_str({kp}) }})"),
        (CTy::Vec(e), CTy::Slice(_)) => format!("(&({}){{ ({}*)({kp})->ptr, ({kp})->len }})", ctype(q), ctype(e)),
        (CTy::Array(_, n), CTy::Slice(_)) => format!("(&({}){{ ({kp})->v, {n} }})", ctype(q)),
        // `&str` and `Box<str>` are the fat str value itself.
        (CTy::Ref(inner) | CTy::Boxed(inner), CTy::Str) if **inner == CTy::Str => kp.to_string(),
        (CTy::Boxed(_) | CTy::Ref(_), _) => format!("(*{kp})"),
        // `Cow<B>` borrows as the `B` it derefs to.
        (CTy::Adt(_), _) => match super::fmt::cow_view_expr(p, k, kp) {
            Some((CTy::Ref(inner), e)) if *inner != CTy::Str => e,
            Some((rb, e)) => format!("(({}[]){{ {e} }})", ctype(&rb)),
            None => kp.to_string(),
        },
        (CTy::Rc(e), _) => super::rc_ptr(&format!("(*{kp})"), e),
        // `Rc<str>` borrows as `str`: the same fat value (cgen/own.rs).
        (CTy::Own(..), _) => kp.to_string(),
        _ => kp.to_string(),
    }
}

/// `PartialEq::eq` of two values of `t` at `a` and `b` (`t*`).
fn eq_expr(p: &Program, t: &CTy, a: &str, b: &str, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let _ = p;
    match t {
        CTy::Unit => "1".into(),
        CTy::Bool | CTy::Char | CTy::Int(_) if !matches!(t, CTy::Int(i) if is128(*i)) => format!("(*({a}) == *({b}))"),
        CTy::Str => format!("lust_str_eq(*({a}), *({b}))"),
        CTy::Ref(inner) if **inner == CTy::Str => format!("lust_str_eq(*({a}), *({b}))"),
        CTy::String => format!("lust_str_eq(lust_string_as_str({a}), lust_string_as_str({b}))"),
        _ => {
            need(Glue::Eq, t);
            format!("eq_{}({a}, {b})", mangle(t))
        }
    }
}

/// The body of `uint8_t eq_<table>(T *a, T *b)`: std's PartialEq of a
/// map or set. The lengths agree, and each element of `a`, in bucket
/// order, is found in `b` by `b`'s builder (`other.get(k)`); a map's
/// values then compare, `a`'s on the left.
pub(super) fn table_eq_body(p: &Program, t: &CTy, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let CTy::Hash(k, _) = t else { return "  return 0;\n".into() };
    let (m, e) = (mangle(t), ctype(&elem_cty(t)));
    need(Glue::HashKey, t);
    need(Glue::HashEq, t);
    let key = key_of(t, "x");
    let mut s = format!(
        "  if (lust_hash_len(&a->t) != lust_hash_len(&b->t)) return 0;\n  lust_hash_iter it; lust_hash_iter_init(&it, &a->t);\n  {e} *x;\n  while ((x = ({e}*)lust_hash_iter_next(&it, 0))) {{\n    {e} *y = ({e}*)lust_hash_find(&b->t, hk_{m}(&b->s, {key}), heq_{m}, (void*){key}, 0);\n    if (!y) return 0;\n"
    );
    if *k == HashTy::HashMap
        && let CTy::Tuple(parts) = elem_cty(t)
    {
        let c = eq_expr(p, &parts[1], "(&x->f1)", "(&y->f1)", need);
        let _ = writeln!(s, "    if (!{c}) return 0;");
    }
    s.push_str("  }\n  return 1;\n");
    s
}

/// The drop glue body of a table: the builder first, then every
/// element in bucket order (hashbrown's field order and drop loop).
pub(super) fn drop_body(p: &Program, t: &CTy, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let (s, ec) = (builder_cty(t), elem_cty(t));
    let mut body = String::new();
    if needs_drop_c(p, &s) {
        need(Glue::Drop, &s);
        let _ = writeln!(body, "  drop_{}(&p->s);", mangle(&s));
    }
    if needs_drop_c(p, &ec) {
        need(Glue::Drop, &ec);
        let _ = writeln!(
            body,
            "  {{ lust_hash_iter it; lust_hash_iter_init(&it, &p->t); void *e; while ((e = lust_hash_iter_next(&it, 0))) drop_{}(({}*)e); }}",
            mangle(&ec),
            ctype(&ec)
        );
    }
    body.push_str("  lust_hash_drop_table(&p->t, 0, 0);\n");
    body
}

/// The clone glue body of a table: the builder, then the table with
/// the same buckets, elements cloned in bucket order.
pub(super) fn clone_body(p: &Program, t: &CTy, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let (s, ec) = (builder_cty(t), elem_cty(t));
    let ct = ctype(t);
    let e = ctype(&ec);
    let sc = if is_copy_c(p, &s) {
        "p->s".to_string()
    } else {
        need(Glue::Clone, &s);
        format!("clone_{}(&p->s)", mangle(&s))
    };
    need(Glue::HashClone, t);
    format!(
        "  {ct} r; r.s = {sc}; lust_hash_init(&r.t, sizeof({e}), _Alignof({e}));\n  lust_hash_clone_into(&r.t, &p->t, hcl_{}, 0);\n  return r;\n",
        mangle(t)
    )
}

/// The static initializer of an empty table around a const hasher
/// value (`HashMap::with_hasher(S)` in a static): the empty singleton,
/// as `lust_hash_init` leaves it. The control bytes point at a 16-byte
/// all-EMPTY array of this unit (emitted once into `pre`), a copy of
/// the runtime's static empty group; the table never writes through it.
pub(super) fn const_empty_table(t: &CTy, s_init: &str, pre: &mut String) -> String {
    if !pre.contains("lust_hash_cempty[16]") {
        pre.push_str("#ifndef LUST_HASH_CEMPTY\n#define LUST_HASH_CEMPTY\nstatic const uint8_t lust_hash_cempty[16] = {0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF};\n#endif\n");
    }
    let e = ctype(&elem_cty(t));
    format!(
        "(({}){{ .s = {s_init}, .t = {{ .ctrl = (uint8_t*)lust_hash_cempty, .elem_size = sizeof({e}), .elem_align = _Alignof({e}) }} }})",
        ctype(t)
    )
}

/// The body of `default_T` for a hash type: `Default::default()` of
/// the builders and hashers, and a table built `with_hasher(S::default())`.
pub(super) fn default_body(p: &Program, t: &CTy, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    match t {
        CTy::Hash(k, _) if is_table(*k) => {
            let (s, e) = (builder_cty(t), ctype(&elem_cty(t)));
            let sv = default_of(p, &s, need);
            format!("  {} r; r.s = {sv}; lust_hash_init(&r.t, sizeof({e}), _Alignof({e}));\n  return r;\n", ctype(t))
        }
        _ => format!("  return {};\n", default_of(p, t, need)),
    }
}

/// `Default::default()` of a builder or hasher type as a C expression.
fn default_of(p: &Program, t: &CTy, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    match t {
        CTy::Hash(HashTy::RandomState, _) => "lust_random_state_new()".into(),
        CTy::Hash(HashTy::DefaultHasher, _) => "lust_sip13_new_with_keys(0, 0)".into(),
        CTy::Hash(HashTy::BuildHasherDefault, _) | CTy::Unit => "((lust_Unit){})".into(),
        _ => {
            let _ = p;
            need(Glue::Default, t);
            format!("default_{}()", mangle(t))
        }
    }
}

/// True for the builtins `FnGen::hash_builtin` emits.
fn is_hash_builtin(b: Builtin) -> bool {
    use Builtin as B;
    matches!(
        b,
        B::HashNew
            | B::HashWithCapacity
            | B::HashWithHasher
            | B::HashWithCapacityAndHasher
            | B::HashDefault
            | B::HashLen
            | B::HashIsEmpty
            | B::HashClear
            | B::HashCapacity
            | B::MapInsert
            | B::MapGet
            | B::MapGetMut
            | B::MapContainsKey
            | B::MapRemove
            | B::MapRemoveEntry
            | B::MapRetain
            | B::SetRetain
            | B::MapEntry
            | B::EntryOrInsert
            | B::EntryOrDefault
            | B::EntryKey
            | B::EntryOccupied
            | B::EntryIntoMut
            | B::EntryInsert
            | B::EntryGetMut
            | B::EntryInsertEntry
            | B::EntryAsOccupied
            | B::EntryAsVacant
            | B::VacIntoKey
            | B::MapGetKeyValue
            | B::OccKey
            | B::OccGet
            | B::OccGetMut
            | B::OccIntoMut
            | B::OccInsert
            | B::OccRemove
            | B::OccRemoveEntry
            | B::SetInsert
            | B::SetContains
            | B::SetRemove
            | B::SetGet
            | B::HashIterNew
            | B::HashIterNext
            | B::HashIterLen
            | B::HashExtendReserve
            | B::HashReserve
            | B::HashInto
            | B::HashOne
            | B::BuildHasher
            | B::HasherCall
    )
}

/// The drop glue body of an owning hash iterator: the elements not yet
/// yielded, in iteration order, then the allocation (hashbrown's
/// `RawIntoIter` drop). A drain instead empties the table (control
/// bytes reset, tombstones too, allocation kept: `clear_no_drop`) and
/// puts it back in the map (hashbrown's `RawDrain` drop).
pub(super) fn iter_drop_body(p: &Program, t: &CTy, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let ec = elem_cty(t);
    let mut body = String::from("  p->it.t = &p->t;\n");
    if needs_drop_c(p, &ec) {
        need(Glue::Drop, &ec);
        let _ = writeln!(body, "  {{ void *e; while ((e = lust_hash_iter_next(&p->it, 0))) drop_{}(({}*)e); }}", mangle(&ec), ctype(&ec));
    }
    if matches!(t, CTy::Hash(k, _) if k.is_drain()) {
        // `lust_hash_drain_finish` with no drop fn and nothing left is
        // the runtime's `clear_no_drop`.
        body.push_str("  { lust_hash_drain z; lust_hash_drain_init(&z, &p->t); z.left = 0; lust_hash_drain_finish(&z, 0, 0); }\n  *p->orig = p->t;\n");
    } else {
        body.push_str("  lust_hash_drop_table(&p->t, 0, 0);\n");
    }
    body
}

impl FnGen<'_, '_> {
    /// One HashMap, HashSet, or Entry builtin call (check/hashmap.rs) as
    /// hashbrown runs it, or None for every other builtin. `dest` is the
    /// call's result type, which the constructors build.
    pub(super) fn hash_builtin(&mut self, b: Builtin, ops: &[Operand], dest: &CTy, loc: &str, post: &mut Vec<String>) -> Option<String> {
        use Builtin as B;
        if !is_hash_builtin(b) {
            return None;
        }
        let mut vals = Vec::new();
        let mut tys = Vec::new();
        for o in ops {
            let (v, t) = self.operand(o, loc, post);
            vals.push(v);
            tys.push(t);
        }
        self.note_held(dest);
        let dc = ctype(dest);
        // The receiver: a table or Entry behind `&`/`&mut`, or an Entry
        // by value.
        let (recv, r) = match tys.first() {
            Some(CTy::Ref(inner)) => ((**inner).clone(), format!("({})", vals[0])),
            Some(t) => (t.clone(), format!("(&{})", vals.first().cloned().unwrap_or_default())),
            None => (CTy::Unit, String::new()),
        };
        let t = self.tmp();
        match b {
            // `x.hash(state)`: (&T, &mut H), through the value glue.
            B::HashInto => {
                let Some(CTy::Ref(hc)) = tys.get(1) else { panic!("internal: `hash` without a `&mut H` argument") };
                // A `&str` or `&[T]` receiver is a fat value, not a
                // pointer (the autoref'd `[T]` arrives as `CTy::Slice`
                // itself): hash it from a temporary, as core hashes the
                // reference as its pointee.
                let (xt, xp) = match &tys[0] {
                    CTy::Ref(x) if matches!(**x, CTy::Str | CTy::Slice(_)) => {
                        let _ = writeln!(self.out, "    {} {t}_x = {};", ctype(&tys[0]), vals[0]);
                        (tys[0].clone(), format!("(&{t}_x)"))
                    }
                    CTy::Ref(x) => ((**x).clone(), vals[0].clone()),
                    CTy::Slice(_) | CTy::Str => {
                        let _ = writeln!(self.out, "    {} {t}_x = {};", ctype(&tys[0]), vals[0]);
                        (tys[0].clone(), format!("(&{t}_x)"))
                    }
                    other => panic!("internal: `hash` receiver of C type {other:?}"),
                };
                let key = hv_key(&xt, hc);
                self.want(Glue::HashValue, &key);
                let _ = writeln!(self.out, "    hv_{}({}, {xp});", mangle(&key), vals[1]);
                Some("((lust_Unit){})".into())
            }
            // `s.hash_one(x)`: (&S, T); `x` is moved in and dropped after.
            B::HashOne => {
                let (Some(CTy::Ref(s)), Some(x)) = (tys.first(), tys.get(1)) else { return Some("0".into()) };
                let key = CTy::Tuple(vec![(**s).clone(), x.clone()]);
                self.want(Glue::HashOne, &key);
                let _ = writeln!(self.out, "    {} {t}_x = {}; uint64_t {t} = hone_{}({}, &{t}_x);", ctype(x), vals[1], mangle(&key), vals[0]);
                if needs_drop_c(self.p, x) {
                    self.want(Glue::Drop, x);
                    let _ = writeln!(self.out, "    drop_{}(&{t}_x);", mangle(x));
                }
                Some(t)
            }
            // `s.build_hasher()`: (&S,), a std builder.
            B::BuildHasher => {
                let Some(CTy::Ref(s)) = tys.first() else { return Some("0".into()) };
                let mut need = Vec::new();
                let init = build_into(self.p, self.slots, s, &format!("({})", vals[0]), &t, &mut |g, c| need.push((g, c.clone())));
                for (g, c) in need {
                    self.want(g, &c);
                }
                let _ = writeln!(self.out, "    {init}");
                Some(t)
            }
            // A Hasher method, picked by its argument (check/mod.rs `HasherCall`).
            B::HasherCall => {
                let hc = match tys.first() {
                    Some(CTy::Ref(h)) => (**h).clone(),
                    _ => return Some("0".into()),
                };
                let m = match tys.get(1) {
                    None => 0,
                    Some(CTy::Int(i)) => write_int(*i),
                    Some(_) => HASHER_METHODS.iter().position(|n| *n == "write").unwrap_or(1),
                };
                // The call can name the `&[u8]` struct (an integer write
                // goes through `write`): this unit must declare it.
                self.note_held(&bytes_cty());
                let call = hasher_call(self.p, self.slots, &hc, m, &format!("({})", vals[0]), vals.get(1).map_or("", |v| v.as_str()));
                if m == 0 {
                    return Some(call);
                }
                let _ = writeln!(self.out, "    {call}");
                Some("((lust_Unit){})".into())
            }
            B::HashNew | B::HashWithCapacity | B::HashWithHasher | B::HashWithCapacityAndHasher | B::HashDefault => {
                let CTy::Hash(k, _) = dest else { return Some("((lust_Unit){})".into()) };
                if !is_table(*k) {
                    let mut need = Vec::new();
                    let v = default_of(self.p, dest, &mut |g, t| need.push((g, t.clone())));
                    for (g, t) in need {
                        self.want(g, &t);
                    }
                    return Some(v);
                }
                let e = ctype(&elem_cty(dest));
                let s = match b {
                    B::HashWithHasher => vals[0].clone(),
                    B::HashWithCapacityAndHasher => vals[1].clone(),
                    B::HashDefault => {
                        let mut need = Vec::new();
                        let v = default_of(self.p, &builder_cty(dest), &mut |g, t| need.push((g, t.clone())));
                        for (g, t) in need {
                            self.want(g, &t);
                        }
                        v
                    }
                    _ => "lust_random_state_new()".into(),
                };
                let init = match b {
                    B::HashWithCapacity => format!("lust_hash_init_with_capacity(&{t}.t, sizeof({e}), _Alignof({e}), {});", vals[0]),
                    B::HashWithCapacityAndHasher => {
                        format!("lust_hash_init_with_capacity(&{t}.t, sizeof({e}), _Alignof({e}), {});", vals[0])
                    }
                    _ => format!("lust_hash_init(&{t}.t, sizeof({e}), _Alignof({e}));"),
                };
                let _ = writeln!(self.out, "    {dc} {t}; {t}.s = {s}; {init}");
                Some(t)
            }
            B::HashLen => Some(format!("lust_hash_len(&{r}->t)")),
            B::HashIsEmpty => Some(format!("((uint8_t)(lust_hash_len(&{r}->t) == 0))")),
            B::HashCapacity => Some(format!("lust_hash_capacity(&{r}->t)")),
            B::HashClear => {
                let ec = elem_cty(&recv);
                let drop = if needs_drop_c(self.p, &ec) {
                    self.want(Glue::HashDrop, &recv);
                    format!("hdr_{}", mangle(&recv))
                } else {
                    "0".into()
                };
                let _ = writeln!(self.out, "    lust_hash_clear(&{r}->t, {drop}, 0);");
                Some("((lust_Unit){})".into())
            }
            B::MapGet | B::MapGetMut | B::MapGetKeyValue | B::MapContainsKey | B::SetContains | B::SetGet => {
                // hashbrown's `get_inner`: an empty table answers None
                // without hashing the key.
                let (q, qp) = self.q_arg(&tys[1], &vals[1]);
                let mk = self.want_q(&recv, &q);
                let e = ctype(&elem_cty(&recv));
                let f = self.tmp();
                let _ = writeln!(
                    self.out,
                    "    {e} *{f} = 0; if (lust_hash_len(&{r}->t) != 0) {f} = ({e}*)lust_hash_find(&{r}->t, hkq_{mk}(&{r}->s, {qp}), heqq_{mk}, (void*){qp}, 0);"
                );
                Some(match b {
                    B::MapContainsKey | B::SetContains => format!("((uint8_t)({f} != 0))"),
                    _ => {
                        let found = match b {
                            B::SetGet => f.clone(),
                            // `(&K, &V)`: the dest's tuple, both fields in the bucket.
                            B::MapGetKeyValue => {
                                let CTy::Option(pair) = dest else { unreachable!("get_key_value returns an Option") };
                                format!("(({}){{ &{f}->f0, &{f}->f1 }})", ctype(pair))
                            }
                            _ => format!("(&{f}->f1)"),
                        };
                        let some = self.make_variant(dest, 1, &[found]);
                        let none = self.make_variant(dest, 0, &[]);
                        let _ = writeln!(self.out, "    {dc} {t} = {f} ? {some} : {none};");
                        t
                    }
                })
            }
            B::MapRemove | B::MapRemoveEntry | B::SetRemove => {
                let (q, qp) = self.q_arg(&tys[1], &vals[1]);
                let mk = self.want_q(&recv, &q);
                let ec = elem_cty(&recv);
                let (e, o) = (ctype(&ec), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    {e} {o}; int {o}_hit = lust_hash_remove(&{r}->t, hkq_{mk}(&{r}->s, {qp}), heqq_{mk}, (void*){qp}, &{o});"
                );
                if b == B::SetRemove {
                    if needs_drop_c(self.p, &ec) {
                        self.want(Glue::Drop, &ec);
                        let _ = writeln!(self.out, "    if ({o}_hit) drop_{}(&{o});", mangle(&ec));
                    }
                    return Some(format!("((uint8_t){o}_hit)"));
                }
                // `remove_entry` hands back the stored pair (key and value).
                if b == B::MapRemoveEntry {
                    let some = self.make_variant(dest, 1, &[o.clone()]);
                    let none = self.make_variant(dest, 0, &[]);
                    let _ = writeln!(self.out, "    {dc} {t} = {o}_hit ? {some} : {none};");
                    return Some(t);
                }
                let kc = key_cty(&recv);
                if needs_drop_c(self.p, &kc) {
                    self.want(Glue::Drop, &kc);
                    let _ = writeln!(self.out, "    if ({o}_hit) drop_{}(&{o}.f0);", mangle(&kc));
                }
                let some = self.make_variant(dest, 1, &[format!("{o}.f1")]);
                let none = self.make_variant(dest, 0, &[]);
                let _ = writeln!(self.out, "    {dc} {t} = {o}_hit ? {some} : {none};");
                Some(t)
            }
            B::MapRetain | B::SetRetain => {
                // hashbrown's `retain`: the predicate runs once per element
                // in iteration order; a rejected element is erased, then
                // dropped (key before value), before the next call. The
                // closure drops after the loop.
                let ec = elem_cty(&recv);
                let e = ctype(&ec);
                let f = self.adapter_callee(&ops[1]);
                let (c, it, s) = (self.tmp(), self.tmp(), self.tmp());
                let mut body = String::new();
                let _ = writeln!(body, "    {} {c} = {};", ctype(&tys[1]), vals[1]);
                let _ = writeln!(body, "    lust_hash_iter {it}; lust_hash_iter_init(&{it}, &{r}->t); uint64_t {it}_i; {e} *{s};");
                let _ = writeln!(body, "    while (({s} = ({e}*)lust_hash_iter_next(&{it}, &{it}_i))) {{");
                let args = if b == B::MapRetain { vec![format!("(&{s}->f0)"), format!("(&{s}->f1)")] } else { vec![s.clone()] };
                let (keep, _) = self.adapter_call_c(&mut body, &f, &format!("&{c}"), &args);
                let drop = if needs_drop_c(self.p, &ec) {
                    self.want(Glue::Drop, &ec);
                    format!(" drop_{}({s});", mangle(&ec))
                } else {
                    String::new()
                };
                let _ = writeln!(body, "      if (!{keep}) {{ lust_hash_erase_at(&{r}->t, {it}_i, 0);{drop} }}");
                let _ = writeln!(body, "    }}");
                if needs_drop_c(self.p, &tys[1]) {
                    self.want(Glue::Drop, &tys[1]);
                    let _ = writeln!(body, "    drop_{}(&{c});", mangle(&tys[1]));
                }
                let _ = write!(self.out, "{body}");
                Some("((lust_Unit){})".into())
            }
            B::MapInsert | B::SetInsert => {
                let m = mangle(&recv);
                for g in [Glue::HashKey, Glue::HashEq, Glue::HashOf] {
                    self.want(g, &recv);
                }
                let (kc, ec) = (key_cty(&recv), elem_cty(&recv));
                let (k, e) = (ctype(&kc), ctype(&ec));
                let (kv, h, s, i) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {k} {kv} = {}; uint64_t {h} = hk_{m}(&{r}->s, &{kv}); void *{s}; uint64_t {i};", vals[1]);
                let drop_key = if needs_drop_c(self.p, &kc) {
                    self.want(Glue::Drop, &kc);
                    format!(" drop_{}(&{kv});", mangle(&kc))
                } else {
                    String::new()
                };
                let find = format!("lust_hash_find_or_insert(&{r}->t, {h}, heq_{m}, &{kv}, hof_{m}, &{r}->s, &{s}, &{i})");
                if b == B::SetInsert {
                    let _ = writeln!(
                        self.out,
                        "    uint8_t {t}; if ({find}) {{ {t} = 0;{drop_key} }} else {{ *({e}*)lust_hash_insert_at(&{r}->t, {h}, {i}) = {kv}; {t} = 1; }}"
                    );
                    return Some(t);
                }
                let vt = match &ec {
                    CTy::Tuple(es) => ctype(&es[1]),
                    _ => "lust_Unit".into(),
                };
                let vv = self.tmp();
                let some = self.make_variant(dest, 1, &[format!("(({e}*){s})->f1")]);
                let none = self.make_variant(dest, 0, &[]);
                let _ = writeln!(
                    self.out,
                    "    {vt} {vv} = {}; {dc} {t}; if ({find}) {{ {t} = {some}; (({e}*){s})->f1 = {vv};{drop_key} }} else {{ {e} *n_{t} = ({e}*)lust_hash_insert_at(&{r}->t, {h}, {i}); n_{t}->f0 = {kv}; n_{t}->f1 = {vv}; {t} = {none}; }}",
                    vals[2]
                );
                Some(t)
            }
            B::MapEntry => {
                // hashbrown's `rustc_entry`: hash, find (stored == probe);
                // occupied drops the probe key now, vacant reserves one.
                let m = mangle(&recv);
                for g in [Glue::HashKey, Glue::HashEqEntry, Glue::HashOf] {
                    self.want(g, &recv);
                }
                let kc = key_cty(&recv);
                let k = ctype(&kc);
                let kv = self.tmp();
                let drop_key = if needs_drop_c(self.p, &kc) {
                    self.want(Glue::Drop, &kc);
                    format!("drop_{}(&{kv});", mangle(&kc))
                } else {
                    String::new()
                };
                let _ = writeln!(
                    self.out,
                    "    {k} {kv} = {}; {dc} {t}; {t}.t = &{r}->t; {t}.hash = hk_{m}(&{r}->s, &{kv}); {t}.slot = lust_hash_find(&{r}->t, {t}.hash, heqe_{m}, &{kv}, 0);",
                    vals[1]
                );
                let _ = writeln!(
                    self.out,
                    "    if ({t}.slot) {{ {drop_key} }} else {{ lust_hash_reserve(&{r}->t, 1, hof_{m}, &{r}->s); {t}.key = {kv}; }}"
                );
                Some(t)
            }
            B::EntryOrInsert | B::EntryOrDefault => {
                let ec = elem_cty(&recv);
                let e = ctype(&ec);
                let vc = match &ec {
                    CTy::Tuple(es) => es[1].clone(),
                    _ => CTy::Unit,
                };
                let ev = self.tmp();
                let _ = writeln!(self.out, "    {} {ev} = {};", ctype(&recv), vals[0]);
                let (pre, occupied_drop, value) = if b == B::EntryOrInsert {
                    let vv = self.tmp();
                    let drop = if needs_drop_c(self.p, &vc) {
                        self.want(Glue::Drop, &vc);
                        format!(" drop_{}(&{vv});", mangle(&vc))
                    } else {
                        String::new()
                    };
                    (format!("{} {vv} = {}; ", ctype(&vc), vals[1]), drop, vv)
                } else {
                    let mut need = Vec::new();
                    let v = match &vc {
                        CTy::Unit | CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Float(_) => zero_lit(self.p, &vc),
                        _ => {
                            need.push((Glue::Default, vc.clone()));
                            format!("default_{}()", mangle(&vc))
                        }
                    };
                    for (g, t) in need {
                        self.want(g, &t);
                    }
                    (String::new(), String::new(), v)
                };
                let _ = writeln!(
                    self.out,
                    "    {pre}{dc} {t}; if ({ev}.slot) {{ {t} = &(({e}*){ev}.slot)->f1;{occupied_drop} }} else {{ {e} *n_{t} = ({e}*)lust_hash_insert_no_grow_slot({ev}.t, {ev}.hash, 0); n_{t}->f0 = {ev}.key; n_{t}->f1 = {value}; {t} = &n_{t}->f1; }}"
                );
                Some(t)
            }
            B::EntryKey => {
                let e = ctype(&elem_cty(&recv));
                Some(format!("({r}->slot ? &(({e}*){r}->slot)->f0 : &{r}->key)"))
            }
            // The steps of the closure forms (lower/iter.rs `entry_with`).
            B::EntryOccupied => Some(format!("({r}->slot != 0)")),
            B::EntryIntoMut | B::EntryGetMut => {
                let e = ctype(&elem_cty(&recv));
                if b == B::EntryGetMut {
                    return Some(format!("(&(({e}*){r}->slot)->f1)"));
                }
                let ev = self.tmp();
                let _ = writeln!(self.out, "    {} {ev} = {};", ctype(&recv), vals[0]);
                Some(format!("(&(({e}*){ev}.slot)->f1)"))
            }
            B::EntryInsert => {
                let e = ctype(&elem_cty(&recv));
                let ev = self.tmp();
                let _ = writeln!(self.out, "    {} {ev} = {};", ctype(&recv), vals[0]);
                let _ = writeln!(
                    self.out,
                    "    {dc} {t}; {{ {e} *n_{t} = ({e}*)lust_hash_insert_no_grow_slot({ev}.t, {ev}.hash, 0); n_{t}->f0 = {ev}.key; n_{t}->f1 = {}; {t} = &n_{t}->f1; }}",
                    vals[1]
                );
                Some(t)
            }
            // std's `Entry::insert_entry`: occupied, `entry.insert(v)` (the
            // new value is stored, then the old one drops); vacant, the
            // key and value go into the slot `entry()` reserved. The
            // OccupiedEntry is the Entry's struct with its slot set.
            B::EntryInsertEntry => {
                let ec = elem_cty(&recv);
                let e = ctype(&ec);
                let vc = match &ec {
                    CTy::Tuple(es) => es[1].clone(),
                    _ => CTy::Unit,
                };
                let vt = ctype(&vc);
                let (ev, vv) = (self.tmp(), self.tmp());
                let drop_old = if needs_drop_c(self.p, &vc) {
                    self.want(Glue::Drop, &vc);
                    format!(" drop_{}(&o_{t});", mangle(&vc))
                } else {
                    String::new()
                };
                let _ = writeln!(
                    self.out,
                    "    {} {ev} = {}; {vt} {vv} = {};\n    if ({ev}.slot) {{ {vt} o_{t} = (({e}*){ev}.slot)->f1; (({e}*){ev}.slot)->f1 = {vv};{drop_old} }} else {{ {e} *n_{t} = ({e}*)lust_hash_insert_no_grow_slot({ev}.t, {ev}.hash, 0); n_{t}->f0 = {ev}.key; n_{t}->f1 = {vv}; {ev}.slot = n_{t}; }}\n    {dc} {t}; {t}.t = {ev}.t; {t}.hash = {ev}.hash; {t}.slot = {ev}.slot;",
                    ctype(&recv),
                    vals[0],
                    vals[1]
                );
                Some(t)
            }
            // The payload of an `Entry::Occupied` / `Entry::Vacant` pattern:
            // the Entry's fields in the variant's struct (same layout).
            // The probe key the vacant entry owns, moved out (the entry
            // is consumed, so its drop never runs).
            B::VacIntoKey => {
                let ev = self.tmp();
                let _ = writeln!(self.out, "    {} {ev} = {};", ctype(&recv), vals[0]);
                Some(format!("{ev}.key"))
            }
            B::EntryAsOccupied | B::EntryAsVacant => {
                let ev = self.tmp();
                let _ = writeln!(
                    self.out,
                    "    {} {ev} = {}; {dc} {t}; {t}.t = {ev}.t; {t}.hash = {ev}.hash; {t}.slot = {ev}.slot; {t}.key = {ev}.key;",
                    ctype(&recv),
                    vals[0]
                );
                Some(t)
            }
            B::OccKey | B::OccGet | B::OccGetMut => {
                let e = ctype(&elem_cty(&recv));
                let f = if b == B::OccKey { "f0" } else { "f1" };
                Some(format!("(&(({e}*){r}->slot)->{f})"))
            }
            B::OccIntoMut => {
                let e = ctype(&elem_cty(&recv));
                let ev = self.tmp();
                let _ = writeln!(self.out, "    {} {ev} = {};", ctype(&recv), vals[0]);
                Some(format!("(&(({e}*){ev}.slot)->f1)"))
            }
            // `mem::replace(self.get_mut(), value)`.
            B::OccInsert => {
                let ec = elem_cty(&recv);
                let e = ctype(&ec);
                let vt = match &ec {
                    CTy::Tuple(es) => ctype(&es[1]),
                    _ => "lust_Unit".into(),
                };
                let _ = writeln!(self.out, "    {vt} {t} = (({e}*){r}->slot)->f1; (({e}*){r}->slot)->f1 = {};", vals[1]);
                Some(t)
            }
            // hashbrown's `OccupiedEntry::remove_entry` erases the bucket
            // and moves the pair out; `remove` then drops the key.
            B::OccRemove | B::OccRemoveEntry => {
                let ec = elem_cty(&recv);
                let e = ctype(&ec);
                let ev = self.tmp();
                let _ = writeln!(
                    self.out,
                    "    {} {ev} = {}; {e} {t}; lust_hash_erase_at({ev}.t, lust_hash_index_of({ev}.t, {ev}.slot), &{t});",
                    ctype(&recv),
                    vals[0]
                );
                if b == B::OccRemoveEntry {
                    return Some(t);
                }
                let kc = key_cty(&recv);
                if needs_drop_c(self.p, &kc) {
                    self.want(Glue::Drop, &kc);
                    let _ = writeln!(self.out, "    drop_{}(&{t}.f0);", mangle(&kc));
                }
                Some(format!("{t}.f1"))
            }
            B::HashIterNew => {
                // A borrowing iterator walks the table in place; an owning
                // one takes the table, and the map's builder drops now
                // (the map is consumed by `into_iter`).
                let CTy::Hash(k, _) = dest else { return None };
                // A drain takes the map's table and leaves the map an
                // empty table with no allocation (hashbrown's
                // `RawTableInner::NEW`) until the drain drops.
                if k.is_drain() {
                    let _ = writeln!(
                        self.out,
                        "    {dc} {t}; {t}.t = {r}->t; {t}.orig = &{r}->t; lust_hash_init(&{r}->t, {t}.t.elem_size, {t}.t.elem_align); lust_hash_iter_init(&{t}.it, &{t}.t);"
                    );
                    return Some(t);
                }
                if !k.is_owning_iter() {
                    let _ = writeln!(self.out, "    {dc} {t}; lust_hash_iter_init(&{t}.it, &{r}->t);");
                    return Some(t);
                }
                let m = self.tmp();
                let _ = writeln!(self.out, "    {} {m} = {};", ctype(&recv), vals[0]);
                let s = builder_cty(&recv);
                if needs_drop_c(self.p, &s) {
                    self.want(Glue::Drop, &s);
                    let _ = writeln!(self.out, "    drop_{}(&{m}.s);", mangle(&s));
                }
                let _ = writeln!(self.out, "    {dc} {t}; {t}.t = {m}.t; lust_hash_iter_init(&{t}.it, &{t}.t);");
                Some(t)
            }
            B::HashIterLen => Some(format!("{r}->it.left")),
            B::HashReserve | B::HashExtendReserve => {
                // `extend` reserves the hint's lower bound into an empty
                // table, else half of it rounded up (wrapping, as std).
                let m = mangle(&recv);
                self.want(Glue::HashOf, &recv);
                let n = if b == B::HashReserve {
                    vals[1].clone()
                } else {
                    format!("(lust_hash_len(&{r}->t) == 0 ? (uint64_t)({0}) : ((uint64_t)({0}) + 1) / 2)", vals[1])
                };
                let _ = writeln!(self.out, "    lust_hash_reserve(&{r}->t, {n}, hof_{m}, &{r}->s);");
                Some("((lust_Unit){})".into())
            }
            B::HashIterNext => {
                let CTy::Hash(k, a) = &recv else { return None };
                let ec = elem_cty(&recv);
                let e = ctype(&ec);
                let f = self.tmp();
                let repoint = if k.is_owning_iter() || k.is_drain() { format!("{r}->it.t = &{r}->t; ") } else { String::new() };
                let _ = writeln!(self.out, "    {repoint}{e} *{f} = ({e}*)lust_hash_iter_next(&{r}->it, 0);");
                let map = a.len() == 2;
                // The part of an owned element an item leaves behind drops
                // when the item is taken (`map(|(k, _)| k)` and kin).
                let drop_part = |this: &mut Self, part: usize| {
                    let pc = a[part].clone();
                    if needs_drop_c(this.p, &pc) {
                        this.want(Glue::Drop, &pc);
                        let _ = writeln!(this.out, "    if ({f}) drop_{}(&{f}->f{part});", mangle(&pc));
                    }
                };
                let item = match k {
                    HashTy::IterPairs => {
                        let it = CTy::Tuple(vec![CTy::Ref(Box::new(a[0].clone())), CTy::Ref(Box::new(a[1].clone()))]);
                        self.note_held(&it);
                        format!("(({}){{ &{f}->f0, &{f}->f1 }})", ctype(&it))
                    }
                    HashTy::IterKeys if map => format!("(&{f}->f0)"),
                    HashTy::IterKeys => f.clone(),
                    HashTy::IterValues => format!("(&{f}->f1)"),
                    HashTy::IntoPairs | HashTy::DrainPairs | HashTy::DrainKeys => format!("(*{f})"),
                    HashTy::IntoKeys if map => {
                        drop_part(self, 1);
                        format!("({f}->f0)")
                    }
                    HashTy::IntoKeys => format!("(*{f})"),
                    HashTy::IntoValues => {
                        drop_part(self, 0);
                        format!("({f}->f1)")
                    }
                    _ => return None,
                };
                let some = self.make_variant(dest, 1, &[item]);
                let none = self.make_variant(dest, 0, &[]);
                let _ = writeln!(self.out, "    {dc} {t} = {f} ? {some} : {none};");
                Some(t)
            }
            _ => None,
        }
    }

    /// The lookup type `Q` of a `&Q` argument and a `Q*` C expression for
    /// it (a fat `&str` or `&[T]` goes through a temporary).
    fn q_arg(&mut self, t: &CTy, v: &str) -> (CTy, String) {
        match t {
            CTy::Ref(inner) if **inner == CTy::Str => {
                let q = self.tmp();
                let _ = writeln!(self.out, "    lust_str {q} = {v};");
                (CTy::Str, format!("(&{q})"))
            }
            CTy::Ref(inner) => ((**inner).clone(), format!("({v})")),
            _ => {
                let q = self.tmp();
                let _ = writeln!(self.out, "    {} {q} = {v};", ctype(t));
                (t.clone(), format!("(&{q})"))
            }
        }
    }

    /// Requests the per-(table, Q) lookup glue and returns its mangled
    /// key.
    fn want_q(&mut self, table: &CTy, q: &CTy) -> String {
        let key = CTy::Tuple(vec![table.clone(), q.clone()]);
        self.want(Glue::HashKeyQ, &key);
        self.want(Glue::HashEqQ, &key);
        mangle(&key)
    }
}
