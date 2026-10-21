// LLVM IR backend for release builds (`LUST_RELEASE_BACKEND=llvm` with `LUST_RELEASE_C=1`).
//
// Each fn body becomes one LLVM IR fn `fl_<id>` in its unit's `.ll` text, next to the
// unit's C. The LLVM fn owns the frame: an alloca per local and per drop or move flag,
// the control flow (blocks, branches, switches, returns) and the unwinding: a call or a
// statement with a cleanup entry is an `invoke`, its landing pad keeps the exception and
// runs the cleanup blocks, and the end of a cleanup ladder is `resume`. There is no frame
// struct and no ladder state store (the C backend's unwind tables scheme, cgen/unwind.rs).
// The runtime's C++ throw and catch (runtime/unwind.cc) stay as they are.
//
// A statement whose form has no native lowering runs as a small C helper `lh_<id>_<n>`
// cut from cgen's own C for that statement (`FnGen::stmt`, `FnGen::term`): it takes
// pointers to the locals and flags its text names, so the C and the LLVM code share one
// frame. A unit compiles as one module (cc.rs links the C module's bitcode into the LLVM
// module before -O2), so the helpers inline (always_inline) and SROA promotes the frame
// as for native code.
//
// ABI: `fl_<id>` takes scalars (ints, floats, thin pointers) by value and every other
// value by pointer to a copy the callee owns; an aggregate result goes through a leading
// sret pointer. C callers (glue, vtable shims, trampolines, helpers) keep calling
// `f_<id>` with the C signature: a C wrapper in the unit forwards to `fl_<id>`.
use super::unwind::{is_ident, skip_lit};
use super::*;

/// True when this thread emits LLVM IR for release C fn bodies: release C names, the
/// `LUST_RELEASE_BACKEND=llvm` switch, and a program whose panics abort or unwind with
/// tables (the flag scheme stays C).
pub(crate) fn on(p: &Program) -> bool {
    static ENV: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let env = *ENV.get_or_init(|| std::env::var("LUST_RELEASE_BACKEND").is_ok_and(|v| v == "llvm"));
    env && names::release() && (!p.unwind || p.unwind_tables)
}

/// How the internal ABI passes a C value: not at all (zero-sized), in a register as the
/// given LLVM type with its extension attribute, as the bits of a small aggregate in one
/// integer register (`Bits(bytes)`: a newtype id, a small `Option`; rustc passes these as
/// integers too), or by pointer to memory.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Pass {
    Skip,
    Scalar(&'static str, &'static str),
    Bits(u64),
    /// A 16-byte aggregate (a `&str`, a slice, `Option<u64>`) as two 8-byte words.
    Pair,
    Mem,
}

/// The C type of a `Pass::Pair` result: clang returns it in two registers, as `{ i64, i64 }`.
pub(crate) const PAIR_TYPEDEF: &str = "typedef struct { uint64_t a, b; } ll_pair;\n";

/// The LLVM and C integer types of a `Pass::Bits` value of `n` bytes.
fn bits_types(n: u64) -> (&'static str, &'static str) {
    match n {
        1 => ("i8", "uint8_t"),
        2 => ("i16", "uint16_t"),
        4 => ("i32", "uint32_t"),
        _ => ("i64", "uint64_t"),
    }
}

pub(super) fn pass_of(p: &Program, t: &CTy) -> Pass {
    if c_size_align(p, t).0 == 0 {
        return Pass::Skip;
    }
    let c = ctype(t);
    if c.ends_with('*') || c.starts_with("Fp_") {
        return Pass::Scalar("ptr", "");
    }
    match c.as_str() {
        "uint8_t" => Pass::Scalar("i8", "zeroext"),
        "int8_t" => Pass::Scalar("i8", "signext"),
        "uint16_t" => Pass::Scalar("i16", "zeroext"),
        "int16_t" => Pass::Scalar("i16", "signext"),
        "uint32_t" | "int32_t" => Pass::Scalar("i32", ""),
        "uint64_t" | "int64_t" => Pass::Scalar("i64", ""),
        "double" => Pass::Scalar("double", ""),
        "float" => Pass::Scalar("float", ""),
        // An aggregate of exactly 1, 2, 4 or 8 bytes (exact layout) travels as its bits.
        _ => match c_layout(p, t) {
            Some(l) if matches!(l.size, 1 | 2 | 4 | 8) && bits_on() => Pass::Bits(l.size),
            Some(l) if l.size == 16 && bits_on() && pair_on() => Pass::Pair,
            _ => Pass::Mem,
        },
    }
}

/// True unless `LUST_LL_PAIR=0` (16-byte aggregates by pointer, to measure `Pass::Pair`).
fn pair_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("LUST_LL_PAIR").map_or(true, |v| v != "0"))
}

/// True unless `LUST_LL_BITS=0` (small aggregates by pointer, to measure `Pass::Bits`).
fn bits_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("LUST_LL_BITS").map_or(true, |v| v != "0"))
}

/// True unless `LUST_LL_FACTS=0`: the LLVM fns carry the facts Rust gives references
/// (`ref_facts`). The switch exists to measure their payoff.
fn facts_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("LUST_LL_FACTS").map_or(true, |v| v != "0"))
}

/// The LLVM attributes Rust's rules give a thin pointer of semantic type `ty` passed or
/// returned by value, as rustc emits them: a reference or `Box` is non-null, aligned and
/// dereferenceable for its pointee's size (when its layout is exact); `&mut T`, `Box<T>`
/// and `&T` of a type without interior mutability are `noalias` (a parameter only), and
/// such a `&T` is `readonly`.
fn ref_facts(p: &Program, tys: &Tys, ty: Ty, param: bool) -> String {
    if !facts_on() {
        return String::new();
    }
    let (pointee, unique, shared) = match tys.kind(ty) {
        TyKind::Ref(_, m, e) => (e, m == Mut::Mut, m == Mut::Shared),
        TyKind::Adt(..) if tys.builtin_of(ty) == Some(BuiltinTy::Boxed) => match tys.adt_first_ty_arg(ty) {
            Some(e) => (e, true, false),
            None => return String::new(),
        },
        _ => return String::new(),
    };
    let pc = cty(tys, pointee);
    let Some(l) = c_layout(p, &pc) else { return String::new() };
    let mut a = format!("nonnull align {}", l.align.max(1));
    if l.size > 0 {
        let _ = write!(a, " dereferenceable({})", l.size);
    }
    // Freeze as rustc asks it: no `UnsafeCell` inline (the semantic check knows std's
    // cell, once and lazy models; the C form knows the sync types). A `LocalKey` is a
    // slot word the runtime may fill in place.
    let freeze = shared
        && !crate::check::collect::interior_mut(p, tys, pointee)
        && is_freeze_c(p, &pc, &mut HashSet::new())
        && tys.builtin_of(pointee) != Some(BuiltinTy::LocalKey);
    if param && (unique || freeze) {
        a.push_str(" noalias");
    }
    if param && freeze {
        a.push_str(" readonly");
    }
    a
}

/// True unless `LUST_LL_NATIVE=0`: simple statements lower to LLVM IR directly instead of
/// C helpers (`FnGen::ll_native_stmt`).
fn native_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("LUST_LL_NATIVE").map_or(true, |v| v != "0"))
}

/// One step from a place's base to its address (`FnGen::ll_plan`).
#[derive(Clone, Debug)]
enum PStep {
    /// Load the thin pointer stored here (a reference or `Box`) to a value of this C type.
    Load(CTy),
    /// Load the pointer to an `Rc`/`Arc` count block stored here; its value of this C type
    /// is at this offset in the block (two words, then the value at its alignment).
    LoadAt(CTy, u64),
    /// Element `local` of the Vec, slice (its fat value here) or array of this length here,
    /// of this C type, after the bounds check that panics at this location (cgen's
    /// `index_unw`).
    Index(usize, Option<u64>, CTy, LocWord),
    /// Move this many bytes into the value; the C member path, for the layout check.
    Offset(u64, String),
}

/// A place lowered natively: its local, the steps, and the C type at the end.
struct Plan {
    local: usize,
    steps: Vec<PStep>,
    ty: CTy,
}

/// One operand of a value built in place (`FnGen::ll_shape`): its offset in the value and
/// its C type.
struct Part<'o> {
    op: &'o Operand,
    off: u64,
    ty: CTy,
}

/// A value an assignment builds in place: its operands at their offsets, the tag or niche
/// scalar of an enum variant (offset, bytes, bits), and whether it starts zeroed (cgen's
/// `zero_lit` form: no fields and no tag).
struct Shape<'o> {
    parts: Vec<Part<'o>>,
    tag: Option<(u64, u64, u128)>,
    zero: bool,
}

/// An operand read before its store (`FnGen::ll_native_parts`).
enum Held {
    Skip,
    /// An SSA value of this LLVM type: a scalar, or the bits of a small aggregate.
    Ssa(&'static str, String),
    /// The address of the bytes to copy and its alignment; true: a temporary whose lifetime
    /// ends at the copy.
    Mem(String, u64, bool),
}

/// The text of an LLVM `c"..."` string constant for `bytes`.
fn ll_bytes_lit(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len());
    for &b in bytes {
        if (0x20..0x7f).contains(&b) && b != b'"' && b != b'\\' {
            s.push(b as char);
        } else {
            let _ = write!(s, "\\{b:02X}");
        }
    }
    s
}

/// An LLVM integer literal of `size` bytes for the bit pattern `bits`, written signed.
fn ll_int_lit(bits: u128, size: u64) -> String {
    let w = size * 8;
    let m = bits & scalar_mask(size);
    if w < 128 && (m >> (w - 1)) & 1 == 1 { ((m as i128) - (1i128 << w)).to_string() } else { m.to_string() }
}

/// A name of the fn's frame that a statement's C reads.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Name {
    Local(usize),
    Drop(usize),
    Move(usize, usize),
    Ltc,
    Ex,
}

/// One fn's LLVM side: its definition, the declarations it names, and its helpers' C
/// (cc.rs links that module internalized, so the helpers vanish once inlined).
#[derive(Default)]
pub struct LlFn {
    pub def: String,
    pub decls: BTreeSet<String>,
    pub helpers: String,
    /// The fn's size for cross-unit inlining (`ll_inline_set`): statements and blocks of its
    /// body outside cleanup, whatever form they take in IR.
    pub cost: u32,
    /// False when the fn has no C side (no helpers): only its C ABI wrapper names C types.
    pub c_side: bool,
}

/// The per-fn state of LLVM emission.
struct Ll {
    tag: String,
    /// Helper definitions (C), in order.
    helpers: String,
    n_helpers: usize,
    /// Locals with static storage (promoted constants, byte string temps): C file statics.
    statics: Vec<bool>,
    /// The cleanup blocks each landing pad enters.
    pads: BTreeSet<u32>,
    decls: BTreeSet<String>,
    body: String,
    /// The number of continuation blocks made so far.
    conts: usize,
    /// An internal error (an unsupported C form in a helper): the driver reports it.
    error: Option<String>,
    /// `_Static_assert`s of the field offsets native code uses, for the helper C.
    asserts: BTreeSet<String>,
    /// Temporaries native code needs (call arguments and results), as entry-block allocas.
    allocas: String,
    /// Per block: the locals whose drop flag may be set at its terminator (`flags_maybe_set`).
    flags_at_term: Vec<Vec<bool>>,
    /// The span and cleanup entry of the statement or terminator being lowered: a bounds
    /// check in its address code panics there (`PStep::Index`).
    span: Span,
    unwind: Option<u32>,
    /// The C types whose member offsets `asserts` checks: the C side must define them.
    assert_types: Vec<CTy>,
}

impl FnGen<'_, '_> {
    /// The frame names `text` reads (sorted, deduplicated): locals, their drop and move
    /// flags, the caller location `ltc`, the exception slot `ex`.
    fn frame_names(&self, text: &str) -> Vec<Name> {
        let n = self.local_cty.len();
        let b = text.as_bytes();
        let mut out = BTreeSet::new();
        let mut i = 0;
        while i < b.len() {
            match b[i] {
                b'"' | b'\'' => i = skip_lit(b, i),
                c if is_ident(c) && (i == 0 || !is_ident(b[i - 1])) => {
                    let start = i;
                    while i < b.len() && is_ident(b[i]) {
                        i += 1;
                    }
                    // A member (`x.l3`, `p->d1`) is not a frame name.
                    let member = start > 0 && (b[start - 1] == b'.' || (start > 1 && &b[start - 2..start] == b"->"));
                    if member {
                        continue;
                    }
                    let w = &text[start..i];
                    // A cgen number: digits with no leading zero, under `bound`.
                    let num = |s: &str, bound: usize| {
                        let ok = !s.is_empty() && s.bytes().all(|c| c.is_ascii_digit()) && (s == "0" || !s.starts_with('0'));
                        if ok { s.parse::<usize>().ok().filter(|&k| k < bound) } else { None }
                    };
                    let name = match w.as_bytes()[0] {
                        _ if w == "ltc_so" || w == "ltc_low" => Some(Name::Ltc),
                        _ if w == "ex" => Some(Name::Ex),
                        b'l' => num(&w[1..], n).map(Name::Local),
                        b'd' => num(&w[1..], n).filter(|&k| self.local_drop[k] && self.dflags.keeps(k as Local)).map(Name::Drop),
                        b'm' => w[1..].split_once('_').and_then(|(a, k)| {
                            let l = num(a, n)?;
                            Some(Name::Move(l, num(k, self.move_paths[l].len())?))
                        }),
                        _ => None,
                    };
                    if let Some(nm) = name {
                        out.insert(nm);
                    }
                }
                c if c.is_ascii_digit() => {
                    while i < b.len() && is_ident(b[i]) {
                        i += 1;
                    }
                }
                _ => i += 1,
            }
        }
        out.into_iter().collect()
    }

    /// Makes a C helper of statement text `text` (and, with `ret`, a value: its C type and
    /// expression, returned after the text) and returns the LLVM call operands: the
    /// callee name, its LLVM return type with its extension, and the argument list.
    fn ll_helper(&self, ll: &mut Ll, text: &str, ret: Option<(&str, &str, Pass)>) -> (String, String, String) {
        let names = self.frame_names(&format!("{text}{}", ret.map_or("", |r| r.1)));
        if contains_word(text, "return") || text.contains("goto bb") {
            ll.error.get_or_insert_with(|| {
                format!(
                    "internal: LLVM backend: a statement of `{}` jumps out of its C ({}), which a helper cannot hold",
                    self.p.display_path(self.p.fn_info(self.body.fn_id).name),
                    text.trim().chars().take(120).collect::<String>()
                )
            });
        }
        let name = format!("lh_{}_{}", ll.tag, ll.n_helpers);
        ll.n_helpers += 1;
        let mut params = Vec::new();
        let mut args = Vec::new();
        let mut ex = false;
        for nm in &names {
            match *nm {
                Name::Local(l) if ll.statics[l] => {}
                Name::Local(l) => {
                    params.push(format!("{} *q{l}", ctype(&self.local_cty[l])));
                    args.push(format!("ptr %l{l}"));
                }
                Name::Drop(l) => {
                    params.push(format!("uint8_t *qd{l}"));
                    args.push(format!("ptr %d{l}"));
                }
                Name::Move(l, k) => {
                    params.push(format!("uint8_t *qm{l}_{k}"));
                    args.push(format!("ptr %m{l}_{k}"));
                }
                Name::Ltc => {
                    params.push("const uint64_t **qltc_so, uint64_t *qltc_low".to_string());
                    args.push("ptr %ltc_so, ptr %ltc_low".to_string());
                }
                Name::Ex => ex = true,
            }
        }
        let (cret, llret) = match ret {
            Some((ct, _, Pass::Scalar(t, ext))) => (ct.to_string(), if ext.is_empty() { t.to_string() } else { format!("{ext} {t}") }),
            _ => ("void".to_string(), "void".to_string()),
        };
        let plist = if params.is_empty() { "void".to_string() } else { params.join(", ") };
        let _ = writeln!(ll.helpers, "__attribute__((visibility(\"hidden\"), always_inline)) {cret} {name}({plist}) {{");
        if ex {
            ll.helpers.push_str("  lust_exc ex; (void)ex;\n");
        }
        ll.helpers.push_str(text);
        if let Some((_, e, _)) = ret {
            let _ = writeln!(ll.helpers, "  return ({e});");
        }
        ll.helpers.push_str("}\n");
        let decl_params: Vec<&str> = args.iter().map(|_| "ptr").collect();
        ll.decls.insert(format!("declare {llret} @{name}({})", decl_params.join(", ")));
        (name, llret, args.join(", "))
    }

    /// Emits a call of a helper (`invoke` when `unwind` names a cleanup entry), and returns
    /// the value name when it has one.
    fn ll_call(&self, ll: &mut Ll, callee: &(String, String, String), unwind: Option<u32>) -> Option<String> {
        let (name, ret, args) = callee;
        let v = if ret == "void" {
            None
        } else {
            ll.conts += 1;
            Some(format!("%v{}", ll.conts))
        };
        let assign = v.as_ref().map_or(String::new(), |v| format!("{v} = "));
        match unwind {
            Some(u) => {
                ll.conts += 1;
                let cont = format!("c{}", ll.conts);
                ll.pads.insert(u);
                let _ = writeln!(ll.body, "  {assign}invoke {ret} @{name}({args}) to label %{cont} unwind label %lp{u}\n{cont}:");
            }
            None => {
                let _ = writeln!(ll.body, "  {assign}call {ret} @{name}({args})");
            }
        }
        v
    }

    /// The C of statement `s` (block `bi`, index `si`) as cgen writes it for a fn with no
    /// frame struct.
    fn stmt_text(&mut self, bi: usize, si: usize, s: &Stmt) -> String {
        self.at = (bi as u32, si as u32);
        self.unw = self.stmt_action(bi, si).filter(|_| !matches!(s.kind, StmtKind::StorageDead(_) | StmtKind::FakeRead(_)));
        let saved = std::mem::take(&mut self.out);
        self.stmt(&s.kind, s.span);
        self.unw = None;
        std::mem::replace(&mut self.out, saved)
    }

    /// An operand as an LLVM value of its scalar type: a plain local's load or a
    /// constant, else a helper that computes it.
    fn ll_operand(&mut self, ll: &mut Ll, o: &Operand, span: Span) -> (String, Pass) {
        if native_on()
            && let Some((t, _)) = self.ll_scalar_ok(ll, o)
        {
            let pass = pass_of(self.p, &t);
            return (self.ll_scalar(ll, o), pass);
        }
        match o {
            Operand::Copy(pl) | Operand::Move(pl) if pl.proj.is_empty() && !ll.statics[pl.local as usize] => {
                let l = pl.local as usize;
                let pass = pass_of(self.p, &self.local_cty[l]);
                if let Pass::Scalar(t, _) = pass {
                    ll.conts += 1;
                    let v = format!("%v{}", ll.conts);
                    let _ = writeln!(ll.body, "  {v} = load {t}, ptr %l{l}");
                    return (v, pass);
                }
            }
            Operand::Const(Const::Bool(b)) => return ((*b as u8).to_string(), Pass::Scalar("i8", "zeroext")),
            _ => {}
        }
        let loc = self.loc(span);
        let mut post = Vec::new();
        let saved = std::mem::take(&mut self.out);
        let (e, t) = self.operand(o, &loc, &mut post);
        let pre = std::mem::replace(&mut self.out, saved);
        let pass = pass_of(self.p, &t);
        let ct = ctype(&t);
        let h = self.ll_helper(ll, &pre, Some((&ct, &e, pass)));
        (self.ll_call(ll, &h, None).unwrap_or_else(|| "0".into()), pass)
    }

    /// Generates fn `fl_<id>` and its C side (helpers, the C ABI wrapper `f_<id>`, the
    /// trampoline) into `self.out`. Returns the LLVM definition and declarations, or an
    /// internal error.
    pub(super) fn function_ll(&mut self) -> Result<LlFn, String> {
        let p = self.p;
        let fid = self.body.fn_id;
        let slot = self.slots.of(fid);
        let tag = names::fn_tag(slot);
        let n = self.body.blocks.len();
        let mut reachable = vec![false; n];
        let mut stack = vec![0usize];
        while let Some(b) = stack.pop() {
            if std::mem::replace(&mut reachable[b], true) {
                continue;
            }
            stack.extend(succ(&self.body.blocks[b].term).into_iter().map(|s| s.0 as usize));
            stack.extend(self.body.stmt_unwind.iter().filter(|e| e.0.0 as usize == b).map(|e| e.2.0 as usize));
        }
        let order: Vec<usize> = (0..n).filter(|&b| reachable[b]).collect();
        let cost = order
            .iter()
            .filter(|&&b| !self.cleanup.get(b).copied().unwrap_or(false))
            .map(|&b| 1 + self.body.blocks[b].stmts.iter().filter(|s| !matches!(s.kind, StmtKind::StorageDead(_) | StmtKind::FakeRead(_))).count() as u32)
            .sum();
        let nl = self.local_cty.len();
        let statics: Vec<bool> = (0..nl)
            .map(|i| self.body.promoted.contains(&(i as Local)) || self.byte_blobs.get(i).is_some_and(|b| b.is_some()))
            .collect();
        let mut ll = Ll {
            tag: tag.clone(),
            helpers: String::new(),
            n_helpers: 0,
            statics,
            pads: BTreeSet::new(),
            decls: BTreeSet::new(),
            body: String::new(),
            conts: 0,
            error: None,
            asserts: BTreeSet::new(),
            allocas: String::new(),
            flags_at_term: self.flags_maybe_set(),
            span: Span::default(),
            unwind: None,
            assert_types: Vec::new(),
        };
        // Str literal caches (`kstr`) are on: the slots and their interning become IR globals
        // and prologue code below (`ll_kstr_init`).
        self.kdecl_at = Some(0);
        for &bi in &order {
            let block = self.body.block(Bb(bi as u32));
            let cleanup = self.cleanup.get(bi).copied().unwrap_or(false);
            let _ = writeln!(ll.body, "bb{bi}:");
            for (si, s) in block.stmts.iter().enumerate() {
                if matches!(s.kind, StmtKind::StorageDead(_) | StmtKind::FakeRead(_)) {
                    continue;
                }
                let unwind = if cleanup || !p.unwind { None } else { self.stmt_unw.get(&(bi as u32, si as u32)).copied() };
                self.at = (bi as u32, si as u32);
                (ll.span, ll.unwind) = (s.span, unwind);
                if native_on() && self.ll_native_stmt(&mut ll, s, unwind) {
                    continue;
                }
                let text = self.stmt_text(bi, si, s);
                if text.trim().is_empty() {
                    continue;
                }
                let h = self.ll_helper(&mut ll, &text, None);
                self.ll_call(&mut ll, &h, unwind);
            }
            let term_unwind = if cleanup { None } else { self.stmt_unw.get(&(bi as u32, block.stmts.len() as u32)).copied() };
            self.at = (bi as u32, block.stmts.len() as u32);
            (ll.span, ll.unwind) = (block.term_span, term_unwind.filter(|_| p.unwind));
            self.ll_term(&mut ll, bi, cleanup, term_unwind.filter(|_| p.unwind));
        }
        if let Some(e) = ll.error.take() {
            return Err(e);
        }
        // The landing pads: keep the exception, enter the cleanup block.
        for &u in &ll.pads {
            let _ = writeln!(
                ll.body,
                "lp{u}:\n  %lpv{u} = landingpad {{ ptr, i32 }} cleanup\n  store {{ ptr, i32 }} %lpv{u}, ptr %exn\n  br label %bb{u}"
            );
        }
        // The compile-time promoted values' decls (`kstatic_decl`) come first: a value
        // that holds strs adds literals and an entry write to the entry helper.
        let kdecls: Vec<Option<String>> = (0..self.local_cty.len()).map(|i| if ll.statics[i] { self.kstatic_decl(i) } else { None }).collect();
        let kstr_init = self.ll_kstr_init(&mut ll);
        let def = self.ll_define(&mut ll, kstr_init.as_deref());
        // The C sides: the helpers with the macros and statics they read; then the C ABI
        // wrapper and the trampoline, which stay in the unit's plain C. A fn with no helpers
        // (and no literal or constant prologue) has no helper side: nothing in C reads its
        // frame, so its layout checks and its locals' types would only make the unit's C
        // bigger and change it more often.
        let c_side = ll.n_helpers > 0 || kstr_init.is_some() || kdecls.iter().any(Option::is_some) || !self.prelude.is_empty();
        let helpers = if c_side {
            for t in std::mem::take(&mut ll.assert_types) {
                collect_types(&t, &mut self.sig_types);
            }
            let saved = std::mem::take(&mut self.out);
            self.ll_c_side(&ll, kstr_init.as_deref(), &kdecls);
            std::mem::replace(&mut self.out, saved)
        } else {
            self.kstrs.clear();
            String::new()
        };
        let wrapper = self.ll_wrapper(slot);
        let _ = writeln!(self.out, "/* {} */\n{wrapper}{}", p.display_path(p.fn_info(fid).name), trampoline(p, fid, slot));
        ll.decls.insert("declare i32 @__gcc_personality_v0(...)".into());
        // The inline cost on a comment line above the fn, for reading the IR.
        let def = format!("; cost {cost}\n{def}");
        Ok(LlFn { def, decls: std::mem::take(&mut ll.decls), helpers, cost, c_side })
    }

    /// The terminator of block `bi`.
    fn ll_term(&mut self, ll: &mut Ll, bi: usize, cleanup: bool, unwind: Option<u32>) {
        let block = self.body.block(Bb(bi as u32));
        let span = block.term_span;
        match &block.term {
            Terminator::Goto(t) => {
                let _ = writeln!(ll.body, "  br label %bb{}", t.0);
            }
            Terminator::If(o, a, b) => {
                let (v, pass) = self.ll_operand(ll, o, span);
                let t = match pass {
                    Pass::Scalar(t, _) => t,
                    _ => "i8",
                };
                ll.conts += 1;
                let c = format!("%v{}", ll.conts);
                let _ = writeln!(ll.body, "  {c} = icmp ne {t} {v}, 0\n  br i1 {c}, label %bb{}, label %bb{}", a.0, b.0);
            }
            Terminator::Switch(o, cases, other) => {
                let (v, pass) = self.ll_operand(ll, o, span);
                let t = match pass {
                    Pass::Scalar(t, _) => t,
                    _ => "i32",
                };
                let _ = write!(ll.body, "  switch {t} {v}, label %bb{} [", other.0);
                for (val, b) in cases {
                    let _ = write!(ll.body, " {t} {val}, label %bb{}", b.0);
                }
                ll.body.push_str(" ]\n");
            }
            Terminator::Call { target: CallTarget::Fn(f), args, dest, next, unwind: call_unwind }
                if native_on() && {
                    let dest_clear = !ll.flags_at_term[bi][dest.local as usize];
                    let span = self.body.blocks[bi].term_span;
                    self.ll_native_call(ll, *f, args, dest, dest_clear, span, if cleanup || !self.p.unwind { None } else { call_unwind.map(|u| u.0) })
                } =>
            {
                let _ = writeln!(ll.body, "  br label %bb{}", next.0);
            }
            Terminator::Call { target: CallTarget::Builtin(b), args, dest, next, .. } if native_on() && self.ll_native_builtin(ll, *b, args, dest) => {
                let _ = writeln!(ll.body, "  br label %bb{}", next.0);
            }
            Terminator::Call { next, unwind: call_unwind, .. } => {
                self.unw = self.stmt_action(bi, block.stmts.len());
                let saved = std::mem::take(&mut self.out);
                let term = block.term.clone();
                self.term(&term, span, Some(next.0 as usize));
                self.unw = None;
                let text = std::mem::replace(&mut self.out, saved);
                let h = self.ll_helper(ll, &text, None);
                let u = if cleanup || !self.p.unwind { None } else { call_unwind.map(|u| u.0) };
                self.ll_call(ll, &h, u);
                let _ = writeln!(ll.body, "  br label %bb{}", next.0);
            }
            Terminator::Return => match pass_of(self.p, &self.local_cty[0]) {
                Pass::Scalar(t, _) => {
                    ll.conts += 1;
                    let _ = writeln!(ll.body, "  %v{0} = load {t}, ptr %l0\n  ret {t} %v{0}", ll.conts);
                }
                Pass::Bits(n) => {
                    ll.conts += 1;
                    let t = bits_types(n).0;
                    let _ = writeln!(ll.body, "  %v{0} = load {t}, ptr %l0, align {n}\n  ret {t} %v{0}", ll.conts);
                }
                Pass::Pair => {
                    ll.conts += 1;
                    let _ = writeln!(
                        ll.body,
                        "  %pa{0} = load i64, ptr %l0, align 8\n  %pq{0} = getelementptr inbounds i8, ptr %l0, i64 8\n  %pb{0} = load i64, ptr %pq{0}, align 8\n  %pv{0} = insertvalue {{ i64, i64 }} poison, i64 %pa{0}, 0\n  %pw{0} = insertvalue {{ i64, i64 }} %pv{0}, i64 %pb{0}, 1\n  ret {{ i64, i64 }} %pw{0}",
                        ll.conts
                    );
                }
                _ => ll.body.push_str("  ret void\n"),
            },
            Terminator::Unreachable | Terminator::MatchExhausted if cleanup && self.p.unwind => {
                ll.conts += 1;
                let _ = writeln!(ll.body, "  %v{0} = load {{ ptr, i32 }}, ptr %exn\n  resume {{ ptr, i32 }} %v{0}", ll.conts);
            }
            // An exhaustive match's otherwise edge (see `assume_unreachable`).
            Terminator::MatchExhausted if super::assume_unreachable(self.p) => ll.body.push_str("  unreachable\n"),
            Terminator::Unreachable | Terminator::MatchExhausted => {
                ll.decls.insert("declare void @abort() noreturn nounwind".into());
                ll.body.push_str("  call void @abort()\n  unreachable\n");
            }
            Terminator::Panic(_) => {
                self.unw = self.stmt_action(bi, block.stmts.len());
                let saved = std::mem::take(&mut self.out);
                let term = block.term.clone();
                self.term(&term, span, None);
                self.unw = None;
                let text = std::mem::replace(&mut self.out, saved);
                let h = self.ll_helper(ll, &text, None);
                self.ll_call(ll, &h, unwind);
                ll.body.push_str("  unreachable\n");
            }
        }
    }

    /// The prologue helper that interns the fn's str literals (`kstr`) and its batched
    /// constant locals (`kbatch_local`), if it has any (`kintern_block`; `ll_c_side`
    /// declares the slots and the flag it reads).
    fn ll_kstr_init(&mut self, ll: &mut Ll) -> Option<String> {
        self.kdecl_at = None;
        let block = self.kintern_block("  ");
        if block.is_empty() {
            return None;
        }
        // The slots and the flag are file statics on the C side (`ll_c_side`).
        let body: String = block.lines().filter(|l| !l.trim_start().starts_with("static ")).map(|l| format!("{l}\n")).collect();
        let name = format!("lh_{}_k", ll.tag);
        let _ = write!(ll.helpers, "__attribute__((visibility(\"hidden\"), always_inline)) void {name}(void) {{\n{body}}}\n");
        ll.decls.insert(format!("declare void @{name}()"));
        Some(name)
    }

    /// The LLVM definition of `fl_<id>`.
    fn ll_define(&mut self, ll: &mut Ll, kstr_init: Option<&str>) -> String {
        let p = self.p;
        let fid = self.body.fn_id;
        let info = p.fn_info(fid);
        let mut params: Vec<String> = Vec::new();
        let mut entry = String::new();
        let mut is_param = vec![false; self.local_cty.len()];
        let ret_pass = pass_of(p, &self.local_cty[0]);
        let (ret_size, ret_align) = c_size_align(p, &self.local_cty[0]);
        let ret_ll = match ret_pass {
            Pass::Scalar("ptr", _) => {
                let facts = ref_facts(p, &self.body.tys, self.body.locals[0].ty, false);
                if facts.is_empty() { "ptr".to_string() } else { format!("{facts} ptr") }
            }
            Pass::Scalar(t, ext) => {
                if ext.is_empty() {
                    t.to_string()
                } else {
                    format!("{ext} {t}")
                }
            }
            Pass::Bits(n) => bits_types(n).0.to_string(),
            Pass::Pair => "{ i64, i64 }".to_string(),
            Pass::Mem => {
                // No `sret`: C callers declare this pointer plainly (`ll_proto`).
                params.push(format!("ptr noalias nocapture noundef nonnull align {ret_align} dereferenceable({ret_size}) %l0"));
                is_param[0] = true;
                "void".to_string()
            }
            Pass::Skip => "void".to_string(),
        };
        for i in 1..=self.body.arg_count.min(self.local_cty.len() - 1) {
            let t = &self.local_cty[i];
            let (size, align) = c_size_align(p, t);
            match pass_of(p, t) {
                Pass::Skip => {}
                Pass::Scalar(ty, ext) => {
                    let mut ext = if ext.is_empty() { String::new() } else { format!("{ext} ") };
                    if ty == "ptr" {
                        let facts = ref_facts(p, &self.body.tys, self.body.locals[i].ty, true);
                        if !facts.is_empty() {
                            ext = format!("{facts} ");
                        }
                    }
                    params.push(format!("{ty} {ext}noundef %p{i}"));
                    let _ = writeln!(entry, "  %l{i} = alloca {ty}, align {align}\n  store {ty} %p{i}, ptr %l{i}");
                    is_param[i] = true;
                }
                // No `noundef`: an aggregate's bits may hold padding or an inactive variant's
                // bytes (an `Ok(())` leaves its error word unwritten).
                Pass::Bits(n) => {
                    let ty = bits_types(n).0;
                    params.push(format!("{ty} %p{i}"));
                    let _ = writeln!(entry, "  %l{i} = alloca [{size} x i8], align {}\n  store {ty} %p{i}, ptr %l{i}, align {n}", align.max(n));
                    is_param[i] = true;
                }
                Pass::Pair => {
                    params.push(format!("i64 %p{i}a, i64 %p{i}b"));
                    let _ = writeln!(
                        entry,
                        "  %l{i} = alloca [16 x i8], align {}\n  store i64 %p{i}a, ptr %l{i}, align 8\n  %l{i}h = getelementptr inbounds i8, ptr %l{i}, i64 8\n  store i64 %p{i}b, ptr %l{i}h, align 8",
                        align.max(8)
                    );
                    is_param[i] = true;
                }
                Pass::Mem => {
                    params.push(format!("ptr noalias nocapture noundef nonnull align {align} dereferenceable({size}) %l{i}"));
                    is_param[i] = true;
                }
            }
        }
        if crate::check::caller::is_track_caller(p, fid) {
            params.push("ptr noundef %ltc_so.v, i64 noundef %ltc_low.v".into());
            entry.push_str("  %ltc_so = alloca ptr, align 8\n  store ptr %ltc_so.v, ptr %ltc_so\n  %ltc_low = alloca i64, align 8\n  store i64 %ltc_low.v, ptr %ltc_low\n");
        }
        let mut allocas = String::new();
        for (i, t) in self.local_cty.iter().enumerate() {
            if is_param[i] || ll.statics[i] {
                continue;
            }
            let (size, align) = c_size_align(p, t);
            match pass_of(p, t) {
                Pass::Scalar(ty, _) => {
                    let _ = writeln!(allocas, "  %l{i} = alloca {ty}, align {align}");
                }
                // The return local is read back as one integer (`Terminator::Return`).
                Pass::Bits(n) => {
                    let _ = writeln!(allocas, "  %l{i} = alloca [{size} x i8], align {}", align.max(n));
                }
                Pass::Pair => {
                    let _ = writeln!(allocas, "  %l{i} = alloca [16 x i8], align {}", align.max(8));
                }
                _ => {
                    let _ = writeln!(allocas, "  %l{i} = alloca [{size} x i8], align {}", align.max(1));
                }
            }
        }
        let mut flags = String::new();
        let n_flags: usize =
            (0..self.local_cty.len()).map(|i| (self.local_drop[i] && self.dflags.keeps(i as Local)) as usize + self.move_paths[i].len()).sum();
        // Drop and move flags live in memory (an empty asm use makes them escape, as cgen's
        // frame struct does) when a fn has many of them and many landing pads: promoting
        // them puts a phi per flag on every merge of the cleanup paths, and SROA then runs
        // for minutes (`LUST_LL_FLAGMEM`, flags x pads, default 100000; 0: never).
        static FLAGMEM: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
        let flagmem = *FLAGMEM.get_or_init(|| std::env::var("LUST_LL_FLAGMEM").ok().and_then(|v| v.parse().ok()).unwrap_or(100_000));
        let escape = flagmem > 0 && n_flags * ll.pads.len() > flagmem;
        for i in 0..self.local_cty.len() {
            let param = i >= 1 && i <= self.body.arg_count;
            let mut names: Vec<String> = Vec::new();
            if self.local_drop[i] && self.dflags.keeps(i as Local) {
                let _ = writeln!(flags, "  store i8 {}, ptr %d{i}", param as u8);
                names.push(format!("%d{i}"));
            }
            for k in 0..self.move_paths[i].len() {
                let _ = writeln!(flags, "  store i8 1, ptr %m{i}_{k}");
                names.push(format!("%m{i}_{k}"));
            }
            for n in names {
                let _ = writeln!(allocas, "  {n} = alloca i8");
                if escape {
                    let _ = writeln!(flags, "  call void asm sideeffect \"\", \"r\"(ptr {n})");
                }
            }
        }
        // The exception slot: landing pads store it, ladder ends load it (a cleanup block
        // whose every entry became native code stays, unreachable, and still names it).
        if !ll.pads.is_empty() || self.cleanup.iter().any(|&c| c) {
            allocas.push_str("  %exn = alloca { ptr, i32 }\n");
        }
        allocas.push_str(&ll.allocas);
        let mut attrs = String::new();
        // A giant body (`LUST_LL_HUGE` lines of IR, default 60000; tsgo has two, a cold
        // table initializer and a registration fn) is not optimized: promoting its thousands
        // of allocas and drop flags over thousands of blocks costs the optimizer minutes per
        // run. The line count grows with each statement lowered natively instead of through a
        // helper (a helper's body is not counted, though it inlines all the same): at 40000,
        // tsgo's hot lib snapshot decoder went over and ran unoptimized.
        static HUGE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
        let huge = *HUGE.get_or_init(|| std::env::var("LUST_LL_HUGE").ok().and_then(|v| v.parse().ok()).unwrap_or(60_000));
        if huge > 0 && ll.body.lines().count() > huge {
            attrs.push_str(" optnone noinline");
        } else {
            attrs.push_str(&source_fn_attrs(p, fid));
        }
        if p.unwind {
            attrs.push_str(" uwtable");
            // The C personality, as the helpers' cleanup guards have it: every landing pad
            // here only cleans up, and LLVM inlines no fn of another personality.
            if !ll.pads.is_empty() {
                attrs.push_str(" personality ptr @__gcc_personality_v0");
            }
        } else {
            attrs.push_str(" nounwind");
        }
        let id = names::fn_tag(self.slots.of(fid));
        let mut d = String::new();
        let _ = writeln!(d, "; {}", p.display_path(info.name).replace('\n', " "));
        let _ = writeln!(d, "define {ret_ll} @fl_{id}({}){attrs} {{\nentry:", params.join(", "));
        d.push_str(&allocas);
        d.push_str(&entry);
        d.push_str(&flags);
        if let Some(k) = kstr_init {
            let _ = writeln!(d, "  call void @{k}()");
        }
        d.push_str("  br label %bb0\n");
        d.push_str(&ll.body);
        d.push_str("}\n");
        d
    }

    /// The helper side of a fn emitted as LLVM IR, into `self.out`: the prelude (vtables,
    /// shims, outlined panics), the frame macros and file statics the helpers read, and the
    /// helpers.
    fn ll_c_side(&mut self, ll: &Ll, kstr_init: Option<&str>, kdecls: &[Option<String>]) {
        let p = self.p;
        let fid = self.body.fn_id;
        let tag = &ll.tag;
        let prelude = std::mem::take(&mut self.prelude);
        let _ = writeln!(self.out, "/* {} */", p.display_path(p.fn_info(fid).name));
        self.out.push_str(&prelude);
        let mut undef: Vec<String> = Vec::new();
        let mut def = |out: &mut String, name: String, val: String| {
            let _ = writeln!(out, "#define {name} {val}");
            undef.push(name);
        };
        for i in 0..self.local_cty.len() {
            if ll.statics[i] {
                def(&mut self.out, format!("l{i}"), format!("l{i}_{tag}"));
                if self.kconst_local(i) {
                    def(&mut self.out, format!("lk{i}"), format!("lk{i}_{tag}"));
                    def(&mut self.out, format!("lkd{i}"), format!("lkd{i}_{tag}"));
                }
            } else {
                def(&mut self.out, format!("l{i}"), format!("(*q{i})"));
            }
            if self.local_drop[i] && self.dflags.keeps(i as Local) {
                def(&mut self.out, format!("d{i}"), format!("(*qd{i})"));
            }
            for k in 0..self.move_paths[i].len() {
                def(&mut self.out, format!("m{i}_{k}"), format!("(*qm{i}_{k})"));
            }
        }
        if crate::check::caller::is_track_caller(p, fid) {
            def(&mut self.out, "ltc_so".into(), "(*qltc_so)".into());
            def(&mut self.out, "ltc_low".into(), "(*qltc_low)".into());
        }
        if kstr_init.is_some() {
            if !self.kstrs.is_empty() {
                def(&mut self.out, "lks".into(), format!("lks_{tag}"));
            }
            def(&mut self.out, "lks_ok".into(), format!("lks_ok_{tag}"));
            if !self.kstrs.is_empty() {
                let _ = writeln!(self.out, "static const void *lks[{}];", self.kstrs.len());
            }
            self.out.push_str("static int32_t lks_ok;\n");
        }
        // Statics: promoted constants (zeroed, written by their statement) and byte string
        // temps (initialized here), with their interning slots.
        for i in 0..self.local_cty.len() {
            if !ll.statics[i] {
                continue;
            }
            let ct = ctype(&self.local_cty[i]);
            match (&kdecls[i], self.byte_blobs.get(i).cloned().flatten()) {
                (Some(d), _) => self.out.push_str(d),
                // An empty one has no initializer: `{0}` is too many for `v[0]`.
                (None, Some(b)) if b.is_empty() => {
                    let _ = writeln!(self.out, "static {ct} l{i};");
                }
                (None, Some(b)) => {
                    let _ = writeln!(self.out, "static {ct} l{i} = {{ .v = {} }};", c_bytes_lit(b.as_slice()));
                }
                (None, None) => {
                    let _ = writeln!(self.out, "static {ct} l{i};");
                }
            }
            if self.kconst_local(i) {
                let d = self.kconst_decls(i);
                self.out.push_str(&d);
            }
        }
        self.kstrs.clear();
        // The LLVM fn sizes each aggregate local's alloca (and a by-pointer parameter's
        // dereferenceable bytes) by `c_size_align`: the C type the helpers read must agree.
        let mut asserted: HashSet<String> = HashSet::new();
        for t in &self.local_cty {
            if matches!(pass_of(p, t), Pass::Mem | Pass::Bits(_) | Pass::Pair) {
                let ct = ctype(t);
                if asserted.insert(ct.clone()) {
                    let (size, align) = c_size_align(p, t);
                    let _ = writeln!(self.out, "_Static_assert(sizeof({ct}) == {size} && _Alignof({ct}) == {align}, \"ll layout\");");
                }
            }
        }
        for a in &ll.asserts {
            self.out.push_str(a);
        }
        self.out.push_str(&ll.helpers);
        for u in undef {
            let _ = writeln!(self.out, "#undef {u}");
        }
        self.out.push('\n');
    }

    /// The C prototype of `fl_<id>` and the C ABI wrapper `f_<id>` that forwards to it.
    fn ll_wrapper(&self, slot: u32) -> String {
        let p = self.p;
        let f = self.body.fn_id;
        let info = p.fn_info(f);
        let id = names::fn_tag(slot);
        let ret_c = cty(&p.tys, info.ret);
        let rp = pass_of(p, &ret_c);
        let large = ret_is_large(p, f);
        let rt = ctype(&ret_c);
        let mut args: Vec<String> = Vec::new();
        let mut pre = String::new();
        if rp == Pass::Mem {
            args.push(if large { "out".into() } else { "&r".into() });
        }
        for (i, &t) in info.params.iter().enumerate() {
            let ct = cty(&p.tys, t);
            match pass_of(p, &ct) {
                Pass::Skip => {}
                Pass::Scalar(..) => args.push(format!("p{}", i + 1)),
                Pass::Bits(n) => {
                    let _ = write!(pre, "{} b{}; memcpy(&b{1}, &p{1}, {n}); ", bits_types(n).1, i + 1);
                    args.push(format!("b{}", i + 1));
                }
                Pass::Pair => {
                    let _ = write!(pre, "uint64_t b{}[2]; memcpy(b{0}, &p{0}, 16); ", i + 1);
                    args.push(format!("b{0}[0], b{0}[1]", i + 1));
                }
                Pass::Mem => args.push(if param_by_ptr(p, &ct) { format!("p{}", i + 1) } else { format!("&p{}", i + 1) }),
            }
        }
        if crate::check::caller::is_track_caller(p, f) {
            args.push("ltc_so".into());
            args.push("ltc_low".into());
        }
        let call = format!("fl_{id}({})", args.join(", "));
        let body = match (rp, large) {
            (Pass::Scalar(..), _) => format!("return {call};"),
            (Pass::Bits(n), _) => format!("{} rb = {call}; {rt} r; memcpy(&r, &rb, {n}); return r;", bits_types(n).1),
            (Pass::Pair, _) => format!("ll_pair rb = {call}; {rt} r; memcpy(&r, &rb, 16); return r;"),
            (Pass::Mem, true) => format!("{call};"),
            (Pass::Skip, true) => format!("(void)out; {call};"),
            _ => format!("{rt} r; {call}; return r;"),
        };
        format!("{}{} {{ {pre}{body} }}\n", ll_proto(p, f, &id), fn_sig(p, f, slot))
    }

    /// Registers the C prototype of written fn `f`'s internal ABI entry `fl_<id>`
    /// (`ll_proto`) with the C types it names: a value it passes by value (a scalar, a fn
    /// pointer, whose typedef has no forward form) by what that holds, a value it passes by
    /// pointer by name. A fn without a C side declares its locals' types by name only
    /// (`gen_fn`), so the prototype must not rely on them.
    fn ll_note_proto(&mut self, f: LocalDefId, id: &str) {
        let p = self.p;
        self.slots.externs.borrow_mut().insert(ll_proto(p, f, id));
        let info = p.fn_info(f);
        for t in info.params.iter().chain(std::iter::once(&info.ret)).map(|&t| cty(&p.tys, t)) {
            match pass_of(p, &t) {
                Pass::Scalar(..) => {
                    let mut held = Vec::new();
                    by_value_deps(&t, &mut held);
                    self.sig_types.extend(held);
                    collect_types(&t, &mut self.sig_named);
                }
                Pass::Mem => collect_types(&t, &mut self.sig_named),
                Pass::Skip | Pass::Bits(_) | Pass::Pair => {}
            }
        }
    }

    /// A call of written fn `f` with C argument values `args` (all of its params, in
    /// order) through its internal ABI entry `fl_<id>` (an LLVM fn), from a helper's C:
    /// an aggregate argument goes as the address of a fresh copy the callee owns, an
    /// aggregate result through a fresh temporary. Pre-statements go to `self.out`;
    /// returns the value expression. `loc` is the call's location (`#[track_caller]`).
    pub(super) fn ll_fn_call(&mut self, f: LocalDefId, args: &[String], loc: &str) -> String {
        let p = self.p;
        let slot = self.slots.of(f);
        let id = names::fn_tag(slot);
        self.ll_note_proto(f, &id);
        let info = p.fn_info(f);
        let mut all: Vec<String> = Vec::new();
        let rt = cty(&p.tys, info.ret);
        let rp = pass_of(p, &rt);
        let r = self.tmp();
        if rp == Pass::Mem {
            all.push(format!("&{r}"));
        }
        for (a, &t) in args.iter().zip(&info.params) {
            let ct = cty(&p.tys, t);
            match pass_of(p, &ct) {
                Pass::Skip => {}
                Pass::Scalar(..) => all.push(a.clone()),
                Pass::Bits(n) => {
                    let (v, b) = (self.tmp(), self.tmp());
                    let _ = writeln!(self.out, "    {} {v} = {a}; {} {b}; memcpy(&{b}, &{v}, {n});", ctype(&ct), bits_types(n).1);
                    all.push(b);
                }
                Pass::Pair => {
                    let (v, b) = (self.tmp(), self.tmp());
                    let _ = writeln!(self.out, "    {} {v} = {a}; uint64_t {b}[2]; memcpy({b}, &{v}, 16);", ctype(&ct));
                    all.push(format!("{b}[0], {b}[1]"));
                }
                Pass::Mem => {
                    let v = self.tmp();
                    let _ = writeln!(self.out, "    {} {v} = {a};", ctype(&ct));
                    all.push(format!("&{v}"));
                }
            }
        }
        if crate::check::caller::is_track_caller(p, f) {
            all.push(super::names::hot_loc(loc));
        }
        let call = format!("fl_{id}({})", all.join(", "));
        match rp {
            Pass::Scalar(..) => call,
            Pass::Bits(n) => {
                let _ = writeln!(self.out, "    {} {r}b = {call}; {} {r}; memcpy(&{r}, &{r}b, {n});", bits_types(n).1, ctype(&rt));
                r
            }
            Pass::Pair => {
                let _ = writeln!(self.out, "    ll_pair {r}b = {call}; {} {r}; memcpy(&{r}, &{r}b, 16);", ctype(&rt));
                r
            }
            Pass::Mem => {
                let _ = writeln!(self.out, "    {} {r}; {call};", ctype(&rt));
                r
            }
            Pass::Skip => {
                let _ = writeln!(self.out, "    {call};");
                zero_lit(p, &rt)
            }
        }
    }
}

impl FnGen<'_, '_> {
    /// The native address plan of `pl`: a non-static local, then derefs of references and
    /// boxes to sized values, and fields of structs, tuples and enum variants whose C layout
    /// is exact (cgen's `place` reads the same members). None for any other form.
    fn ll_plan(&self, ll: &Ll, pl: &Place) -> Option<Plan> {
        let l = pl.local as usize;
        if ll.statics[l] {
            return None;
        }
        let mut t = self.local_cty[l].clone();
        let mut steps = Vec::new();
        let mut variant: Option<u32> = None;
        let mut path = String::new();
        for (k, pr) in pl.proj.iter().enumerate() {
            match (pr, t.clone()) {
                // `(*s)[i]` of a slice reference: the slice place is the fat value itself.
                (Proj::Deref, CTy::Slice(_)) if matches!(pl.proj.get(k + 1), Some(Proj::Index(_))) => {}
                (&Proj::Index(i), CTy::Vec(el) | CTy::Slice(el) | CTy::Array(el, _)) => {
                    let i = i as usize;
                    if ll.statics[i] || self.local_cty[i] != CTy::Int(IntTy::Usize) || c_layout(self.p, &el).is_none() || c_size_align(self.p, &el).0 == 0 {
                        return None;
                    }
                    let n = if let CTy::Array(_, n) = t { Some(n) } else { None };
                    let w = loc_word(&self.index_loc(i as Local, &self.loc(ll.span)))?;
                    steps.push(PStep::Index(i, n, (*el).clone(), w));
                    path.clear();
                    t = *el;
                }
                (Proj::Deref, CTy::Ref(inner) | CTy::Boxed(inner)) if *inner != CTy::Str && c_layout(self.p, &inner).is_some() => {
                    steps.push(PStep::Load((*inner).clone()));
                    path.clear();
                    t = *inner;
                }
                // Release C's offset place (cgen's `place`): the value at its offset in the block.
                (Proj::Deref, CTy::Rc(inner) | CTy::Sync(crate::ty::sync::SyncTy::Arc, inner)) => {
                    let l = c_layout(self.p, &inner).filter(|l| l.align > 0 && l.size > 0)?;
                    steps.push(PStep::LoadAt((*inner).clone(), 16u64.div_ceil(l.align) * l.align));
                    path.clear();
                    t = *inner;
                }
                // A `RefCell` guard points at its cell (`{ isize, T }`): the value is field 1.
                (Proj::Deref, CTy::Guard(inner, _)) => {
                    let cell = CTy::RefCell(inner.clone());
                    let off = *c_layout(self.p, &cell)?.field_offsets.get(1)?;
                    if c_size_align(self.p, &inner).0 == 0 {
                        return None;
                    }
                    steps.push(PStep::Load(cell));
                    steps.push(PStep::Offset(off, "f1".into()));
                    path.clear();
                    t = *inner;
                }
                (&Proj::Field(i), CTy::Adt(a)) => {
                    let lay = c_layout(self.p, &t)?;
                    let adt = self.p.adt(a);
                    let v = if adt.is_enum { variant.take()? } else { 0 };
                    let off = if adt.is_enum { *lay.variant_offsets.get(v as usize)?.get(i as usize)? } else { *lay.field_offsets.get(i as usize)? };
                    let member = if adt.is_enum { format!("u.v{v}.f{i}") } else { format!("f{i}") };
                    path = if path.is_empty() { member.clone() } else { format!("{path}.{member}") };
                    t = cty(&self.p.tys, adt.variants.get(v as usize)?.fields.get(i as usize)?.ty);
                    // A zero-sized field has no bytes to find (C may place it elsewhere).
                    if c_size_align(self.p, &t).0 == 0 {
                        return None;
                    }
                    steps.push(PStep::Offset(off, member));
                }
                (&Proj::Field(i), CTy::Tuple(es)) => {
                    let lay = c_layout(self.p, &t)?;
                    let off = *lay.field_offsets.get(i as usize)?;
                    t = es.get(i as usize)?.clone();
                    if c_size_align(self.p, &t).0 == 0 {
                        return None;
                    }
                    steps.push(PStep::Offset(off, format!("f{i}")));
                }
                (Proj::Downcast(_), CTy::Option(_)) => {}
                (Proj::Field(_), CTy::Option(inner)) => {
                    let lay = c_layout(self.p, &t)?;
                    let off = *lay.variant_offsets.get(1)?.first()?;
                    t = *inner;
                    if c_size_align(self.p, &t).0 == 0 {
                        return None;
                    }
                    steps.push(PStep::Offset(off, "u.v1.f0".into()));
                }
                (Proj::Downcast(v), CTy::Result(..) | CTy::Adt(_)) => variant = Some(*v),
                (Proj::Field(_), CTy::Result(a, b)) => {
                    let lay = c_layout(self.p, &t)?;
                    let v = variant.take().unwrap_or(0);
                    let off = *lay.variant_offsets.get(v as usize)?.first()?;
                    t = if v == 0 { *a } else { *b };
                    if c_size_align(self.p, &t).0 == 0 {
                        return None;
                    }
                    steps.push(PStep::Offset(off, format!("u.v{v}.f0")));
                }
                _ => return None,
            }
        }
        // A pending variant view with no field is not a place this file reads.
        if variant.is_some() {
            return None;
        }
        c_layout(self.p, &t)?;
        Some(Plan { local: l, steps, ty: t })
    }

    /// Emits the address of plan `pl`; returns the pointer and the alignment known there.
    /// Each offset gets its C layout check (`Ll::asserts`).
    fn ll_addr(&mut self, ll: &mut Ll, pl: &Plan) -> (String, u64) {
        let mut cur = format!("%l{}", pl.local);
        let mut ty = self.local_cty[pl.local].clone();
        let mut align = c_size_align(self.p, &ty).1.max(1);
        let mut members: Vec<String> = Vec::new();
        // The offset from the last load (or the local) to here: what the member path names.
        let mut cum = 0u64;
        for st in &pl.steps {
            match st {
                PStep::Load(inner) => {
                    ll.conts += 1;
                    let v = format!("%v{}", ll.conts);
                    let a = c_size_align(self.p, inner).1.max(1);
                    let facts = if facts_on() { format!(", !nonnull !{{}}, !noundef !{{}}, !align !{{i64 {a}}}") } else { String::new() };
                    let _ = writeln!(ll.body, "  {v} = load ptr, ptr {cur}, align {}{facts}", align.min(8));
                    cur = v;
                    ty = inner.clone();
                    align = a;
                    members.clear();
                    cum = 0;
                }
                PStep::Index(i, n, el, w) => {
                    ll.conts += 1;
                    let k = ll.conts;
                    let (ptr, len) = match n {
                        Some(n) => (cur.clone(), n.to_string()),
                        None => {
                            let a = align.min(8);
                            let _ = writeln!(ll.body, "  %xp{k} = load ptr, ptr {cur}, align {a}\n  %xq{k} = getelementptr inbounds i8, ptr {cur}, i64 8\n  %xl{k} = load i64, ptr %xq{k}, align {a}");
                            (format!("%xp{k}"), format!("%xl{k}"))
                        }
                    };
                    let _ = writeln!(
                        ll.body,
                        "  %xi{k} = load i64, ptr %l{i}\n  %xc{k} = icmp uge i64 %xi{k}, {len}\n  br i1 %xc{k}, label %xf{k}, label %xo{k}, !prof !{{!\"branch_weights\", i32 1, i32 2000}}\nxf{k}:"
                    );
                    let lv = ll_loc_value(ll, w, k);
                    ll.decls.insert("declare i64 @lust_bounds(i64, i64, i64)".into());
                    match ll.unwind {
                        Some(u) => {
                            ll.pads.insert(u);
                            let _ = writeln!(ll.body, "  %xr{k} = invoke i64 @lust_bounds(i64 %xi{k}, i64 {len}, i64 {lv}) to label %xu{k} unwind label %lp{u}\nxu{k}:\n  unreachable");
                        }
                        None => {
                            let _ = writeln!(ll.body, "  %xr{k} = call i64 @lust_bounds(i64 %xi{k}, i64 {len}, i64 {lv})\n  unreachable");
                        }
                    }
                    let stride = c_size_align(self.p, el).0;
                    // An element GEP, as clang writes `&base[i]`: its offset cannot wrap, which
                    // loop analysis needs (a plain multiply hides that).
                    let _ = writeln!(ll.body, "xo{k}:\n  %xe{k} = getelementptr inbounds [{stride} x i8], ptr {ptr}, i64 %xi{k}");
                    cur = format!("%xe{k}");
                    ty = el.clone();
                    align = c_size_align(self.p, el).1.max(1);
                    members.clear();
                    cum = 0;
                }
                PStep::LoadAt(inner, off) => {
                    ll.conts += 1;
                    let v = format!("%v{}", ll.conts);
                    let facts = if facts_on() { ", !nonnull !{}, !noundef !{}, !align !{i64 8}" } else { "" };
                    let _ = writeln!(ll.body, "  {v} = load ptr, ptr {cur}, align {}{facts}\n  {v}o = getelementptr inbounds i8, ptr {v}, i64 {off}", align.min(8));
                    cur = format!("{v}o");
                    ty = inner.clone();
                    align = c_size_align(self.p, inner).1.max(1);
                    members.clear();
                    cum = 0;
                }
                PStep::Offset(off, member) => {
                    members.push(member.clone());
                    cum += off;
                    // The helper C must define what native code projects into (release C
                    // defines only what a unit holds by value, `gen_fn`).
                    ll.assert_types.push(ty.clone());
                    let _ = ll.asserts.insert(format!(
                        "_Static_assert(__builtin_offsetof({}, {}) == {cum}, \"ll offset\");\n",
                        ctype(&ty),
                        members.join(".")
                    ));
                    if *off != 0 {
                        ll.conts += 1;
                        let v = format!("%v{}", ll.conts);
                        let _ = writeln!(ll.body, "  {v} = getelementptr inbounds i8, ptr {cur}, i64 {off}");
                        cur = v;
                        align = align.min(1 << off.trailing_zeros());
                    }
                }
            }
        }
        (cur, align)
    }

    /// The load facts of a scalar of C type `t` read from memory: a reference or box is
    /// non-null and aligned, a bool 0 or 1, a char below 0x110000.
    fn ll_load_facts(&self, t: &CTy) -> String {
        if !facts_on() {
            return String::new();
        }
        match t {
            CTy::Bool => ", !range !{i8 0, i8 2}, !noundef !{}".into(),
            CTy::Char => ", !range !{i32 0, i32 1114112}, !noundef !{}".into(),
            CTy::Ref(inner) | CTy::Boxed(inner) if **inner != CTy::Str => match c_layout(self.p, inner) {
                Some(l) => format!(", !nonnull !{{}}, !noundef !{{}}, !align !{{i64 {}}}", l.align.max(1)),
                None => String::new(),
            },
            _ => String::new(),
        }
    }

    /// The C type of operand `o` when native code can read it as one scalar (a native
    /// place's value or a literal), with the flag a move of it clears. None otherwise.
    fn ll_scalar_ok(&self, ll: &Ll, o: &Operand) -> Option<(CTy, Option<String>)> {
        match o {
            Operand::Copy(pl) | Operand::Move(pl) => {
                let plan = self.ll_plan(ll, pl)?;
                if !matches!(pass_of(self.p, &plan.ty), Pass::Scalar(..)) {
                    return None;
                }
                let mut clear = None;
                if matches!(o, Operand::Move(_)) && self.local_drop[pl.local as usize] {
                    clear = if pl.proj.is_empty() {
                        self.dflags.keeps(pl.local).then(|| format!("%d{}", pl.local))
                    } else {
                        Some(format!("%m{}_{}", pl.local, self.move_flag(pl.local, &self.steps_of(pl)?)?))
                    };
                }
                Some((plan.ty, clear))
            }
            Operand::Const(Const::Int(_, it)) if !is128(*it) => Some((CTy::Int(*it), None)),
            Operand::Const(Const::Bool(_)) => Some((CTy::Bool, None)),
            Operand::Const(Const::Char(_)) => Some((CTy::Char, None)),
            Operand::Const(Const::Float(_, f)) => Some((CTy::Float(*f), None)),
            _ => None,
        }
    }

    /// Emits the value of an operand `ll_scalar_ok` accepted (and its move's flag clear).
    fn ll_scalar(&mut self, ll: &mut Ll, o: &Operand) -> String {
        match o {
            Operand::Copy(pl) | Operand::Move(pl) => {
                let plan = self.ll_plan(ll, pl).expect("checked by ll_scalar_ok");
                let Pass::Scalar(t, _) = pass_of(self.p, &plan.ty) else { unreachable!() };
                let (a, align) = self.ll_addr(ll, &plan);
                ll.conts += 1;
                let v = format!("%v{}", ll.conts);
                let facts = self.ll_load_facts(&plan.ty);
                let _ = writeln!(ll.body, "  {v} = load {t}, ptr {a}, align {align}{facts}");
                if let Some((_, Some(flag))) = self.ll_scalar_ok(ll, o) {
                    let _ = writeln!(ll.body, "  store i8 0, ptr {flag}");
                }
                v
            }
            Operand::Const(Const::Int(v, it)) => {
                let bits = it.bits();
                let m = if bits >= 128 { *v } else { *v & ((1u128 << bits) - 1) };
                // Printed as a signed value of the width (LLVM reads any bit pattern of it).
                let sv = if bits < 128 && (m >> (bits - 1)) & 1 == 1 { (m as i128) - (1i128 << bits) } else { m as i128 };
                sv.to_string()
            }
            Operand::Const(Const::Bool(b)) => (*b as u8).to_string(),
            Operand::Const(Const::Char(c)) => (*c as u32).to_string(),
            Operand::Const(Const::Float(bits, f)) => match f {
                FloatTy::F64 => format!("0x{bits:016X}"),
                // LLVM writes a float constant as the double of the same value.
                FloatTy::F32 => format!("0x{:016X}", (f32::from_bits(*bits as u32) as f64).to_bits()),
            },
            _ => unreachable!("checked by ll_scalar_ok"),
        }
    }

    /// The native value of a scalar rvalue (release arithmetic, comparisons, int casts,
    /// discriminants), stored to `dp`; false (nothing emitted) for any other form.
    fn ll_native_value(&mut self, ll: &mut Ll, rv: &Rvalue, dp: &Plan) -> bool {
        let Pass::Scalar(dt, _) = pass_of(self.p, &dp.ty) else { return false };
        let int_signed = |t: &CTy| matches!(t, CTy::Int(i) if i.signed());
        let value = match rv {
            Rvalue::Bin(op, a, b) => {
                let (Some((at, _)), Some((bt, _))) = (self.ll_scalar_ok(ll, a), self.ll_scalar_ok(ll, b)) else { return false };
                use BinOp::*;
                let float = matches!(at, CTy::Float(_));
                let ok_operands = matches!(at, CTy::Int(i) if !is128(i)) || at == CTy::Bool || at == CTy::Char || float;
                if !ok_operands || (at != bt && !matches!(op, Shl | Shr)) {
                    return false;
                }
                if op.is_cmp() {
                    if dp.ty != CTy::Bool {
                        return false;
                    }
                } else if dp.ty != at {
                    return false;
                }
                let t = match pass_of(self.p, &at) {
                    Pass::Scalar(t, _) => t,
                    _ => return false,
                };
                let inst = match (op, float) {
                    (Add, false) if !self.p.overflow_checks && at != CTy::Bool => "add",
                    (Sub, false) if !self.p.overflow_checks && at != CTy::Bool => "sub",
                    (Mul, false) if !self.p.overflow_checks && at != CTy::Bool => "mul",
                    (Add, true) => "fadd",
                    (Sub, true) => "fsub",
                    (Mul, true) => "fmul",
                    (Div, true) => "fdiv",
                    (BitAnd, false) => "and",
                    (BitOr, false) => "or",
                    (BitXor, false) => "xor",
                    (Shl | Shr, false) if !self.p.overflow_checks && matches!(at, CTy::Int(_)) && matches!(bt, CTy::Int(i) if !is128(i)) => "shift",
                    (Eq | Ne | Lt | Le | Gt | Ge, _) => "cmp",
                    _ => return false,
                };
                let av = self.ll_scalar(ll, a);
                let bv = self.ll_scalar(ll, b);
                ll.conts += 1;
                let k = ll.conts;
                match inst {
                    "cmp" => {
                        let pred = if float {
                            match op {
                                Eq => "fcmp oeq",
                                Ne => "fcmp une",
                                Lt => "fcmp olt",
                                Le => "fcmp ole",
                                Gt => "fcmp ogt",
                                _ => "fcmp oge",
                            }
                        } else {
                            let s = int_signed(&at);
                            match (op, s) {
                                (Eq, _) => "icmp eq",
                                (Ne, _) => "icmp ne",
                                (Lt, true) => "icmp slt",
                                (Lt, false) => "icmp ult",
                                (Le, true) => "icmp sle",
                                (Le, false) => "icmp ule",
                                (Gt, true) => "icmp sgt",
                                (Gt, false) => "icmp ugt",
                                (Ge, true) => "icmp sge",
                                _ => "icmp uge",
                            }
                        };
                        let _ = writeln!(ll.body, "  %c{k} = {pred} {t} {av}, {bv}\n  %v{k} = zext i1 %c{k} to i8");
                    }
                    "shift" => {
                        // The amount masked to the width (overflow checks off), as cgen's C.
                        let CTy::Int(ai) = at else { unreachable!() };
                        let CTy::Int(bi) = bt else { unreachable!() };
                        let bty = match pass_of(self.p, &bt) {
                            Pass::Scalar(x, _) => x,
                            _ => return false,
                        };
                        let wide = if bty == "i64" {
                            bv
                        } else {
                            let ext = if bi.signed() { "sext" } else { "zext" };
                            let _ = writeln!(ll.body, "  %w{k} = {ext} {bty} {bv} to i64");
                            format!("%w{k}")
                        };
                        let _ = writeln!(ll.body, "  %m{k} = and i64 {wide}, {}", ai.bits() - 1);
                        let amt = if t == "i64" {
                            format!("%m{k}")
                        } else {
                            let _ = writeln!(ll.body, "  %n{k} = trunc i64 %m{k} to {t}");
                            format!("%n{k}")
                        };
                        let sh = match (op, ai.signed()) {
                            (Shl, _) => "shl",
                            (_, true) => "ashr",
                            _ => "lshr",
                        };
                        let _ = writeln!(ll.body, "  %v{k} = {sh} {t} {av}, {amt}");
                    }
                    i => {
                        let _ = writeln!(ll.body, "  %v{k} = {i} {t} {av}, {bv}");
                    }
                }
                format!("%v{k}")
            }
            Rvalue::Un(op, a) => {
                let Some((at, _)) = self.ll_scalar_ok(ll, a) else { return false };
                if at != dp.ty {
                    return false;
                }
                let inst = match (op, &at) {
                    (UnOp::Neg, CTy::Float(_)) => "fneg",
                    (UnOp::Neg, CTy::Int(i)) if !self.p.overflow_checks && !is128(*i) => "neg",
                    (UnOp::Not, CTy::Bool) => "notb",
                    (UnOp::Not, CTy::Int(i)) if !is128(*i) => "not",
                    _ => return false,
                };
                let av = self.ll_scalar(ll, a);
                ll.conts += 1;
                let k = ll.conts;
                let _ = match inst {
                    "fneg" => writeln!(ll.body, "  %v{k} = fneg {dt} {av}"),
                    "neg" => writeln!(ll.body, "  %v{k} = sub {dt} 0, {av}"),
                    "notb" => writeln!(ll.body, "  %v{k} = xor i8 {av}, 1"),
                    _ => writeln!(ll.body, "  %v{k} = xor {dt} {av}, -1"),
                };
                format!("%v{k}")
            }
            Rvalue::Cast(a, to) => {
                let Some((at, _)) = self.ll_scalar_ok(ll, a) else { return false };
                let to_c = cty(&self.body.tys, *to);
                if to_c != dp.ty {
                    return false;
                }
                let int_like = |t: &CTy| matches!(t, CTy::Int(i) if !is128(*i)) || matches!(t, CTy::Bool | CTy::Char);
                // Int to int (a bool or char source is unsigned); only `u8 as char` makes a char.
                if !int_like(&at) || !matches!(to_c, CTy::Int(i) if !is128(i)) && !(to_c == CTy::Char && at == CTy::Int(IntTy::U8)) {
                    return false;
                }
                let (Pass::Scalar(ft, _), Pass::Scalar(tt, _)) = (pass_of(self.p, &at), pass_of(self.p, &to_c)) else { return false };
                let av = self.ll_scalar(ll, a);
                let width = |t: &str| t[1..].parse::<u32>().unwrap_or(64);
                let (fw, tw) = (width(ft), width(tt));
                if fw == tw {
                    av
                } else {
                    ll.conts += 1;
                    let k = ll.conts;
                    let inst = if tw < fw {
                        "trunc"
                    } else if int_signed(&at) {
                        "sext"
                    } else {
                        "zext"
                    };
                    let _ = writeln!(ll.body, "  %v{k} = {inst} {ft} {av} to {tt}");
                    format!("%v{k}")
                }
            }
            Rvalue::Discriminant(pl) => {
                let Some(plan) = self.ll_plan(ll, pl) else { return false };
                if !matches!(dp.ty, CTy::Int(i) if !is128(i)) || !self.ll_disc_ok(&plan.ty) {
                    return false;
                }
                self.ll_disc(ll, &plan, dt)
            }
            _ => return false,
        };
        let (da, dalign) = self.ll_addr(ll, dp);
        let _ = writeln!(ll.body, "  store {dt} {value}, ptr {da}, align {dalign}");
        true
    }

    /// True when `ll_disc` reads the variant index of a value of C type `t`: a tag or a niche
    /// scalar of up to 8 bytes, or no tag.
    fn ll_disc_ok(&self, t: &CTy) -> bool {
        let Some(lay) = c_layout(self.p, t) else { return false };
        let discs = adt_discs(self.p, t);
        match lay.enum_tag {
            Some(EnumTag::None(_)) => true,
            Some(EnumTag::NicheFilled { niche, .. }) => niche.scalar_size <= 8,
            Some(EnumTag::Explicit { size, .. }) => size <= 8 && !discs.is_empty(),
            None => false,
        }
    }

    /// Emits the variant index of the enum value at `plan` as an LLVM integer of type `dt`
    /// (`disc_call`): a sequential tag holds the index; the other tags as cgen's `disc_` glue
    /// maps them: a niche value within the span is variant `first` plus its wrapping
    /// distance from `start`, any other value the dataful variant; a non-sequential tag
    /// value is the index of the variant with that discriminant (0 for none). The caller
    /// checked `ll_disc_ok`.
    fn ll_disc(&mut self, ll: &mut Ll, plan: &Plan, dt: &str) -> String {
        let lay = c_layout(self.p, &plan.ty).expect("checked by ll_disc_ok");
        let n = adt_discs(self.p, &plan.ty).len();
        match lay.enum_tag {
            Some(EnumTag::None(vi)) => vi.to_string(),
            Some(EnumTag::NicheFilled { variant, niche, first, last, start }) => {
                let n = niche.scalar_size;
                let tt = bits_types(n).0;
                let (a, align) = self.ll_addr(ll, plan);
                ll.conts += 1;
                let k = ll.conts;
                let off = niche.offset;
                let (ptr, al) = if off == 0 {
                    (a, align)
                } else {
                    let _ = writeln!(ll.body, "  %nq{k} = getelementptr inbounds i8, ptr {a}, i64 {off}");
                    (format!("%nq{k}"), align.min(1 << off.trailing_zeros()))
                };
                let span = (last - first + 1) as u128;
                let db = dt[1..].parse::<u64>().unwrap_or(64) / 8;
                let _ = writeln!(
                    ll.body,
                    "  %nt{k} = load {tt}, ptr {ptr}, align {}\n  %nd{k} = sub {tt} %nt{k}, {}\n  %nc{k} = icmp ult {tt} %nd{k}, {}",
                    al.min(n),
                    ll_int_lit(start, n),
                    ll_int_lit(span, n)
                );
                let dist = match (n * 8).cmp(&(db * 8)) {
                    std::cmp::Ordering::Equal => format!("%nd{k}"),
                    o => {
                        let inst = if o == std::cmp::Ordering::Greater { "trunc" } else { "zext" };
                        let _ = writeln!(ll.body, "  %nz{k} = {inst} {tt} %nd{k} to {dt}");
                        format!("%nz{k}")
                    }
                };
                let _ = writeln!(
                    ll.body,
                    "  %na{k} = add {dt} {dist}, {}\n  %v{k} = select i1 %nc{k}, {dt} %na{k}, {dt} {}",
                    ll_int_lit(first as u128, db),
                    ll_int_lit(variant as u128, db)
                );
                format!("%v{k}")
            }
            // As cgen's `disc_` glue: a switch over the tag values (LLVM makes it a table, or
            // folds it into the switch that reads the result).
            Some(EnumTag::Explicit { size, .. }) if !discs_sequential(&adt_discs(self.p, &plan.ty)) => {
                let tt = bits_types(size).0;
                let db = dt[1..].parse::<u64>().unwrap_or(64) / 8;
                let (a, align) = self.ll_addr(ll, plan);
                ll.conts += 1;
                let k = ll.conts;
                let discs = adt_discs(self.p, &plan.ty);
                let _ = write!(ll.body, "  %nt{k} = load {tt}, ptr {a}, align {}\n  switch {tt} %nt{k}, label %nd{k} [", align.min(size));
                for (vi, &d) in discs.iter().enumerate().skip(1) {
                    let _ = write!(ll.body, " {tt} {}, label %nc{k}_{vi}", ll_int_lit((d as u128) & scalar_mask(size), size));
                }
                ll.body.push_str(" ]\n");
                let mut phi = format!("[ 0, %nd{k} ]");
                let _ = writeln!(ll.body, "nd{k}:\n  br label %nw{k}");
                for vi in 1..discs.len() {
                    let _ = writeln!(ll.body, "nc{k}_{vi}:\n  br label %nw{k}");
                    let _ = write!(phi, ", [ {}, %nc{k}_{vi} ]", ll_int_lit(vi as u128, db));
                }
                let _ = writeln!(ll.body, "nw{k}:\n  %nv{k} = phi {dt} {phi}");
                format!("%nv{k}")
            }
            Some(EnumTag::Explicit { size, .. }) => {
                let tt = bits_types(size).0;
                let (a, align) = self.ll_addr(ll, plan);
                ll.conts += 1;
                let k = ll.conts;
                let range = if facts_on() { format!(", !range !{{{tt} 0, {tt} {n}}}, !noundef !{{}}") } else { String::new() };
                let _ = writeln!(ll.body, "  %t{k} = load {tt}, ptr {a}, align {}{range}", align.min(size));
                let (tw, dw) = (size * 8, dt[1..].parse::<u64>().unwrap_or(64));
                if tw == dw {
                    format!("%t{k}")
                } else {
                    let inst = if dw < tw { "trunc" } else { "zext" };
                    let _ = writeln!(ll.body, "  %v{k} = {inst} {tt} %t{k} to {dt}");
                    format!("%v{k}")
                }
            }
            _ => unreachable!("checked by ll_disc_ok"),
        }
    }

    /// A call of written fn `f` (args `args`, result to `dest`) lowered natively: arguments
    /// by the callee's internal ABI from native places or literals (an aggregate through a
    /// fresh copy the callee owns), moved arguments' flags cleared first (the callee owns
    /// them from the start, as cgen's `emit_assign`), an `invoke` when `unwind` names a
    /// cleanup entry, then the result stored to `dest`, dropping the value a whole local
    /// held. False (nothing emitted) for any other shape.
    /// `dest_clear`: the destination local's drop flag is surely clear here, so it holds no
    /// old value (a result can go straight into it). `span`: the call's, for a
    /// `#[track_caller]` callee's location argument.
    fn ll_native_call(&mut self, ll: &mut Ll, f: LocalDefId, args: &[Operand], dest: &Place, dest_clear: bool, span: Span, unwind: Option<u32>) -> bool {
        let p = self.p;
        if !has_generated_body(p, f) {
            return false;
        }
        // A `#[track_caller]` callee takes this call's location last, as the address of its
        // slot constant and its line and column bits (`fl_` has a ptr and an i64 parameter
        // for them, as the C wrapper has; `names::hot_loc`).
        let loc = if crate::check::caller::is_track_caller(p, f) {
            match loc_word(&self.loc(span)) {
                Some(w) => Some(w),
                None => return false,
            }
        } else {
            None
        };
        let info = p.fn_info(f);
        if args.len() != info.params.len() {
            return false;
        }
        let rt = cty(&p.tys, info.ret);
        if dest.proj.iter().any(|p| matches!(p, Proj::Index(_))) {
            return false;
        }
        let Some(dp) = self.ll_plan(ll, dest) else { return false };
        if dp.ty != rt {
            return false;
        }
        let dl = dest.local as usize;
        let drop_old = needs_drop_c(p, &dp.ty);
        // A destination with move paths drops an old value by elaboration (`ll_elab`).
        let elab = drop_old && !self.move_paths[dl].is_empty();
        if drop_old && (!dest.proj.is_empty() || !self.local_drop[dl] || (elab && !dest_clear && (!self.dflags.keeps(dest.local) || !self.ll_elab_ok(ll, dl, &[])))) {
            return false;
        }
        // Check every argument before emitting anything.
        let pts: Vec<CTy> = info.params.iter().map(|&t| cty(&p.tys, t)).collect();
        let mut clears: Vec<String> = Vec::new();
        for (a, pt) in args.iter().zip(&pts) {
            match pass_of(p, pt) {
                Pass::Scalar(..) => match self.ll_scalar_ok(ll, a) {
                    Some((t, _)) if t == *pt => {}
                    _ => return false,
                },
                Pass::Skip | Pass::Bits(_) | Pass::Pair | Pass::Mem => {
                    let (Operand::Copy(pl) | Operand::Move(pl)) = a else { return false };
                    match self.ll_plan(ll, pl) {
                        Some(plan) if plan.ty == *pt => {}
                        _ => return false,
                    }
                }
            }
            if let Operand::Move(pl) = a
                && self.local_drop[pl.local as usize]
            {
                if pl.proj.is_empty() {
                    if self.dflags.keeps(pl.local) {
                        clears.push(format!("%d{}", pl.local));
                    }
                } else {
                    match self.steps_of(pl).and_then(|path| self.move_flag(pl.local, &path)) {
                        Some(k) => clears.push(format!("%m{}_{k}", pl.local)),
                        None => return false,
                    }
                }
            }
        }
        self.note_callee(f);
        let id = names::fn_tag(self.slots.of(f));
        self.ll_note_proto(f, &id);
        ll.decls.insert(ll_decl(p, f, &id));
        ll.conts += 1;
        let k = ll.conts;
        let mut vals: Vec<String> = Vec::new();
        // The call's temporaries live only around it (lifetime markers: their stack slots
        // can share space, as the C helpers' block locals do).
        let mut temps: Vec<(String, u64)> = Vec::new();
        ll.decls.insert("declare void @llvm.lifetime.start.p0(i64, ptr)".into());
        ll.decls.insert("declare void @llvm.lifetime.end.p0(i64, ptr)".into());
        let rp = pass_of(p, &rt);
        // A moved whole local passed by pointer goes as itself: the caller never reads it
        // again (its flag is clear), so the callee may own that memory, as rustc does.
        let direct: Vec<bool> = args
            .iter()
            .zip(&pts)
            .map(|(a, pt)| matches!(a, Operand::Move(pl) if pl.proj.is_empty() && !ll.statics[pl.local as usize] && pass_of(p, pt) == Pass::Mem))
            .collect();
        let direct_locals: Vec<usize> =
            args.iter().zip(&direct).filter(|(_, d)| **d).filter_map(|(a, _)| if let Operand::Move(pl) = a { Some(pl.local as usize) } else { None }).collect();
        // An old value the call result replaces (dropped after the call returns), unless the
        // destination's flag is surely clear here.
        // A static flag (`ir::dropflags`) says whether the old value is there on every path.
        let static_old = if drop_old && !self.dflags.keeps(dest.local) { self.dflags.test(self.at, dest.local) } else { None };
        let old_live = drop_old && !dest_clear && static_old != Some(false);
        if drop_old && !dest_clear && !old_live {
            // No old value on any path: its glue stays wanted all the same, as other C names it.
            self.want(Glue::Drop, &dp.ty);
        }
        // The result goes straight to a whole-local destination that holds nothing to drop
        // (a panic before the end leaves nothing that reads it: its flag is clear), unless
        // that local is an argument passed as itself.
        let ret_direct = rp == Pass::Mem && dest.proj.is_empty() && !old_live && !ll.statics[dl] && !direct_locals.contains(&dl);
        if rp == Pass::Mem {
            if ret_direct {
                vals.push(format!("ptr %l{dl}"));
            } else {
                let (size, align) = c_size_align(p, &rt);
                let _ = writeln!(ll.allocas, "  %r{k} = alloca [{size} x i8], align {align}");
                let _ = writeln!(ll.body, "  call void @llvm.lifetime.start.p0(i64 {size}, ptr %r{k})");
                vals.push(format!("ptr %r{k}"));
            }
        }
        for (j, (a, pt)) in args.iter().zip(&pts).enumerate() {
            match pass_of(p, pt) {
                Pass::Skip => {}
                Pass::Scalar(t, ext) => {
                    let v = self.ll_scalar_operand_value(ll, a);
                    let ext = if ext.is_empty() { String::new() } else { format!("{ext} ") };
                    vals.push(format!("{t} {ext}{v}"));
                }
                Pass::Bits(n) => {
                    let (Operand::Copy(pl) | Operand::Move(pl)) = a else { unreachable!() };
                    let plan = self.ll_plan(ll, pl).expect("checked");
                    let (addr, align) = self.ll_addr(ll, &plan);
                    let t = bits_types(n).0;
                    let _ = writeln!(ll.body, "  %a{k}_{j} = load {t}, ptr {addr}, align {}", align.min(n));
                    vals.push(format!("{t} %a{k}_{j}"));
                }
                Pass::Pair => {
                    let (Operand::Copy(pl) | Operand::Move(pl)) = a else { unreachable!() };
                    let plan = self.ll_plan(ll, pl).expect("checked");
                    let (addr, align) = self.ll_addr(ll, &plan);
                    let al = align.min(8);
                    let _ = writeln!(
                        ll.body,
                        "  %a{k}_{j} = load i64, ptr {addr}, align {al}\n  %a{k}_{j}q = getelementptr inbounds i8, ptr {addr}, i64 8\n  %a{k}_{j}b = load i64, ptr %a{k}_{j}q, align {al}"
                    );
                    vals.push(format!("i64 %a{k}_{j}, i64 %a{k}_{j}b"));
                }
                Pass::Mem if direct[j] => {
                    let (Operand::Copy(pl) | Operand::Move(pl)) = a else { unreachable!() };
                    vals.push(format!("ptr %l{}", pl.local));
                }
                Pass::Mem => {
                    let (Operand::Copy(pl) | Operand::Move(pl)) = a else { unreachable!() };
                    let plan = self.ll_plan(ll, pl).expect("checked");
                    let (addr, align) = self.ll_addr(ll, &plan);
                    let (size, palign) = c_size_align(p, pt);
                    let _ = writeln!(ll.allocas, "  %a{k}_{j} = alloca [{size} x i8], align {palign}");
                    ll.decls.insert("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)".into());
                    let _ = writeln!(
                        ll.body,
                        "  call void @llvm.lifetime.start.p0(i64 {size}, ptr %a{k}_{j})\n  call void @llvm.memcpy.p0.p0.i64(ptr align {palign} %a{k}_{j}, ptr align {align} {addr}, i64 {size}, i1 false)"
                    );
                    temps.push((format!("%a{k}_{j}"), size));
                    vals.push(format!("ptr %a{k}_{j}"));
                }
            }
        }
        if let Some(w) = loc {
            vals.push(ll_loc_args(ll, &w, k));
        }
        for flag in &clears {
            let _ = writeln!(ll.body, "  store i8 0, ptr {flag}");
        }
        let ret_ty = match rp {
            Pass::Scalar(t, ext) => {
                if ext.is_empty() {
                    t.to_string()
                } else {
                    format!("{ext} {t}")
                }
            }
            Pass::Bits(n) => bits_types(n).0.to_string(),
            Pass::Pair => "{ i64, i64 }".into(),
            _ => "void".into(),
        };
        let assign = if ret_ty == "void" { String::new() } else { format!("%v{k} = ") };
        let call = format!("{ret_ty} @fl_{id}({})", vals.join(", "));
        match unwind {
            Some(u) => {
                ll.pads.insert(u);
                let _ = writeln!(ll.body, "  {assign}invoke {call} to label %c{k} unwind label %lp{u}\nc{k}:");
            }
            None => {
                let _ = writeln!(ll.body, "  {assign}call {call}");
            }
        }
        for (t, size) in &temps {
            let _ = writeln!(ll.body, "  call void @llvm.lifetime.end.p0(i64 {size}, ptr {t})");
        }
        // The old value of a whole local drops once the call returned (`drop_old_value`).
        if old_live {
            if static_old.is_some() {
                let _ = writeln!(ll.body, "  br label %od{k}\nod{k}:");
            } else {
                let _ = writeln!(
                    ll.body,
                    "  %o{k} = load i8, ptr %d{dl}\n  %oc{k} = icmp ne i8 %o{k}, 0\n  br i1 %oc{k}, label %od{k}, label %on{k}\nod{k}:\n  store i8 0, ptr %d{dl}"
                );
            }
            if elab {
                self.ll_elab(ll, dl, &[], unwind);
                let _ = writeln!(ll.body, "  br label %on{k}");
            } else {
                let glue = format!("drop_{}", mangle(&dp.ty));
                self.want(Glue::Drop, &dp.ty);
                ll.decls.insert(format!("declare void @{glue}(ptr)"));
                match unwind {
                    Some(u) => {
                        let _ = writeln!(ll.body, "  invoke void @{glue}(ptr %l{dl}) to label %on{k} unwind label %lp{u}");
                    }
                    None => {
                        let _ = writeln!(ll.body, "  call void @{glue}(ptr %l{dl})\n  br label %on{k}");
                    }
                }
            }
            let _ = writeln!(ll.body, "on{k}:");
        }
        let (da, dalign) = self.ll_addr(ll, &dp);
        match rp {
            Pass::Scalar(t, _) => {
                let _ = writeln!(ll.body, "  store {t} %v{k}, ptr {da}, align {dalign}");
            }
            Pass::Bits(n) => {
                let _ = writeln!(ll.body, "  store {} %v{k}, ptr {da}, align {}", bits_types(n).0, dalign.min(n));
            }
            Pass::Pair => {
                let al = dalign.min(8);
                let _ = writeln!(
                    ll.body,
                    "  %v{k}a = extractvalue {{ i64, i64 }} %v{k}, 0\n  %v{k}b = extractvalue {{ i64, i64 }} %v{k}, 1\n  store i64 %v{k}a, ptr {da}, align {al}\n  %v{k}q = getelementptr inbounds i8, ptr {da}, i64 8\n  store i64 %v{k}b, ptr %v{k}q, align {al}"
                );
            }
            Pass::Mem if ret_direct => {}
            Pass::Mem => {
                let (size, align) = c_size_align(p, &rt);
                ll.decls.insert("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)".into());
                let _ = writeln!(
                    ll.body,
                    "  call void @llvm.memcpy.p0.p0.i64(ptr align {dalign} {da}, ptr align {align} %r{k}, i64 {size}, i1 false)\n  call void @llvm.lifetime.end.p0(i64 {size}, ptr %r{k})"
                );
            }
            Pass::Skip => {}
        }
        if drop_old && static_old.is_none() {
            let _ = writeln!(ll.body, "  store i8 1, ptr %d{dl}");
        }
        // The whole value is there again (`drop_old_value`'s `reset_move_flags`).
        if drop_old {
            for k in 0..self.move_paths[dl].len() {
                let _ = writeln!(ll.body, "  store i8 1, ptr %m{dl}_{k}");
            }
        }
        true
    }

    /// For each block, the locals whose drop flag may be set at its terminator: a write to a
    /// local (an assign to it or a part, a call result) may set its flag; a move of the whole
    /// local or its drop clears it. A move this does not model counts as still set, so a
    /// clear answer is exact.
    pub(super) fn flags_maybe_set(&self) -> Vec<Vec<bool>> {
        let body = self.body;
        let (nl, nb) = (body.locals.len(), body.blocks.len());
        let mut entry: Vec<Option<Vec<bool>>> = vec![None; nb];
        let mut at_term = vec![vec![true; nl]; nb];
        // Parameters own their values at entry.
        entry[0] = Some((0..nl).map(|l| l >= 1 && l <= body.arg_count).collect());
        let mut work = vec![0usize];
        fn join(entry: &mut [Option<Vec<bool>>], work: &mut Vec<usize>, b: Bb, st: &[bool]) {
            let b = b.0 as usize;
            match &mut entry[b] {
                Some(e) => {
                    let mut grew = false;
                    for (x, &y) in e.iter_mut().zip(st) {
                        grew |= y && !*x;
                        *x |= y;
                    }
                    if grew {
                        work.push(b);
                    }
                }
                None => {
                    entry[b] = Some(st.to_vec());
                    work.push(b);
                }
            }
        }
        while let Some(b) = work.pop() {
            let mut st = entry[b].clone().expect("queued blocks have a state");
            for s in &body.blocks[b].stmts {
                match &s.kind {
                    StmtKind::Assign(pl, rv) => {
                        if let Rvalue::Use(Operand::Move(src)) = rv
                            && src.proj.is_empty()
                        {
                            st[src.local as usize] = false;
                        }
                        st[pl.local as usize] = true;
                    }
                    StmtKind::Drop(l) => st[*l as usize] = false,
                    _ => {}
                }
            }
            at_term[b] = st.clone();
            match &body.blocks[b].term {
                Terminator::Call { args, dest, next, unwind, .. } => {
                    // A call owns its moved arguments from the start.
                    for a in args {
                        if let Operand::Move(p) = a
                            && p.proj.is_empty()
                        {
                            st[p.local as usize] = false;
                        }
                    }
                    if let Some(u) = unwind {
                        join(&mut entry, &mut work, *u, &st);
                    }
                    st[dest.local as usize] = true;
                    join(&mut entry, &mut work, *next, &st);
                }
                Terminator::Goto(t) => join(&mut entry, &mut work, *t, &st),
                Terminator::If(_, a, c) => {
                    join(&mut entry, &mut work, *a, &st);
                    join(&mut entry, &mut work, *c, &st);
                }
                Terminator::Switch(_, cases, other) => {
                    for (_, t) in cases {
                        join(&mut entry, &mut work, *t, &st);
                    }
                    join(&mut entry, &mut work, *other, &st);
                }
                Terminator::Return | Terminator::Unreachable | Terminator::MatchExhausted | Terminator::Panic(_) => {}
            }
        }
        at_term
    }

    /// The shape of rvalue `rv` stored into a place of C type `dt`: a copy or move of a value
    /// of that type, or an aggregate (struct, enum variant, tuple, array, `Some`/`None`,
    /// `Ok`/`Err`) as cgen's compound literals build it (`variant_lit`). None for any other
    /// rvalue, or a tag wider than 8 bytes.
    fn ll_shape<'o>(&self, rv: &'o Rvalue, dt: &CTy) -> Option<Shape<'o>> {
        let p = self.p;
        let lay = c_layout(p, dt)?;
        // The parts and the enum variant built (None: not an enum).
        let (parts, variant): (Vec<Part<'o>>, Option<usize>) = match rv {
            Rvalue::Use(o @ (Operand::Copy(_) | Operand::Move(_))) => (vec![Part { op: o, off: 0, ty: dt.clone() }], None),
            Rvalue::Aggregate(a, v, ops) => {
                let a = p.tys.c_adt(*a);
                if *dt != CTy::Adt(a) {
                    return None;
                }
                let adt = p.adt(a);
                let vi = if adt.is_enum { *v as usize } else { 0 };
                let fields = &adt.variants.get(vi)?.fields;
                let offs = if adt.is_enum { lay.variant_offsets.get(vi)? } else { &lay.field_offsets };
                if fields.len() != ops.len() || offs.len() != ops.len() {
                    return None;
                }
                let parts = ops.iter().zip(fields).zip(offs).map(|((o, f), &off)| Part { op: o, off, ty: cty(&p.tys, f.ty) }).collect();
                (parts, adt.is_enum.then_some(vi))
            }
            Rvalue::TupleAgg(ty, ops) => {
                let CTy::Tuple(es) = dt else { return None };
                if cty(&self.body.tys, *ty) != *dt || es.len() != ops.len() || lay.field_offsets.len() != ops.len() {
                    return None;
                }
                (ops.iter().zip(es).zip(&lay.field_offsets).map(|((o, e), &off)| Part { op: o, off, ty: e.clone() }).collect(), None)
            }
            Rvalue::ArrayAgg(ty, ops) => {
                let CTy::Array(el, n) = dt else { return None };
                if cty(&self.body.tys, *ty) != *dt || *n != ops.len() as u64 {
                    return None;
                }
                let stride = c_size_align(p, el).0;
                (ops.iter().enumerate().map(|(i, o)| Part { op: o, off: i as u64 * stride, ty: (**el).clone() }).collect(), None)
            }
            Rvalue::Opt(ty, o) => {
                let CTy::Option(inner) = dt else { return None };
                if cty(&self.body.tys, *ty) != *dt {
                    return None;
                }
                match o {
                    Some(o) => (vec![Part { op: o, off: *lay.variant_offsets.get(1)?.first()?, ty: (**inner).clone() }], Some(1)),
                    None => (Vec::new(), Some(0)),
                }
            }
            Rvalue::Res(ty, is_ok, o) => {
                let CTy::Result(a, b) = dt else { return None };
                if cty(&self.body.tys, *ty) != *dt {
                    return None;
                }
                let vi = usize::from(!*is_ok);
                let ty = if vi == 0 { (**a).clone() } else { (**b).clone() };
                (vec![Part { op: o, off: *lay.variant_offsets.get(vi)?.first()?, ty }], Some(vi))
            }
            _ => return None,
        };
        let mut tag = None;
        let mut zero = parts.is_empty();
        if let Some(vi) = variant {
            match lay.enum_tag {
                Some(EnumTag::Explicit { size, .. }) => {
                    if size > 8 {
                        return None;
                    }
                    tag = Some((0, size, (*adt_discs(p, dt).get(vi)? as u128) & scalar_mask(size)));
                    zero = false;
                }
                Some(EnumTag::NicheFilled { variant: nv, niche, first, start, .. }) if vi != nv => {
                    if niche.scalar_size > 8 {
                        return None;
                    }
                    tag = Some((niche.offset, niche.scalar_size, niche_tag_value(niche, first, start, vi)));
                    zero = false;
                }
                _ => {}
            }
        }
        Some(Shape { parts, tag, zero })
    }

    /// The bytes of a value of `size` bytes built from scalar constants (`ll_native_parts`):
    /// each part's bits little-endian at its offset, the tag or niche scalar, zeroes
    /// elsewhere. None when a part is not a scalar constant.
    fn ll_const_bytes(&self, shape: &Shape, size: u64) -> Option<Vec<u8>> {
        let mut b = vec![0u8; size as usize];
        let mut put = |off: u64, n: u64, bits: u128| {
            for i in 0..n {
                b[(off + i) as usize] = (bits >> (8 * i)) as u8;
            }
        };
        if let Some((off, n, bits)) = shape.tag {
            put(off, n, bits);
        }
        for part in &shape.parts {
            let n = c_size_align(self.p, &part.ty).0;
            let bits = match part.op {
                Operand::Const(Const::Int(v, it)) if !is128(*it) => *v & scalar_mask(n),
                Operand::Const(Const::Bool(x)) => *x as u128,
                Operand::Const(Const::Char(c)) => *c as u128,
                Operand::Const(Const::Float(bits, FloatTy::F64)) => *bits as u128,
                Operand::Const(Const::Float(bits, FloatTy::F32)) => (*bits as u32) as u128,
                Operand::Const(Const::Unit) if n == 0 => continue,
                _ => return None,
            };
            put(part.off, n, bits);
        }
        Some(b)
    }

    /// Drops the old value at plan `dp` of local `l`: its type's drop glue, or with `elab`
    /// the drop elaboration of `l` at that path (`ll_elab`: moves went through it). Drop
    /// calls are `invoke`s when `unwind` names a cleanup entry. With `flag`, `l`'s drop flag
    /// is tested and cleared first (a panic in the drop leaves the local unowned, as cgen's
    /// `emit_assign`).
    fn ll_drop_old(&mut self, ll: &mut Ll, dp: &Plan, flag: bool, elab: Option<&[Step]>, unwind: Option<u32>) {
        let l = dp.local;
        ll.conts += 1;
        let k = ll.conts;
        if flag {
            let _ = writeln!(ll.body, "  %o{k} = load i8, ptr %d{l}\n  %oc{k} = icmp ne i8 %o{k}, 0\n  br i1 %oc{k}, label %od{k}, label %on{k}\nod{k}:\n  store i8 0, ptr %d{l}");
        }
        match elab {
            Some(path) => self.ll_elab(ll, l, path, unwind),
            None => self.ll_glue_drop(ll, dp, unwind),
        }
        let _ = writeln!(ll.body, "  br label %on{k}\non{k}:");
    }

    /// A call of the drop glue of `pl`'s type on its address (an `invoke` when `unwind`
    /// names a cleanup entry; the code goes on after it).
    fn ll_glue_drop(&mut self, ll: &mut Ll, pl: &Plan, unwind: Option<u32>) {
        let glue = format!("drop_{}", mangle(&pl.ty));
        ll.decls.insert(format!("declare void @{glue}(ptr)"));
        let (a, _) = self.ll_addr(ll, pl);
        match unwind {
            Some(u) => {
                ll.pads.insert(u);
                ll.conts += 1;
                let _ = writeln!(ll.body, "  invoke void @{glue}(ptr {a}) to label %c{0} unwind label %lp{u}\nc{0}:", ll.conts);
            }
            None => {
                let _ = writeln!(ll.body, "  call void @{glue}(ptr {a})");
            }
        }
    }

    /// The native address plan of move path `path` of local `l` (the steps `path_place`
    /// reads): fields of structs, tuples, enum variants and the std iterators, array
    /// elements and box derefs, with exact C layouts. A trailing variant view stays on the
    /// enum. None for any other step or a zero-sized part.
    fn ll_path_plan(&self, ll: &Ll, l: usize, path: &[Step]) -> Option<Plan> {
        if ll.statics[l] {
            return None;
        }
        let p = self.p;
        let mut t = self.local_cty[l].clone();
        let mut steps = Vec::new();
        let mut variant: Option<u32> = None;
        for step in path {
            let (off, member, next) = match (*step, t.clone()) {
                (Step::Downcast(v), _) => {
                    variant = Some(v);
                    continue;
                }
                (Step::Deref, CTy::Boxed(inner)) => {
                    if *inner == CTy::Str || c_layout(p, &inner).is_none() || c_size_align(p, &inner).0 == 0 {
                        return None;
                    }
                    steps.push(PStep::Load((*inner).clone()));
                    t = *inner;
                    continue;
                }
                (Step::Field(i), CTy::Adt(a)) => {
                    let lay = c_layout(p, &t)?;
                    let v = variant.take();
                    let (off, member) = match v {
                        Some(v) => (*lay.variant_offsets.get(v as usize)?.get(i as usize)?, format!("u.v{v}.f{i}")),
                        None => (*lay.field_offsets.get(i as usize)?, format!("f{i}")),
                    };
                    (off, member, cty(&p.tys, p.adt(a).variants.get(v.unwrap_or(0) as usize)?.fields.get(i as usize)?.ty))
                }
                (Step::Field(i), CTy::Tuple(es)) => (*c_layout(p, &t)?.field_offsets.get(i as usize)?, format!("f{i}"), es.get(i as usize)?.clone()),
                (Step::Field(0), CTy::OptIter(_, el)) => (*c_layout(p, &t)?.field_offsets.first()?, "f0".into(), CTy::Option(el)),
                (Step::Field(i), CTy::ArrayIter(el, n)) => {
                    let next = match i {
                        0 => CTy::Array(el, n),
                        1 | 2 => CTy::Int(IntTy::Usize),
                        _ => return None,
                    };
                    (*c_layout(p, &t)?.field_offsets.get(i as usize)?, format!("f{i}"), next)
                }
                (Step::Field(_), CTy::Option(inner)) => {
                    variant = None;
                    (*c_layout(p, &t)?.variant_offsets.get(1)?.first()?, "u.v1.f0".into(), *inner)
                }
                (Step::Field(_), CTy::Result(a, b)) => {
                    let v = variant.take().unwrap_or(0);
                    (*c_layout(p, &t)?.variant_offsets.get(v as usize)?.first()?, format!("u.v{v}.f0"), if v == 0 { *a } else { *b })
                }
                (Step::Elem(c), CTy::Array(el, n)) if c < n => {
                    c_layout(p, &t)?;
                    (c * c_size_align(p, &el).0, format!("v[{c}]"), *el)
                }
                _ => return None,
            };
            if c_size_align(p, &next).0 == 0 {
                return None;
            }
            steps.push(PStep::Offset(off, member));
            t = next;
        }
        c_layout(p, &t)?;
        Some(Plan { local: l, steps, ty: t })
    }

    /// The distinct next steps of local `l`'s move paths below `prefix`, in path order.
    fn elab_next_steps(&self, l: usize, prefix: &[Step]) -> Vec<Step> {
        let mut v: Vec<Step> = Vec::new();
        for p in &self.move_paths[l] {
            if p.len() > prefix.len() && p.starts_with(prefix) && !v.contains(&p[prefix.len()]) {
                v.push(p[prefix.len()]);
            }
        }
        v
    }

    /// True when `ll_elab` lowers `elab_drop(l, prefix)` natively: every part it drops has
    /// a native address, every enum it switches on a native discriminant (`ll_disc_ok`).
    fn ll_elab_ok(&self, ll: &Ll, l: usize, prefix: &[Step]) -> bool {
        let deeper = self.move_paths[l].iter().any(|p| p.len() > prefix.len() && p.starts_with(prefix));
        let Some((_, t)) = self.path_place(l as Local, prefix) else { return false };
        let plan = self.ll_path_plan(ll, l, prefix);
        if !deeper {
            return !needs_drop_c(self.p, &t) || plan.is_some();
        }
        let sub = |s: Step| [prefix, &[s]].concat();
        let variant = matches!(prefix.last(), Some(Step::Downcast(_)));
        let next = self.elab_next_steps(l, prefix);
        match &t {
            CTy::Array(..) if !variant => plan.is_some() && next.iter().all(|s| matches!(s, Step::Elem(_)) && self.ll_elab_ok(ll, l, &sub(*s))),
            CTy::ArrayIter(..) => !needs_drop_c(self.p, &t) || plan.is_some(),
            CTy::Boxed(_) => plan.is_some() && self.ll_elab_ok(ll, l, &sub(Step::Deref)),
            _ if self.elab_is_enum(&t) && !variant => {
                plan.is_some() && self.ll_disc_ok(&t) && next.iter().all(|s| !matches!(s, Step::Downcast(_)) || self.ll_elab_ok(ll, l, &sub(*s)))
            }
            _ => (0..self.elab_fields(&t, prefix)).all(|f| self.ll_elab_ok(ll, l, &sub(Step::Field(f as u32)))),
        }
    }

    /// True for an enum C type (`elab_parts` switches on its variant).
    fn elab_is_enum(&self, t: &CTy) -> bool {
        match t {
            CTy::Adt(a) => self.p.adt(*a).is_enum,
            CTy::Option(_) | CTy::Result(..) => true,
            _ => false,
        }
    }

    /// The number of fields `elab_parts` drops one by one in a value of type `t` at `prefix`
    /// (after a variant view: that variant's).
    fn elab_fields(&self, t: &CTy, prefix: &[Step]) -> usize {
        let variant = match prefix.last() {
            Some(Step::Downcast(v)) => Some(*v as usize),
            _ => None,
        };
        match t {
            CTy::Tuple(es) => es.len(),
            CTy::OptIter(..) => 1,
            CTy::Adt(a) => self.p.adt(*a).variants.get(variant.unwrap_or(0)).map_or(0, |v| v.fields.len()),
            CTy::Option(_) => usize::from(variant == Some(1)),
            CTy::Result(..) => usize::from(variant.is_some()),
            _ => 0,
        }
    }

    /// `elab_drop` as native IR: drops the part of local `l` at `prefix` that the fn still
    /// owns, in cgen's order: a moved path only while its flag is set, a place above moved
    /// paths part by part (an enum only in the variant the paths go through), any other
    /// place whole. Drop calls are `invoke`s when `unwind` names a cleanup entry. The caller
    /// checked `ll_elab_ok`.
    fn ll_elab(&mut self, ll: &mut Ll, l: usize, prefix: &[Step], unwind: Option<u32>) {
        let own = self.move_paths[l].iter().position(|p| p == prefix);
        let deeper = self.move_paths[l].iter().any(|p| p.len() > prefix.len() && p.starts_with(prefix));
        let (_, t) = self.path_place(l as Local, prefix).expect("checked by ll_elab_ok");
        let skip = own.map(|k| {
            ll.conts += 1;
            let j = ll.conts;
            let _ = writeln!(ll.body, "  %ef{j} = load i8, ptr %m{l}_{k}\n  %ec{j} = icmp ne i8 %ef{j}, 0\n  br i1 %ec{j}, label %ey{j}, label %en{j}\ney{j}:");
            j
        });
        if deeper {
            self.ll_elab_parts(ll, l, prefix, &t, unwind);
        } else if needs_drop_c(self.p, &t) {
            self.want(Glue::Drop, &t);
            let plan = self.ll_path_plan(ll, l, prefix).expect("checked by ll_elab_ok");
            self.ll_glue_drop(ll, &plan, unwind);
        }
        if let Some(j) = skip {
            let _ = writeln!(ll.body, "  br label %en{j}\nen{j}:");
        }
    }

    /// `elab_parts` as native IR (`ll_elab` one level down): the fields of a struct, tuple
    /// or enum variant in order, an array's elements (runs with no move path drop as a loop;
    /// runs and elements in reverse), a box's pointee then its allocation, or a switch over
    /// the enum variants the moved paths go through (the others drop whole).
    fn ll_elab_parts(&mut self, ll: &mut Ll, l: usize, prefix: &[Step], t: &CTy, unwind: Option<u32>) {
        let p = self.p;
        let sub = |s: Step| [prefix, &[s]].concat();
        let next = self.elab_next_steps(l, prefix);
        let variant = matches!(prefix.last(), Some(Step::Downcast(_)));
        match t {
            CTy::Array(el, n) if !variant => {
                let kept: Vec<u64> = next.iter().filter_map(|s| if let Step::Elem(c) = s { Some(*c) } else { None }).collect();
                let mut parts: Vec<Result<(u64, u64), u64>> = Vec::new();
                let (mut dropping, mut start) = (true, 0);
                for i in 0..*n {
                    let keep = kept.contains(&i);
                    if dropping && keep {
                        parts.push(Ok((start, i)));
                        dropping = false;
                    } else if !dropping && !keep {
                        dropping = true;
                        start = i;
                    }
                    if keep {
                        parts.push(Err(i));
                    }
                }
                if dropping {
                    parts.push(Ok((start, *n)));
                }
                for part in parts.into_iter().rev() {
                    match part {
                        Ok((a, b)) if b > a => {
                            self.want(Glue::Drop, el);
                            let glue = format!("drop_{}", mangle(el));
                            ll.decls.insert(format!("declare void @{glue}(ptr)"));
                            let plan = self.ll_path_plan(ll, l, prefix).expect("checked by ll_elab_ok");
                            let (base, _) = self.ll_addr(ll, &plan);
                            let stride = c_size_align(p, el).0;
                            ll.conts += 1;
                            let j = ll.conts;
                            let _ = writeln!(ll.allocas, "  %ai{j} = alloca i64");
                            let _ = writeln!(
                                ll.body,
                                "  store i64 {a}, ptr %ai{j}\n  br label %ah{j}\nah{j}:\n  %av{j} = load i64, ptr %ai{j}\n  %ac{j} = icmp ult i64 %av{j}, {b}\n  br i1 %ac{j}, label %ab{j}, label %ax{j}\nab{j}:\n  %ae{j} = getelementptr inbounds [{stride} x i8], ptr {base}, i64 %av{j}"
                            );
                            match unwind {
                                Some(u) => {
                                    ll.pads.insert(u);
                                    let _ = writeln!(ll.body, "  invoke void @{glue}(ptr %ae{j}) to label %ak{j} unwind label %lp{u}\nak{j}:");
                                }
                                None => {
                                    let _ = writeln!(ll.body, "  call void @{glue}(ptr %ae{j})");
                                }
                            }
                            let _ = writeln!(ll.body, "  %an{j} = add i64 %av{j}, 1\n  store i64 %an{j}, ptr %ai{j}\n  br label %ah{j}\nax{j}:");
                        }
                        Ok(_) => {}
                        Err(c) => self.ll_elab(ll, l, &sub(Step::Elem(c)), unwind),
                    }
                }
            }
            CTy::ArrayIter(..) => {
                if needs_drop_c(p, t) {
                    self.want(Glue::Drop, t);
                    let plan = self.ll_path_plan(ll, l, prefix).expect("checked by ll_elab_ok");
                    self.ll_glue_drop(ll, &plan, unwind);
                }
            }
            CTy::Boxed(inner) => {
                // The still-owned part behind the pointer, then the allocation itself.
                self.ll_elab(ll, l, &sub(Step::Deref), unwind);
                let plan = self.ll_path_plan(ll, l, prefix).expect("checked by ll_elab_ok");
                let (a, al) = self.ll_addr(ll, &plan);
                let (size, align) = c_size_align(p, inner);
                ll.decls.insert("declare void @lust_dealloc(ptr, i64, i64)".into());
                ll.conts += 1;
                let _ = writeln!(ll.body, "  %bx{0} = load ptr, ptr {a}, align {1}\n  call void @lust_dealloc(ptr %bx{0}, i64 {size}, i64 {align})", ll.conts, al.min(8));
            }
            _ if self.elab_is_enum(t) && !variant => {
                let plan = self.ll_path_plan(ll, l, prefix).expect("checked by ll_elab_ok");
                let idx = self.ll_disc(ll, &plan, "i32");
                ll.conts += 1;
                let j = ll.conts;
                let cases: Vec<u32> = next.iter().filter_map(|s| if let Step::Downcast(v) = s { Some(*v) } else { None }).collect();
                let _ = write!(ll.body, "  switch i32 {idx}, label %sd{j} [");
                for v in &cases {
                    let _ = write!(ll.body, " i32 {v}, label %sc{j}_{v}");
                }
                ll.body.push_str(" ]\n");
                for v in cases {
                    let _ = writeln!(ll.body, "sc{j}_{v}:");
                    self.ll_elab(ll, l, &sub(Step::Downcast(v)), unwind);
                    let _ = writeln!(ll.body, "  br label %sx{j}");
                }
                let _ = writeln!(ll.body, "sd{j}:");
                self.want(Glue::Drop, t);
                self.ll_glue_drop(ll, &plan, unwind);
                let _ = writeln!(ll.body, "  br label %sx{j}\nsx{j}:");
            }
            _ => {
                for f in 0..self.elab_fields(t, prefix) {
                    self.ll_elab(ll, l, &sub(Step::Field(f as u32)), unwind);
                }
            }
        }
    }

    /// Statement `dest = rv` built in place: an aggregate (`ll_shape`) into any native
    /// place, or a copy or move into a place that needs drop. Every operand is read before
    /// the first store, so a source cannot overlap the destination. A destination that needs
    /// drop drops its old value and is marked owned again as cgen's `emit_assign` and
    /// `drop_old_value` do, in their order. False (nothing emitted) for any other shape, a
    /// value that reads the destination's local, or an old value that needs drop
    /// elaboration (moves went through it).
    fn ll_native_parts(&mut self, ll: &mut Ll, dest: &Place, rv: &Rvalue, dp: &Plan, unwind: Option<u32>) -> bool {
        let p = self.p;
        let Some(shape) = self.ll_shape(rv, &dp.ty) else { return false };
        if rvalue_mentions(rv, dest.local) {
            return false;
        }
        // Check every operand before emitting anything; collect the flags its moves clear.
        let mut clears: Vec<String> = Vec::new();
        for part in &shape.parts {
            match part.op {
                Operand::Copy(pl) | Operand::Move(pl) => {
                    if !self.ll_plan(ll, pl).is_some_and(|sp| sp.ty == part.ty) {
                        return false;
                    }
                    if matches!(part.op, Operand::Move(_)) && self.local_drop[pl.local as usize] {
                        if pl.proj.is_empty() {
                            if self.dflags.keeps(pl.local) {
                                clears.push(format!("%d{}", pl.local));
                            }
                        } else if let Some(k) = self.steps_of(pl).and_then(|path| self.move_flag(pl.local, &path)) {
                            clears.push(format!("%m{}_{k}", pl.local));
                        }
                    }
                }
                Operand::Const(Const::Unit) if c_size_align(p, &part.ty).0 == 0 => {}
                o => {
                    if !self.ll_scalar_ok(ll, o).is_some_and(|(t, _)| t == part.ty) {
                        return false;
                    }
                }
            }
        }
        // The old value (`drop_old_value`): `old` is Some when it drops here, true when the
        // local's drop flag is tested first (else it drops on every path); `elab` the move
        // path to elaborate when moves went through the place; `refill` the flags set after
        // the store (the local's drop flag, the move flags at or below the place).
        let l = dest.local as usize;
        let drop = needs_drop_c(p, &dp.ty);
        let mut old: Option<bool> = None;
        let mut elab: Option<Vec<Step>> = None;
        let mut refill: Vec<String> = Vec::new();
        if drop {
            if dest.proj.is_empty() {
                if !self.local_drop[l] {
                    return false;
                }
                if !self.move_paths[l].is_empty() {
                    if !self.dflags.keeps(dest.local) || !self.ll_elab_ok(ll, l, &[]) {
                        return false;
                    }
                    elab = Some(Vec::new());
                }
                if self.dflags.keeps(dest.local) {
                    old = Some(true);
                    refill.push(format!("%d{l}"));
                } else if self.dflags.test(self.at, dest.local) == Some(true) {
                    old = Some(false);
                }
                refill.extend((0..self.move_paths[l].len()).map(|k| format!("%m{l}_{k}")));
            } else {
                old = Some(false);
                if let Some(path) = self.steps_of(dest)
                    && self.move_paths[l].iter().any(|m| m.starts_with(&path))
                {
                    if !self.ll_elab_ok(ll, l, &path) {
                        return false;
                    }
                    refill.extend(self.move_paths[l].iter().enumerate().filter(|(_, m)| m.starts_with(&path)).map(|(k, _)| format!("%m{l}_{k}")));
                    elab = Some(path);
                }
            }
            // Wanted even with no drop here: other C names the glue too. (An elaborated
            // drop wants the glue of the parts it drops.)
            if elab.is_none() {
                self.want(Glue::Drop, &dp.ty);
            }
        }
        // cgen's order: a statement that can unwind computes the value first and drops the old
        // one after (a panic leaves the destination as it was); otherwise a whole local drops
        // its old value first.
        let unw = self.stmt_action(self.at.0 as usize, self.at.1 as usize).is_some() && (drop || !dest.proj.is_empty());
        let drop_first = drop && dest.proj.is_empty() && !unw;
        if drop_first && let Some(flag) = old {
            self.ll_drop_old(ll, dp, flag, elab.as_deref(), unwind);
        }
        // A value read before the old value drops is held in temporaries (the drop may write
        // memory); so is an operand read through a pointer while other parts get stored.
        let stage_all = old.is_some() && !drop_first;
        let mut held = Vec::new();
        for part in &shape.parts {
            let pass = pass_of(p, &part.ty);
            let h = match part.op {
                _ if pass == Pass::Skip => Held::Skip,
                Operand::Copy(pl) | Operand::Move(pl) => {
                    let sp = self.ll_plan(ll, pl).expect("checked above");
                    let (a, al) = self.ll_addr(ll, &sp);
                    ll.conts += 1;
                    let k = ll.conts;
                    match pass {
                        Pass::Scalar(t, _) => {
                            let facts = self.ll_load_facts(&sp.ty);
                            let _ = writeln!(ll.body, "  %h{k} = load {t}, ptr {a}, align {al}{facts}");
                            Held::Ssa(t, format!("%h{k}"))
                        }
                        Pass::Bits(n) => {
                            let t = bits_types(n).0;
                            let _ = writeln!(ll.body, "  %h{k} = load {t}, ptr {a}, align {}", al.min(n));
                            Held::Ssa(t, format!("%h{k}"))
                        }
                        // A 16-byte part (a `&str`, a slice) is copied as bytes like any other
                        // aggregate: two `i64` words would make SROA cast its pointer word.
                        _ if stage_all || (shape.parts.len() > 1 && sp.steps.iter().any(|s| matches!(s, PStep::Load(_) | PStep::LoadAt(..)))) => {
                            let (size, align) = c_size_align(p, &part.ty);
                            ll.decls.insert("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)".into());
                            ll.decls.insert("declare void @llvm.lifetime.start.p0(i64, ptr)".into());
                            ll.decls.insert("declare void @llvm.lifetime.end.p0(i64, ptr)".into());
                            let _ = writeln!(ll.allocas, "  %h{k} = alloca [{size} x i8], align {align}");
                            let _ = writeln!(
                                ll.body,
                                "  call void @llvm.lifetime.start.p0(i64 {size}, ptr %h{k})\n  call void @llvm.memcpy.p0.p0.i64(ptr align {align} %h{k}, ptr align {al} {a}, i64 {size}, i1 false)"
                            );
                            Held::Mem(format!("%h{k}"), align, true)
                        }
                        _ => Held::Mem(a, al, false),
                    }
                }
                o => {
                    let Pass::Scalar(t, _) = pass else { unreachable!("checked above") };
                    Held::Ssa(t, self.ll_scalar(ll, o))
                }
            };
            held.push(h);
        }
        let clear = |ll: &mut Ll| {
            for f in &clears {
                let _ = writeln!(ll.body, "  store i8 0, ptr {f}");
            }
        };
        if !drop_first && let Some(flag) = old {
            clear(ll);
            self.ll_drop_old(ll, dp, flag, elab.as_deref(), unwind);
        }
        // A table of scalar constants is one copy of its bytes from a constant, as clang
        // makes a compound literal of constants (each element stored apart is a few IR lines,
        // and a table of thousands of them is a giant body).
        let size = c_size_align(p, &dp.ty).0;
        if old.is_none()
            && shape.parts.len() >= 8
            && let Some(bytes) = self.ll_const_bytes(&shape, size)
        {
            let (da, dalign) = self.ll_addr(ll, dp);
            ll.conts += 1;
            let k = ll.conts;
            let align = c_size_align(p, &dp.ty).1.max(1);
            ll.decls.insert(format!("@lkc_{}_{k} = private unnamed_addr constant [{size} x i8] c\"{}\", align {align}", ll.tag, ll_bytes_lit(&bytes)));
            ll.decls.insert("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)".into());
            let _ = writeln!(ll.body, "  call void @llvm.memcpy.p0.p0.i64(ptr align {dalign} {da}, ptr align {align} @lkc_{}_{k}, i64 {size}, i1 false)", ll.tag);
            for f in &refill {
                let _ = writeln!(ll.body, "  store i8 1, ptr {f}");
            }
            clear(ll);
            return true;
        }
        // The stores: zeroes, the tag, the parts.
        let (da, dalign) = self.ll_addr(ll, dp);
        let at = |ll: &mut Ll, off: u64| -> (String, u64) {
            if off == 0 {
                return (da.clone(), dalign);
            }
            ll.conts += 1;
            let _ = writeln!(ll.body, "  %g{0} = getelementptr inbounds i8, ptr {da}, i64 {off}", ll.conts);
            (format!("%g{}", ll.conts), dalign.min(1 << off.trailing_zeros()))
        };
        if shape.zero && size > 0 {
            ll.decls.insert("declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)".into());
            let _ = writeln!(ll.body, "  call void @llvm.memset.p0.i64(ptr align {dalign} {da}, i8 0, i64 {size}, i1 false)");
        }
        if let Some((off, n, bits)) = shape.tag {
            let (a, al) = at(ll, off);
            let _ = writeln!(ll.body, "  store {} {}, ptr {a}, align {}", bits_types(n).0, ll_int_lit(bits, n), al.min(n));
        }
        for (part, h) in shape.parts.iter().zip(held) {
            match h {
                Held::Skip => {}
                Held::Ssa(t, v) => {
                    let (a, al) = at(ll, part.off);
                    let _ = writeln!(ll.body, "  store {t} {v}, ptr {a}, align {al}");
                }
                Held::Mem(src, sal, temp) => {
                    let (a, al) = at(ll, part.off);
                    let n = c_size_align(p, &part.ty).0;
                    ll.decls.insert("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)".into());
                    let _ = writeln!(ll.body, "  call void @llvm.memcpy.p0.p0.i64(ptr align {al} {a}, ptr align {sal} {src}, i64 {n}, i1 false)");
                    if temp {
                        let _ = writeln!(ll.body, "  call void @llvm.lifetime.end.p0(i64 {n}, ptr {src})");
                    }
                }
            }
        }
        for f in &refill {
            let _ = writeln!(ll.body, "  store i8 1, ptr {f}");
        }
        if drop_first || old.is_none() {
            clear(ll);
        }
        true
    }

    /// A call of a builtin that only reads its argument's fields (a length, a capacity,
    /// emptiness, `String::as_str`, `Cell::get`), lowered natively as cgen's builtin forms
    /// write it. False (nothing emitted) for any other builtin or shape.
    fn ll_native_builtin(&mut self, ll: &mut Ll, b: Builtin, args: &[Operand], dest: &Place) -> bool {
        use Builtin as B;
        let p = self.p;
        if dest.proj.iter().any(|p| matches!(p, Proj::Index(_))) {
            return false;
        }
        let Some(dp) = self.ll_plan(ll, dest) else { return false };
        let [a] = args else { return false };
        if needs_drop_c(p, &dp.ty) {
            return false;
        }
        let usize_dest = dp.ty == CTy::Int(IntTy::Usize);
        let bool_dest = dp.ty == CTy::Bool;
        // The value: `Word(i64 value)` or `Str(ptr, len)`.
        let thin = self.ll_scalar_ok(ll, a).and_then(|(t, _)| match t {
            CTy::Ref(inner) | CTy::Ptr(inner) => Some(*inner),
            _ => None,
        });
        // A word at `off` behind the thin pointer argument.
        let field = |s: &mut Self, ll: &mut Ll, off: u64| -> String {
            let ptr = s.ll_scalar_operand_value(ll, a);
            ll.conts += 1;
            let k = ll.conts;
            let _ = writeln!(ll.body, "  %bq{k} = getelementptr inbounds i8, ptr {ptr}, i64 {off}\n  %bv{k} = load i64, ptr %bq{k}, align 8");
            format!("%bv{k}")
        };
        // A word at `off` in the fat argument (a `&str` or slice value).
        let fat_field = |s: &mut Self, ll: &mut Ll, off: u64| -> Option<String> {
            let (Operand::Copy(pl) | Operand::Move(pl)) = a else { return None };
            let plan = s.ll_plan(ll, pl)?;
            let (addr, al) = s.ll_addr(ll, &plan);
            ll.conts += 1;
            let k = ll.conts;
            let _ = writeln!(ll.body, "  %bq{k} = getelementptr inbounds i8, ptr {addr}, i64 {off}\n  %bv{k} = load i64, ptr %bq{k}, align {}", al.min(8));
            Some(format!("%bv{k}"))
        };
        let is_empty = |ll: &mut Ll, v: String| -> String {
            ll.conts += 1;
            let k = ll.conts;
            let _ = writeln!(ll.body, "  %be{k} = icmp eq i64 {v}, 0\n  %bz{k} = zext i1 %be{k} to i8");
            format!("%bz{k}")
        };
        let fat_ok = |s: &Self, ll: &Ll, want: &dyn Fn(&CTy) -> bool| -> bool {
            matches!(a, Operand::Copy(pl) | Operand::Move(pl) if s.ll_plan(ll, pl).is_some_and(|pl| want(&pl.ty)))
        };
        let str_ty = |t: &CTy| matches!(t, CTy::Ref(i) if **i == CTy::Str);
        let slice_ty = |t: &CTy| matches!(t, CTy::Slice(_));
        let (value, ty): (String, &str) = match b {
            B::VecLen | B::StringLen if usize_dest && matches!(thin, Some(CTy::Vec(_) | CTy::String)) => (field(self, ll, 8), "i64"),
            B::VecIsEmpty | B::StringIsEmpty if bool_dest && matches!(thin, Some(CTy::Vec(_) | CTy::String)) => {
                let v = field(self, ll, 8);
                (is_empty(ll, v), "i8")
            }
            B::StringCapacity if usize_dest && thin == Some(CTy::String) => (field(self, ll, 16), "i64"),
            // A zero-sized element's capacity is `usize::MAX` (`vec_cap`).
            B::VecCapacity if usize_dest && matches!(&thin, Some(CTy::Vec(_))) => {
                let Some(CTy::Vec(el)) = &thin else { unreachable!() };
                if c_size_align(p, el).0 == 0 { ("-1".into(), "i64") } else { (field(self, ll, 16), "i64") }
            }
            B::VecIterLen if usize_dest && matches!(thin, Some(CTy::VecIter(_))) => {
                let (len, front) = (field(self, ll, 8), field(self, ll, 24));
                ll.conts += 1;
                let _ = writeln!(ll.body, "  %bl{0} = sub i64 {len}, {front}", ll.conts);
                (format!("%bl{}", ll.conts), "i64")
            }
            B::StrLen | B::StrIsEmpty if (usize_dest || bool_dest) && fat_ok(self, ll, &str_ty) => {
                let v = fat_field(self, ll, 8).expect("checked");
                if b == B::StrLen { (v, "i64") } else { (is_empty(ll, v), "i8") }
            }
            B::SliceLen | B::SliceIsEmpty if (usize_dest || bool_dest) && (fat_ok(self, ll, &slice_ty) || matches!(thin, Some(CTy::Array(..)))) => {
                let v = match &thin {
                    Some(CTy::Array(_, n)) => n.to_string(),
                    _ => fat_field(self, ll, 8).expect("checked"),
                };
                if b == B::SliceLen { (v, "i64") } else { (is_empty(ll, v), "i8") }
            }
            B::StringAsStr | B::StringAsMutStr if thin == Some(CTy::String) && str_ty(&dp.ty) => {
                let ptr = self.ll_scalar_operand_value(ll, a);
                let (da, dalign) = self.ll_addr(ll, &dp);
                ll.conts += 1;
                let k = ll.conts;
                let al = dalign.min(8);
                let _ = writeln!(
                    ll.body,
                    "  %bp{k} = load ptr, ptr {ptr}, align 8\n  %bq{k} = getelementptr inbounds i8, ptr {ptr}, i64 8\n  %bn{k} = load i64, ptr %bq{k}, align 8\n  store ptr %bp{k}, ptr {da}, align {al}\n  %br{k} = getelementptr inbounds i8, ptr {da}, i64 8\n  store i64 %bn{k}, ptr %br{k}, align {al}"
                );
                return true;
            }
            // `(*p)`: a Cell's C form is its value's.
            B::CellGet if matches!(&thin, Some(CTy::Cell(e)) if **e == dp.ty) => {
                let ptr = self.ll_scalar_operand_value(ll, a);
                let (da, dalign) = self.ll_addr(ll, &dp);
                let (size, align) = c_size_align(p, &dp.ty);
                match pass_of(p, &dp.ty) {
                    Pass::Skip => {}
                    Pass::Scalar(t, _) => {
                        ll.conts += 1;
                        let facts = self.ll_load_facts(&dp.ty);
                        let _ = writeln!(ll.body, "  %bc{0} = load {t}, ptr {ptr}, align {align}{facts}\n  store {t} %bc{0}, ptr {da}, align {dalign}", ll.conts);
                    }
                    _ => {
                        ll.decls.insert("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)".into());
                        let _ = writeln!(ll.body, "  call void @llvm.memcpy.p0.p0.i64(ptr align {dalign} {da}, ptr align {align} {ptr}, i64 {size}, i1 false)");
                    }
                }
                return true;
            }
            _ => return false,
        };
        let (da, dalign) = self.ll_addr(ll, &dp);
        let _ = writeln!(ll.body, "  store {ty} {value}, ptr {da}, align {dalign}");
        true
    }

    /// `ll_scalar` without the move's flag clear: a call clears its arguments' flags itself.
    fn ll_scalar_operand_value(&mut self, ll: &mut Ll, o: &Operand) -> String {
        match o {
            Operand::Move(pl) => self.ll_scalar(ll, &Operand::Copy(pl.clone())),
            o => self.ll_scalar(ll, o),
        }
    }

    /// Lowers statement `s` to LLVM IR directly when it has a simple form: a copy, move,
    /// constant or address of native places into a place that owns nothing to drop, or the
    /// drop of a local that no partial move touches. False: the statement runs as a helper.
    /// `unwind` is its cleanup entry (a drop can unwind).
    fn ll_native_stmt(&mut self, ll: &mut Ll, s: &Stmt, unwind: Option<u32>) -> bool {
        match &s.kind {
            // A compile-time promoted local's value is its static
            // initializer (`kstatic`): its defining assignment never runs.
            StmtKind::Assign(dest, _) if dest.proj.is_empty() && self.kstatic.contains_key(&dest.local) => true,
            StmtKind::Assign(dest, rv) => {
                // An indexed destination keeps cgen's form: its bounds check runs before the value
                // moves in, with a guard that drops the value (`emit_assign`).
                if dest.proj.iter().any(|p| matches!(p, Proj::Index(_))) {
                    return false;
                }
                let Some(dp) = self.ll_plan(ll, dest) else { return false };
                let aggregate = matches!(rv, Rvalue::Aggregate(..) | Rvalue::TupleAgg(..) | Rvalue::ArrayAgg(..) | Rvalue::Opt(..) | Rvalue::Res(..));
                if aggregate || needs_drop_c(self.p, &dp.ty) {
                    return self.ll_native_parts(ll, dest, rv, &dp, unwind);
                }
                match rv {
                    Rvalue::Use(o @ (Operand::Copy(src) | Operand::Move(src))) => {
                        let Some(sp) = self.ll_plan(ll, src) else { return false };
                        if sp.ty != dp.ty {
                            return false;
                        }
                        // The flag a move clears (`operand`): the whole local's, or its path's.
                        let mut clear: Option<String> = None;
                        if matches!(o, Operand::Move(_)) && self.local_drop[src.local as usize] {
                            if src.proj.is_empty() {
                                clear = self.dflags.keeps(src.local).then(|| format!("%d{}", src.local));
                            } else {
                                match self.steps_of(src).and_then(|path| self.move_flag(src.local, &path)) {
                                    Some(k) => clear = Some(format!("%m{}_{k}", src.local)),
                                    None => return false,
                                }
                            }
                        }
                        let (sa, salign) = self.ll_addr(ll, &sp);
                        let (da, dalign) = self.ll_addr(ll, &dp);
                        match pass_of(self.p, &dp.ty) {
                            Pass::Skip => {}
                            Pass::Scalar(t, _) => {
                                ll.conts += 1;
                                let facts = self.ll_load_facts(&sp.ty);
                                let _ = writeln!(ll.body, "  %v{0} = load {t}, ptr {sa}, align {salign}{facts}\n  store {t} %v{0}, ptr {da}, align {dalign}", ll.conts);
                            }
                            _ => {
                                let size = c_size_align(self.p, &dp.ty).0;
                                // A source inside the destination's own local may overlap it.
                                let f = if src.local == dest.local { "memmove" } else { "memcpy" };
                                ll.decls.insert(format!("declare void @llvm.{f}.p0.p0.i64(ptr, ptr, i64, i1)"));
                                let _ = writeln!(ll.body, "  call void @llvm.{f}.p0.p0.i64(ptr align {dalign} {da}, ptr align {salign} {sa}, i64 {size}, i1 false)");
                            }
                        }
                        if let Some(flag) = clear {
                            let _ = writeln!(ll.body, "  store i8 0, ptr {flag}");
                        }
                        true
                    }
                    Rvalue::Use(Operand::Const(c)) => {
                        let lit = match (c, &dp.ty) {
                            (Const::Int(v, it), CTy::Int(dt)) if it == dt && !is128(*it) => (*v as i128 & ((1i128 << it.bits()) - 1)).to_string(),
                            (Const::Bool(b), CTy::Bool) => (*b as u8).to_string(),
                            (Const::Char(ch), CTy::Char) => (*ch as u32).to_string(),
                            // As `ll_scalar` writes a float constant.
                            (Const::Float(bits, f), CTy::Float(df)) if f == df => match f {
                                FloatTy::F64 => format!("0x{bits:016X}"),
                                FloatTy::F32 => format!("0x{:016X}", (f32::from_bits(*bits as u32) as f64).to_bits()),
                            },
                            (Const::Unit, CTy::Unit) => return true,
                            _ => return false,
                        };
                        let Pass::Scalar(t, _) = pass_of(self.p, &dp.ty) else { return false };
                        let (da, dalign) = self.ll_addr(ll, &dp);
                        let _ = writeln!(ll.body, "  store {t} {lit}, ptr {da}, align {dalign}");
                        true
                    }
                    Rvalue::Ref(_, place) => {
                        // `&*x` of a fat `x` (`&str`, `&[T]`, `&dyn`) is the fat value itself
                        // (cgen's `Rvalue::Ref`): its two words copied, when the C types agree.
                        if let Some((Proj::Deref, head)) = place.proj.split_last()
                            && let Some(xp) = self.ll_plan(ll, &Place { local: place.local, proj: head.to_vec() })
                            && (matches!(&xp.ty, CTy::Ref(inner) if **inner == CTy::Str) || matches!(&xp.ty, CTy::Slice(_) | CTy::Dyn))
                            && ctype(&xp.ty) == ctype(&dp.ty)
                            && pass_of(self.p, &dp.ty) == Pass::Pair
                        {
                            let (sa, salign) = self.ll_addr(ll, &xp);
                            let (da, dalign) = self.ll_addr(ll, &dp);
                            ll.decls.insert("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)".into());
                            let _ = writeln!(ll.body, "  call void @llvm.memcpy.p0.p0.i64(ptr align {dalign} {da}, ptr align {salign} {sa}, i64 16, i1 false)");
                            return true;
                        }
                        let Some(sp) = self.ll_plan(ll, place) else { return false };
                        // Only a thin reference to the place: fat places (str, slices, dyn) keep cgen's forms.
                        let thin = matches!(&dp.ty, CTy::Ref(inner) if **inner == sp.ty) || matches!(&dp.ty, CTy::Ptr(inner) if **inner == sp.ty);
                        if !thin || matches!(sp.ty, CTy::Str | CTy::Slice(_) | CTy::Dyn | CTy::Unsized(..) | CTy::DynCell | CTy::DynLock(_)) {
                            return false;
                        }
                        if pass_of(self.p, &dp.ty) != Pass::Scalar("ptr", "") {
                            return false;
                        }
                        let (sa, _) = self.ll_addr(ll, &sp);
                        let (da, dalign) = self.ll_addr(ll, &dp);
                        let _ = writeln!(ll.body, "  store ptr {sa}, ptr {da}, align {dalign}");
                        true
                    }
                    rv => self.ll_native_value(ll, rv, &dp),
                }
            }
            StmtKind::Drop(l) => {
                let l = *l as usize;
                if !self.local_drop[l] {
                    return true;
                }
                if ll.statics[l] {
                    return false;
                }
                // Partial moves: the drop elaboration (`ll_elab`), under a runtime flag.
                let elab = !self.move_paths[l].is_empty();
                if elab && (!self.dflags.keeps(l as Local) || !self.ll_elab_ok(ll, l, &[])) {
                    return false;
                }
                // A static flag (`ir::dropflags`): drop on every path here, or on none.
                let static_drop = if self.dflags.keeps(l as Local) { None } else { self.dflags.test(self.at, l as Local) };
                let t = self.local_cty[l].clone();
                // Wanted even with no drop here: other C names the glue too.
                if !elab {
                    self.want(Glue::Drop, &t);
                }
                if static_drop == Some(false) {
                    return true;
                }
                if elab {
                    ll.conts += 1;
                    let k = ll.conts;
                    let _ = writeln!(
                        ll.body,
                        "  %v{k} = load i8, ptr %d{l}\n  %c{k} = icmp ne i8 %v{k}, 0\n  br i1 %c{k}, label %dr{k}, label %dn{k}\ndr{k}:\n  store i8 0, ptr %d{l}"
                    );
                    self.ll_elab(ll, l, &[], unwind);
                    let _ = writeln!(ll.body, "  br label %dn{k}\ndn{k}:");
                    return true;
                }
                let glue = format!("drop_{}", mangle(&t));
                ll.decls.insert(format!("declare void @{glue}(ptr)"));
                ll.conts += 1;
                let k = ll.conts;
                if static_drop.is_some() {
                    let _ = writeln!(ll.body, "  br label %dr{k}\ndr{k}:");
                } else {
                    let _ = writeln!(
                        ll.body,
                        "  %v{k} = load i8, ptr %d{l}\n  %c{k} = icmp ne i8 %v{k}, 0\n  br i1 %c{k}, label %dr{k}, label %dn{k}\ndr{k}:\n  store i8 0, ptr %d{l}"
                    );
                }
                match unwind {
                    Some(u) => {
                        ll.pads.insert(u);
                        let _ = writeln!(ll.body, "  invoke void @{glue}(ptr %l{l}) to label %dn{k} unwind label %lp{u}");
                    }
                    None => {
                        let _ = writeln!(ll.body, "  call void @{glue}(ptr %l{l})\n  br label %dn{k}");
                    }
                }
                let _ = writeln!(ll.body, "dn{k}:");
                true
            }
            _ => false,
        }
    }
}

/// The LLVM fn attributes of fn `f`'s source attributes, as rustc maps them: `#[inline]`
/// inlinehint, `#[inline(always)]` alwaysinline, `#[inline(never)]` noinline, `#[cold]`
/// cold. A closure body fn or a trait method stub borrows another fn's def: none.
fn source_fn_attrs(p: &Program, f: LocalDefId) -> String {
    use crate::check::generics::FnClass;
    use crate::lexer::{Tok, TokenTree};
    if p.gx.closure_fns.contains_key(&f) || matches!(p.gx.fn_class.get(f.0 as usize), Some(FnClass::Stub)) {
        return String::new();
    }
    let mut out = String::new();
    for a in &p.fn_info(f).def(&p.ast).attrs {
        if a.path.len() != 1 {
            continue;
        }
        match p.name(a.path[0].name) {
            "cold" => out.push_str(" cold"),
            "inline" => {
                let mut how = " inlinehint";
                if let crate::ast::AttrInput::List(_, trees) = &a.input {
                    for t in trees {
                        if let TokenTree::Token(t) = t
                            && let Tok::Ident(n) = t.tok
                        {
                            match p.name(n) {
                                "always" => how = " alwaysinline",
                                "never" => how = " noinline",
                                _ => {}
                            }
                        }
                    }
                }
                out.push_str(how);
            }
            _ => {}
        }
    }
    out
}

/// The two arguments that pass location word `w` to a `#[track_caller]` callee (names
/// numbered `k`): the slot constant's address and the line and column bits, as cgen's
/// `names::hot_loc` passes them; the calling fn's own pair when it is `#[track_caller]` too.
fn ll_loc_args(ll: &mut Ll, w: &LocWord, k: usize) -> String {
    match w {
        LocWord::Ltc => {
            let _ = writeln!(ll.body, "  %las{k} = load ptr, ptr %ltc_so\n  %lal{k} = load i64, ptr %ltc_low");
            format!("ptr %las{k}, i64 %lal{k}")
        }
        LocWord::Const(n) => {
            ll.decls.insert("@lust_so_none = external constant i64".to_string());
            format!("ptr @lust_so_none, i64 {n}")
        }
        LocWord::Slot(id, low, _) => {
            ll.decls.insert(format!("@lust_so_{id} = external constant i64"));
            format!("ptr @lust_so_{id}, i64 {low}")
        }
    }
}

/// Emits location word `w` as an LLVM `i64` value (names numbered `k`).
fn ll_loc_value(ll: &mut Ll, w: &LocWord, k: usize) -> String {
    match w {
        LocWord::Ltc => {
            let _ = writeln!(
                ll.body,
                "  %lcs{k} = load ptr, ptr %ltc_so\n  %lcw{k} = load volatile i64, ptr %lcs{k}\n  %lcl{k} = load i64, ptr %ltc_low\n  %lc{k} = or i64 %lcw{k}, %lcl{k}"
            );
            format!("%lc{k}")
        }
        LocWord::Const(n) => n.to_string(),
        LocWord::Slot(id, low, cold) => {
            ll.decls.insert(format!("@lust_so_{id} = external constant i64"));
            let v = if *cold { "volatile " } else { "" };
            let _ = writeln!(ll.body, "  %ls{k} = load {v}i64, ptr @lust_so_{id}\n  %lc{k} = or i64 %ls{k}, {low}");
            format!("%lc{k}")
        }
    }
}

/// A `#[track_caller]` location word as cgen's `loc` writes it in C.
#[derive(Clone, Debug)]
enum LocWord {
    /// The calling fn's own received location (`ltc`: it is `#[track_caller]` too).
    Ltc,
    Const(u64),
    /// `(LUST_SO(lust_so_<id>) | <low>ull)`: the fn's location slot (a constant of the
    /// location unit, already shifted above the line and column bits) or'd with them; read
    /// volatile (`true`, a panic site: kept on the cold path) or plain (`(lust_so_<id> |
    /// <low>ull)`). A `#[track_caller]` call passes the slot's address and the bits instead
    /// (`ll_loc_args`).
    Slot(String, u64, bool),
}

/// Parses cgen's C text for a location word (`FnGen::loc`); None for another form.
fn loc_word(c: &str) -> Option<LocWord> {
    if c == super::names::LTC_WORD {
        return Some(LocWord::Ltc);
    }
    if let Some(n) = c.strip_suffix("ull").or_else(|| c.strip_suffix('u'))
        && let Ok(v) = n.parse::<u64>()
    {
        return Some(LocWord::Const(v));
    }
    let (cold, rest) = match c.strip_prefix("(LUST_SO(lust_so_") {
        Some(r) => (true, r.replacen(") | ", " | ", 1)),
        None => (false, c.strip_prefix("(lust_so_")?.to_string()),
    };
    let (id, low) = rest.split_once(" | ")?;
    let low = low.strip_suffix("ull)")?.parse::<u64>().ok()?;
    id.bytes().all(|b| b.is_ascii_hexdigit()).then(|| LocWord::Slot(id.to_string(), low, cold))
}

/// The C prototype of written fn `f`'s internal ABI entry `fl_<id>` (`pass_of` per
/// parameter; an aggregate result through a leading pointer).
fn ll_proto(p: &Program, f: LocalDefId, id: &str) -> String {
    let info = p.fn_info(f);
    let ret_c = cty(&p.tys, info.ret);
    let rp = pass_of(p, &ret_c);
    let rt = ctype(&ret_c);
    let mut params: Vec<String> = Vec::new();
    if rp == Pass::Mem {
        params.push(format!("{rt} *"));
    }
    for &t in &info.params {
        let ct = cty(&p.tys, t);
        match pass_of(p, &ct) {
            Pass::Skip => {}
            Pass::Scalar(..) => params.push(ctype(&ct)),
            Pass::Bits(n) => params.push(bits_types(n).1.into()),
            Pass::Pair => params.push("uint64_t, uint64_t".into()),
            Pass::Mem => params.push(format!("{}*", ctype(&ct))),
        }
    }
    if crate::check::caller::is_track_caller(p, f) {
        params.push("const uint64_t *, uint64_t".into());
    }
    let fret = match rp {
        Pass::Scalar(..) => rt,
        Pass::Bits(n) => bits_types(n).1.into(),
        Pass::Pair => "ll_pair".into(),
        _ => "void".into(),
    };
    let plist = if params.is_empty() { "void".to_string() } else { params.join(", ") };
    format!("{fret} fl_{id}({plist});\n")
}

/// The LLVM declaration of written fn `f`'s internal ABI entry `fl_<id>`: the types and
/// extension attributes of its definition (`FnGen::ll_define`).
fn ll_decl(p: &Program, f: LocalDefId, id: &str) -> String {
    let info = p.fn_info(f);
    let rt = cty(&p.tys, info.ret);
    let mut params: Vec<String> = Vec::new();
    let ret = match pass_of(p, &rt) {
        Pass::Scalar(t, ext) => {
            if ext.is_empty() {
                t.to_string()
            } else {
                format!("{ext} {t}")
            }
        }
        Pass::Bits(n) => bits_types(n).0.to_string(),
        Pass::Pair => "{ i64, i64 }".into(),
        Pass::Mem => {
            params.push("ptr".into());
            "void".into()
        }
        Pass::Skip => "void".into(),
    };
    for &t in &info.params {
        match pass_of(p, &cty(&p.tys, t)) {
            Pass::Skip => {}
            Pass::Scalar(t, ext) => params.push(if ext.is_empty() { t.to_string() } else { format!("{t} {ext}") }),
            Pass::Bits(n) => params.push(bits_types(n).0.into()),
            Pass::Pair => params.push("i64, i64".into()),
            Pass::Mem => params.push("ptr".into()),
        }
    }
    if crate::check::caller::is_track_caller(p, f) {
        params.push("ptr, i64".into());
    }
    format!("declare {ret} @fl_{id}({})", params.join(", "))
}

/// The line that ends an LLVM unit's plain C prelude (only its wrappers' types): what
/// follows (the C ABI wrappers and trampolines) also compiles after the helpers' C, which
/// declares every type the unit holds (cc.rs `compile_pair`).
pub const BODY_MARK: &str = "/* lust: LLVM unit body */\n";

/// True when `text` holds `word` as a whole C identifier outside literals.
fn contains_word(text: &str, word: &str) -> bool {
    let b = text.as_bytes();
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'"' | b'\'' => i = skip_lit(b, i),
            c if is_ident(c) && (i == 0 || !is_ident(b[i - 1])) => {
                let start = i;
                while i < b.len() && is_ident(b[i]) {
                    i += 1;
                }
                if &text[start..i] == word {
                    return true;
                }
            }
            _ => i += 1,
        }
    }
    false
}

/// The LLVM triple of a Rust target triple (the release targets).
pub fn llvm_triple(triple: &str) -> String {
    match triple {
        "x86_64-unknown-linux-musl" => "x86_64-unknown-linux-musl".into(),
        t => t.replace("-unknown-", "-pc-").replace("-pc-linux", "-unknown-linux"),
    }
}

/// The fn ids (`names::fn_tag`) a fn's helpers call through `fl_<id>` (`ll_fn_call`
/// records each callee's prototype in `externs`).
fn ll_callee_ids(f: &FnOut) -> impl Iterator<Item = &str> {
    f.externs.iter().filter_map(|e| {
        let at = e.find(" fl_")? + 4;
        let id = e.get(at..at + 16)?;
        id.bytes().all(|c| c.is_ascii_hexdigit()).then_some(id)
    })
}

/// Cross-unit inlining for the LLVM backend (`LUST_LL_INLINE=<cost>`, default 25, 0: off;
/// `LUST_LL_INLINE_DEPTH`, default 3): the fns outside `slots` that a fn of the unit calls,
/// directly or through such fns up to the depth, whose cost (`LlFn::cost`: statements and
/// blocks) is at most that. `LUST_LL_INLINE_HINT=<n>` (default 1) multiplies the limit by n
/// for `#[inline]` fns and by 2n for `#[inline(always)]` ones. `LUST_LL_INLINE_TINY=<cost>`
/// and `LUST_LL_INLINE_TINY_DEPTH=<levels>` (default 0: off) follow fns of at most that
/// cost that many levels past the depth (a tiny accessor called from a copy at the last
/// level otherwise stays a call). The unit gets an
/// `available_externally` copy of each (`ll_unit`) and its helpers (`fn_unit_parts`), so the
/// optimizer can inline it, as LTO would; its own unit still emits it. `slot_of` maps a fn
/// id to its slot. The copies come in fn id order (slot order carries a persistent
/// session's history, and its units are a one-shot build's). With a profile (`hot`: the fns
/// whose largest counter is at least `LUST_LL_COPY_MIN`, `cc::pgo::hot_ids`) only those are
/// copied: a copy of a fn the profile saw cold is not inlined, but it costs compile time and
/// recompiles its unit with every change to the fn.
pub fn ll_inline_set(fns: &[FnOut], slots: &[usize], slot_of: &std::collections::HashMap<&str, usize>, hot: Option<&HashSet<u64>>) -> Vec<usize> {
    static LIMITS: std::sync::OnceLock<(usize, usize, usize, usize, usize, usize)> = std::sync::OnceLock::new();
    let (bytes, depth, hint, tiny, tiny_depth, path) = *LIMITS.get_or_init(|| {
        let n = |k: &str, d: usize| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
        // 25: tsgo through the release driver ran ~40% slower without copies and slower with
        // smaller or deeper ones (rel-llvm REPORT.md, step 7).
        let path = n("LUST_LL_INLINE_PATH", 0);
        let extra = n("LUST_LL_INLINE_TINY_DEPTH", 0).max(if path > 0 { 6 } else { 0 });
        (n("LUST_LL_INLINE", 25), n("LUST_LL_INLINE_DEPTH", 3), n("LUST_LL_INLINE_HINT", 1), n("LUST_LL_INLINE_TINY", 0), extra, path)
    });
    if bytes == 0 {
        return Vec::new();
    }
    // The limit for one fn, from the attributes of its `define` line (`source_fn_attrs`).
    let limit = |f: &FnOut| {
        let head = f.ll.lines().find(|l| l.starts_with("define ")).unwrap_or_default();
        let head = head.rsplit_once(')').map_or(head, |(_, attrs)| attrs);
        if head.contains(" noinline") {
            0
        } else if head.contains(" alwaysinline") {
            bytes * hint * 2
        } else if head.contains(" inlinehint") {
            bytes * hint
        } else {
            bytes
        }
    };
    let own: HashSet<usize> = slots.iter().copied().collect();
    let mut picked: Vec<(&str, usize)> = Vec::new();
    let mut seen: HashSet<usize> = HashSet::new();
    // Each frontier fn with the summed cost of the copies on its way from the unit's own fn
    // (`LUST_LL_INLINE_PATH=<budget>`: past the depth, a callee within the limit is still
    // copied while that sum stays within the budget, up to six more levels).
    let mut frontier: Vec<(usize, usize)> = slots.iter().map(|&s| (s, 0)).collect();
    for level in 0..depth + tiny_depth {
        let mut next = Vec::new();
        for &(s, sum) in &frontier {
            for id in ll_callee_ids(&fns[s]) {
                let Some(&g) = slot_of.get(id) else { continue };
                let f = &fns[g];
                let cost = f.ll_cost as usize;
                let ok = if level < depth { cost <= limit(f) } else { cost <= tiny || (path > 0 && cost <= limit(f) && sum + cost <= path) };
                if own.contains(&g) || f.ll.is_empty() || !ok || hot.is_some_and(|h| u64::from_str_radix(id, 16).is_ok_and(|n| !h.contains(&n))) || !seen.insert(g) {
                    continue;
                }
                picked.push((id, g));
                next.push((g, sum + cost));
            }
        }
        frontier = next;
    }
    picked.sort_unstable();
    picked.into_iter().map(|(_, g)| g).collect()
}

/// The fn ids whose C ABI wrapper (`f_<id>`) or trampoline (`tramp_<id>`) a C text names, as
/// `(wrappers, trampolines)`. An LLVM fn's own C (its `code`) is the only text that has to
/// define them; a unit keeps a wrapper or trampoline only when some text names it
/// (`c_body`): most fns are called through `fl_<id>` only.
#[derive(Default, Clone)]
pub struct CRefs {
    pub wrappers: HashSet<u64>,
    pub tramps: HashSet<u64>,
}

impl CRefs {
    /// Adds the `f_<id>` and `tramp_<id>` names in `text` (16 hex digits, whole words).
    pub fn scan(&mut self, text: &str) {
        let b = text.as_bytes();
        let word = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
        for (pat, tramp) in [("f_", false), ("tramp_", true)] {
            for (at, _) in text.match_indices(pat) {
                if at > 0 && word(b[at - 1]) {
                    continue;
                }
                let h = at + pat.len();
                let Some(hex) = text.get(h..h + 16) else { continue };
                if b.get(h + 16).is_some_and(|&c| word(c)) {
                    continue;
                }
                let Ok(id) = u64::from_str_radix(hex, 16) else { continue };
                if tramp { self.tramps.insert(id) } else { self.wrappers.insert(id) };
            }
        }
    }

    /// Adds every id `other` holds.
    pub fn extend(&mut self, other: &CRefs) {
        self.wrappers.extend(&other.wrappers);
        self.tramps.extend(&other.tramps);
    }

    /// The C of LLVM fn `id`'s `code` this build needs: its wrapper when some text calls it
    /// or its trampoline is needed (the trampoline calls the wrapper), the trampoline when
    /// some text names it, the `fl_` prototype with the wrapper. Empty when neither.
    pub fn c_body(&self, code: &str, id: &str) -> String {
        let Ok(n) = u64::from_str_radix(id, 16) else { return code.to_string() };
        let tramp = self.tramps.contains(&n);
        let wrapper = tramp || self.wrappers.contains(&n);
        if !wrapper {
            return String::new();
        }
        let t = format!(" tramp_{id}(");
        let mut out = String::new();
        for line in code.lines().filter(|l| tramp || !l.contains(&t)) {
            out.push_str(line);
            out.push('\n');
        }
        out
    }
}

/// Each LLVM fn's C ABI wrapper (`ll_wrapper`: its `fl_<id>` prototype, then `f_<id>`), by fn
/// id, read from the fns' C. A C text that calls the fn through `f_<id>` gets the wrapper as a
/// C99 inline definition in place of its prototype (`adapt`), as release C's inline copies
/// are (`fn_unit_parts`): clang inlines it, so the call goes straight to `fl_<id>`. The fn's
/// own unit keeps the external wrapper while some text names it (`CRefs`), for its address
/// and for calls that stay calls. `LUST_LL_ADAPT=0`: off (measurement).
pub struct Adapters {
    by_id: HashMap<u64, (String, String)>,
}

impl Adapters {
    /// The wrappers of the LLVM fns in `fns`; None when off.
    pub fn new(fns: &[FnOut]) -> Option<Adapters> {
        if std::env::var("LUST_LL_ADAPT").is_ok_and(|v| v == "0") {
            return None;
        }
        let mut by_id = HashMap::new();
        for f in fns.iter().filter(|f| !f.ll.is_empty()) {
            // `code`: the fn's comment line, the `fl_` prototype, the wrapper, the trampoline.
            let code = f.code_text();
            let mut lines = code.lines().skip(1);
            let (Some(proto), Some(def)) = (lines.next(), lines.next()) else { continue };
            let Some(at) = proto.find(" fl_") else { continue };
            let Some(id) = proto.get(at + 4..at + 20).and_then(|h| u64::from_str_radix(h, 16).ok()) else { continue };
            if proto.ends_with(");") && def.ends_with(" }") && def.contains(&format!("f_{id:016x}(")) {
                by_id.insert(id, (proto.to_string(), def.to_string()));
            }
        }
        Some(Adapters { by_id })
    }

    /// `text` with each line that is the prototype of a wrapper here replaced by the wrapper's
    /// `fl_<id>` prototype and its inline definition (the first time; a later one by an inline
    /// declaration), `ll_pair`'s typedef first when the text needs it and has none. A fn `own`
    /// holds is left alone (the text defines its external wrapper). None: no change.
    pub fn adapt(&self, text: &str, own: impl Fn(u64) -> bool) -> Option<String> {
        let b = text.as_bytes();
        let mut out: Option<String> = None;
        let mut last = 0;
        let mut done: HashSet<u64> = HashSet::new();
        let mut pair: Option<bool> = None;
        for (at, _) in text.match_indices("f_") {
            // A prototype names the fn after its return type: ` f_` or `*f_`.
            if at == 0 || !matches!(b[at - 1], b' ' | b'*') || at < last || b.get(at + 18) != Some(&b'(') {
                continue;
            }
            let Some(id) = text.get(at + 2..at + 18).and_then(|h| u64::from_str_radix(h, 16).ok()) else { continue };
            let Some((proto, def)) = self.by_id.get(&id) else { continue };
            let start = text[..at].rfind('\n').map_or(0, |k| k + 1);
            let end = text[at..].find('\n').map_or(text.len(), |k| at + k);
            let line = &text[start..end];
            let head = def.split_once(" {").map_or(def.as_str(), |(h, _)| h);
            if line.strip_suffix(';') != Some(head) || own(id) {
                continue;
            }
            let o = out.get_or_insert_with(|| String::with_capacity(text.len() + 4096));
            o.push_str(&text[last..start]);
            if done.insert(id) {
                if proto.starts_with("ll_pair ") && !*pair.get_or_insert_with(|| text.contains(PAIR_TYPEDEF)) {
                    o.push_str(PAIR_TYPEDEF);
                    pair = Some(true);
                }
                let _ = write!(o, "{proto}\ninline {def}");
            } else {
                let _ = write!(o, "inline {line}");
            }
            last = end;
        }
        out.map(|mut o| {
            o.push_str(&text[last..]);
            o
        })
    }
}

/// The `.ll` text of one release fn unit: the declarations its fns name (each once) and
/// their definitions, then an `available_externally` copy of each fn in `inl`
/// (`ll_inline_set`). Empty when no fn of the unit has LLVM IR.
pub fn ll_unit(fns: &[FnOut], slots: &[usize], inl: &[usize], triple: &str) -> String {
    if slots.iter().all(|&s| fns[s].ll.is_empty()) {
        return String::new();
    }
    // No target line: clang compiles the IR for its own target, as it does the C halves.
    let _ = triple;
    // One source name for every unit: PGO names an internal fn (the helpers, once linked)
    // `<source name>;<fn>`, and a unit's own name follows its members, so a merge that moves
    // one fn would rename the records of every helper in the unit (`pgo::split` owns these
    // records by fn name).
    let mut out = format!("; lust release LLVM IR unit\nsource_filename = \"{}\"\n\n", crate::cc::pgo::STATIC_FILE);
    let mut decls: BTreeSet<&str> = BTreeSet::new();
    for &s in slots.iter().chain(inl) {
        decls.extend(fns[s].ll_decls.iter().map(String::as_str));
    }
    // A fn the unit defines (its own, or an inline copy) is not declared again.
    let defined: HashSet<&str> = slots
        .iter()
        .chain(inl)
        .filter_map(|&s| {
            let d = &fns[s].ll;
            let at = d.find(" @fl_")? + 2;
            d.get(at..at + 19)
        })
        .collect();
    for d in decls {
        if d.starts_with("declare ")
            && let Some(at) = d.find(" @fl_")
            && d.get(at + 2..at + 21).is_some_and(|n| defined.contains(n))
        {
            continue;
        }
        out.push_str(d);
        out.push('\n');
    }
    out.push('\n');
    for &s in slots {
        out.push_str(&fns[s].ll);
    }
    // `LUST_LL_COPY=internal` (measurement): copies are the unit's own internal fns instead,
    // as release C's static copies are, so a training build counts each unit's copy in its
    // callers' context (an available_externally copy has no counters of its own).
    static INTERNAL: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let linkage = if *INTERNAL.get_or_init(|| std::env::var("LUST_LL_COPY").is_ok_and(|v| v == "internal")) { "internal" } else { "available_externally" };
    for &s in inl {
        copy_text(&mut out, &fns[s].ll, linkage);
    }
    out
}

/// Appends fn IR `ll` as an inline copy: `linkage` on its define line, which also leaves out
/// its `dereferenceable(<bytes>)` attributes. Those follow the sizes of the types its params
/// and result point at, which change with any field of them; with them every unit that holds
/// the copy would recompile. Inlining drops them, and a copy is only ever inlined.
fn copy_text(out: &mut String, ll: &str, linkage: &str) {
    let Some(at) = ll.find("\ndefine ") else {
        out.push_str(ll);
        return;
    };
    let end = ll[at + 1..].find('\n').map_or(ll.len(), |k| at + 1 + k);
    out.push_str(&ll[..at]);
    let _ = write!(out, "\ndefine {linkage} ");
    let mut rest = &ll[at + 8..end];
    while let Some(i) = rest.find(" dereferenceable") {
        out.push_str(&rest[..i]);
        rest = &rest[i + 1..];
        rest = rest.find(')').map_or("", |k| &rest[k + 1..]);
    }
    out.push_str(rest);
    out.push_str(&ll[end..]);
}

#[cfg(test)]
mod tests {
    use super::{Adapters, CRefs, FnOut};

    /// A C text that names an LLVM fn's wrapper by its prototype gets the wrapper inline (once,
    /// with `ll_pair` when its result needs it); a fn the text defines keeps its prototype.
    #[test]
    fn a_wrapper_prototype_becomes_an_inline_wrapper() {
        let (a, b) = ("00000000000000aa", "00000000000000bb");
        let fns = [
            FnOut {
                ll: "define".into(),
                text: crate::cgen::CText::Plain(format!(
                    "/* m::a */\nll_pair fl_{a}(uint64_t);\nP f_{a}(uint64_t p1) {{ ll_pair rb = fl_{a}(p1); P r; memcpy(&r, &rb, 16); return r; }}\nP tramp_{a}(uint64_t p1) {{ return f_{a}(p1); }}\n"
                )),
                ..Default::default()
            },
            FnOut {
                ll: "define".into(),
                text: crate::cgen::CText::Plain(format!("/* m::b */\nvoid fl_{b}(void);\nvoid f_{b}(void) {{ fl_{b}(); }}\n")),
                ..Default::default()
            },
        ];
        let ad = Adapters::new(&fns).unwrap();
        let text = format!("int x;\nP f_{a}(uint64_t p1);\nvoid f_{b}(void);\nP f_{a}(uint64_t p1);\nvoid g(void) {{ f_{b}(); }}\n");
        let out = ad.adapt(&text, |id| id == 0xbb).unwrap();
        let want = format!(
            "int x;\n{}ll_pair fl_{a}(uint64_t);\ninline P f_{a}(uint64_t p1) {{ ll_pair rb = fl_{a}(p1); P r; memcpy(&r, &rb, 16); return r; }}\nvoid f_{b}(void);\ninline P f_{a}(uint64_t p1);\nvoid g(void) {{ f_{b}(); }}\n",
            super::PAIR_TYPEDEF
        );
        assert_eq!(out, want);
        assert!(ad.adapt("void g(void) { f_00000000000000aa(1); }\n", |_| false).is_none(), "a call is not a prototype");
    }

    /// An inline copy is `available_externally` and has no dereferenceable bytes.
    #[test]
    fn a_copy_leaves_out_its_dereferenceable_bytes() {
        let ll = "\n; cost 2\n; deref\ndefine nonnull align 8 dereferenceable(1328) ptr @fl_00000000000000ab(ptr nonnull align 8 dereferenceable_or_null(16) noundef %p1) uwtable {\n  %v1 = getelementptr inbounds i8, ptr %p1, i64 8\n  ret ptr %v1\n}\n";
        let mut out = String::new();
        super::copy_text(&mut out, ll, "available_externally");
        let want = ll.replace("define nonnull align 8 dereferenceable(1328) ptr", "define available_externally nonnull align 8 ptr").replace(" dereferenceable_or_null(16)", "");
        assert_eq!(out, want);
    }

    /// A unit keeps an LLVM fn's wrapper only when some text names it, and its trampoline only
    /// when some text names that (the wrapper then too: the trampoline calls it).
    #[test]
    fn a_unit_keeps_only_the_named_wrappers_and_trampolines() {
        let id = "00000000000000ab";
        let code = format!("/* m::f */\nuint8_t fl_{id}(uint64_t);\nuint8_t f_{id}(uint64_t p1) {{ return fl_{id}(p1); }}\nuint8_t tramp_{id}(uint64_t p1) {{ return f_{id}(p1); }}\n");
        let mut r = CRefs::default();
        r.scan(&format!("x = fl_{id}(1); y = lust_f_{id}(2); z = f_{id}x(3); w = drop_f_{id};"));
        assert_eq!(r.c_body(&code, id), "", "fl_, a longer word and a prefix are not names of the wrapper");
        r.scan(&format!("v = f_{id}(4);"));
        let w = r.c_body(&code, id);
        assert!(w.contains(&format!(" f_{id}(")) && !w.contains("tramp_"), "{w}");
        let mut t = CRefs::default();
        t.scan(&format!("p = (void*)tramp_{id};"));
        assert_eq!(t.c_body(&code, id), code);
    }
}
