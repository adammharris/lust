// Slice and Vec methods of TRIAGE R4 (tf-small-a): `[u8]::eq_ignore_ascii_case`
// and `is_ascii`, `[T]::rotate_left`/`rotate_right` and `partition_point`,
// and `Vec::extend_from_within`, `dedup_by`, `dedup_by_key` (`resize_with`
// expands in lower/iter.rs, which calls any callable).
// Each follows core/alloc 1.99: the same closure calls in the same order,
// the same drops at the same moments, core's panics at core's sites, and
// the Vec growth of `reserve`.

use super::*;

/// `std_loc` file index of core/src/slice/mod.rs (runtime/panic.c
/// `lust_std_files`).
const SLICE_MOD_RS: u64 = 14;

/// `std_loc` file index of core/src/str/mod.rs (`stdloc::STD_FILES`).
const STR_MOD_RS: u64 = 32;

/// The (element type, data pointer, length) C expressions of a slice
/// operand in any receiver form: `&Vec<T>`, `&[T]` (the fat value),
/// `&&[T]`, `&[T; N]`, or a by-value array.
fn slice_parts(t: &CTy, val: &str) -> (CTy, String, String) {
    match t {
        CTy::Ref(inner) => match &**inner {
            CTy::Vec(e) => ((**e).clone(), format!("(({}*){val}->ptr)", ctype(e)), format!("{val}->len")),
            CTy::Slice(e) => ((**e).clone(), format!("{val}->ptr"), format!("{val}->len")),
            CTy::Array(e, n) => ((**e).clone(), format!("{val}->v"), format!("((uint64_t){n})")),
            _ => unreachable!(),
        },
        CTy::Slice(e) => ((**e).clone(), format!("{val}.ptr"), format!("{val}.len")),
        CTy::Array(e, n) => ((**e).clone(), format!("{val}.v"), format!("((uint64_t){n})")),
        _ => unreachable!(),
    }
}

impl FnGen<'_, '_> {
    /// `SliceSplitAt` and `SliceSplitEnd` (core's `split_at` family) into
    /// their tuple or `Option` of a tuple, and the `SliceStrip` and
    /// `SliceTrimAscii` subslices; None for any other call.
    pub(super) fn slice_split_builtin(&mut self, b: Builtin, ops: &[Operand], dest: &CTy, loc: &str, post: &mut Vec<String>) -> Option<String> {
        if let Builtin::StrSplitAt(checked) = b {
            return Some(self.str_split_at(checked, ops, dest, loc, post));
        }
        if !matches!(b, Builtin::SliceSplitAt(_) | Builtin::SliceSplitEnd(_) | Builtin::SliceStrip(_) | Builtin::SliceTrimAscii(_) | Builtin::SliceAsChunks(_)) {
            return None;
        }
        let (v, vt) = self.operand(&ops[0], loc, post);
        let (e, ptr, len) = slice_parts(&vt, &v);
        let st = ctype(&CTy::Slice(Box::new(e.clone())));
        self.note_held(dest);
        let dc = ctype(dest);
        let (t, p, n) = (self.tmp(), self.tmp(), self.tmp());
        let _ = writeln!(self.out, "    {} *{p} = {ptr}; uint64_t {n} = {len};", ctype(&e));
        match b {
            Builtin::SliceSplitAt(checked) => {
                let (mid, _) = self.operand(&ops[1], loc, post);
                let m = self.tmp();
                let _ = writeln!(self.out, "    uint64_t {m} = {mid};");
                let pair_ty = match dest {
                    CTy::Option(pt) if checked => ctype(pt),
                    _ => dc.clone(),
                };
                let pair = format!("(({pair_ty}){{ (({st}){{ {p}, {m} }}), (({st}){{ {p} + {m}, {n} - {m} }}) }})");
                if checked {
                    let (some, none) = (self.make_variant(dest, 1, &[pair]), self.make_variant(dest, 0, &[]));
                    let _ = writeln!(self.out, "    {dc} {t} = {m} <= {n} ? {some} : {none};");
                } else {
                    let _ = writeln!(self.out, "    if ({m} > {n}) lust_panic_cstr(\"mid > len\", {loc});\n    {dc} {t} = {pair};");
                }
            }
            Builtin::SliceSplitEnd(last) => {
                let CTy::Option(pt) = dest else { unreachable!("split_first returns an Option") };
                let pair = if last {
                    format!("(({}){{ &{p}[{n} - 1], (({st}){{ {p}, {n} - 1 }}) }})", ctype(pt))
                } else {
                    format!("(({}){{ &{p}[0], (({st}){{ {p} + 1, {n} - 1 }}) }})", ctype(pt))
                };
                let (some, none) = (self.make_variant(dest, 1, &[pair]), self.make_variant(dest, 0, &[]));
                let _ = writeln!(self.out, "    {dc} {t} = {n} > 0 ? {some} : {none};");
            }
            // core: `head == prefix` on `split_at(n)` (or `tail == suffix`
            // on `split_at(len - n)`): the receiver's element on the left,
            // front to back, stopping at the first unequal pair.
            Builtin::SliceStrip(suffix) => {
                let (pv, pt) = self.operand(&ops[1], loc, post);
                let (_, pptr, plen) = slice_parts(&pt, &pv);
                let (pp, pn, off, i, ok) = (self.tmp(), self.tmp(), self.tmp(), self.tmp(), self.tmp());
                let et = ctype(&e);
                let eq = self.eq_expr(&e, &format!("(&{p}[{off} + {i}])"), &format!("(&{pp}[{i}])"));
                let off_expr = if suffix { format!("{n} - {pn}") } else { "0".to_string() };
                let rest = if suffix { format!("(({st}){{ {p}, {n} - {pn} }})") } else { format!("(({st}){{ {p} + {pn}, {n} - {pn} }})") };
                let _ = writeln!(
                    self.out,
                    "    {et} *{pp} = {pptr}; uint64_t {pn} = {plen};\n    uint8_t {ok} = {pn} <= {n}; uint64_t {off} = {ok} ? {off_expr} : 0;\n    for (uint64_t {i} = 0; {ok} && {i} < {pn}; {i}++) if (!({eq})) {{ {ok} = 0; break; }}"
                );
                let (some, none) = (self.make_variant(dest, 1, &[rest]), self.make_variant(dest, 0, &[]));
                let _ = writeln!(self.out, "    {dc} {t} = {ok} ? {some} : {none};");
            }
            // `u8::is_ascii_whitespace`: `\t`, `\n`, `\x0C`, `\r`, and space.
            Builtin::SliceTrimAscii(which) => {
                let ws = |x: &str| format!("({x} == 9 || {x} == 10 || {x} == 12 || {x} == 13 || {x} == 32)");
                if which != 1 {
                    let _ = writeln!(self.out, "    while ({n} > 0 && {}) {{ {p}++; {n}--; }}", ws(&format!("{p}[0]")));
                }
                if which != 0 {
                    let _ = writeln!(self.out, "    while ({n} > 0 && {}) {n}--;", ws(&format!("{p}[{n} - 1]")));
                }
                let _ = writeln!(self.out, "    {dc} {t} = (({st}){{ {p}, {n} }});");
            }
            // core's `as_chunks` (`len / N` arrays, then the rest) and
            // `as_rchunks` (the rest, then the arrays); `N` of 0 is
            // core's assert, at the caller (`#[track_caller]`).
            Builtin::SliceAsChunks(rev) => {
                let CTy::Tuple(parts) = dest else { unreachable!("as_chunks returns a pair") };
                let arr = parts.iter().find_map(|x| match x {
                    CTy::Slice(a) if matches!(**a, CTy::Array(..)) => Some((**a).clone()),
                    _ => None,
                });
                let Some(arr @ CTy::Array(_, cn)) = arr else { unreachable!("as_chunks returns a slice of arrays") };
                let at = ctype(&CTy::Slice(Box::new(arr.clone())));
                let ac = ctype(&arr);
                if cn == 0 {
                    let _ = writeln!(self.out, "    lust_panic_cstr(\"chunk size must be non-zero\", {loc});");
                }
                let q = self.tmp();
                let cn = cn.max(1);
                let _ = writeln!(self.out, "    uint64_t {q} = {n} / {cn};");
                let (chunks, rest) = if rev {
                    (format!("(({at}){{ ({ac}*)({p} + ({n} - {q} * {cn})), {q} }})"), format!("(({st}){{ {p}, {n} - {q} * {cn} }})"))
                } else {
                    (format!("(({at}){{ ({ac}*){p}, {q} }})"), format!("(({st}){{ {p} + {q} * {cn}, {n} - {q} * {cn} }})"))
                };
                let pair = if rev { format!("{rest}, {chunks}") } else { format!("{chunks}, {rest}") };
                let _ = writeln!(self.out, "    {dc} {t} = (({dc}){{ {pair} }});");
            }
            _ => unreachable!(),
        }
        Some(t)
    }

    /// `str::split_at(mid)` and `split_at_checked(mid)`. The unchecked form
    /// fails as core's `slice_error_fail(self, 0, mid)` does, with its text
    /// and at its site in core/src/str/mod.rs; the checked one gives None
    /// for a `mid` past the end or inside a char.
    fn str_split_at(&mut self, checked: bool, ops: &[Operand], dest: &CTy, loc: &str, post: &mut Vec<String>) -> String {
        let (v, vt) = self.operand(&ops[0], loc, post);
        let sv = str_of(&v, &vt);
        let (mid, _) = self.operand(&ops[1], loc, post);
        self.note_held(dest);
        let dc = ctype(dest);
        let (t, sa, m) = (self.tmp(), self.tmp(), self.tmp());
        let _ = writeln!(self.out, "    lust_str {sa} = {sv}; uint64_t {m} = {mid};");
        let pair_ty = match dest {
            CTy::Option(pt) if checked => ctype(pt),
            _ => dc.clone(),
        };
        let pair = format!("(({pair_ty}){{ ((lust_str){{ {sa}.ptr, {m} }}), ((lust_str){{ {sa}.ptr + {m}, {sa}.len - {m} }}) }})");
        if checked {
            let (some, none) = (self.make_variant(dest, 1, &[pair]), self.make_variant(dest, 0, &[]));
            let ok = format!("({m} == {sa}.len || ({m} < {sa}.len && ({sa}.ptr[{m}] & 0xC0) != 0x80))");
            let _ = writeln!(self.out, "    {dc} {t} = {ok} ? {some} : {none};");
        } else {
            let at = std_loc(STR_MOD_RS, 862, 21);
            let _ = writeln!(self.out, "    (void)lust_str_range({sa}.ptr, 0, {m}, 0, {sa}.len, {at});\n    {dc} {t} = {pair};");
        }
        t
    }

    /// The R4 builtins; None for any other call.
    pub(super) fn slices_builtin(&mut self, b: Builtin, ops: &[Operand], vals: &[String], tys: &[CTy]) -> Option<String> {
        use Builtin as B;
        let slice_like = slice_parts;
        let vec_elem = |t: &CTy| -> CTy {
            let CTy::Ref(v) = t else { unreachable!() };
            let CTy::Vec(e) = &**v else { unreachable!() };
            (**e).clone()
        };
        Some(match b {
            B::SliceEqIgnoreAsciiCase => {
                let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (_, optr, olen) = slice_like(&tys[1], &vals[1]);
                let t = self.tmp();
                let _ = writeln!(self.out, "    uint8_t {t} = lust_bytes_eq_ignore_ascii_case({ptr}, {len}, {optr}, {olen});");
                t
            }
            // The runtime's word-at-a-time test (str::is_ascii's), not a byte loop here.
            B::SliceIsAscii => {
                let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                format!("lust_bytes_is_ascii((const uint8_t *){ptr}, {len})")
            }
            B::SliceToAsciiCase(upper) => {
                let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (t, i) = (self.tmp(), self.tmp());
                let (lo, hi, d) = if upper { ('a', 'z', "-= 32") } else { ('A', 'Z', "+= 32") };
                let _ = writeln!(
                    self.out,
                    "    lust_Vec {t} = lust_vec_with_capacity({len}, 1, 1);\n    memcpy({t}.ptr, {ptr}, {len});\n    {t}.len = {len};\n    for (uint64_t {i} = 0; {i} < {t}.len; {i}++) if (((uint8_t*){t}.ptr)[{i}] >= '{lo}' && ((uint8_t*){t}.ptr)[{i}] <= '{hi}') ((uint8_t*){t}.ptr)[{i}] {d};"
                );
                t
            }
            B::SliceMakeAsciiCase(upper) => {
                let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (q, i) = (self.tmp(), self.tmp());
                let (lo, hi, d) = if upper { ('a', 'z', "-= 32") } else { ('A', 'Z', "+= 32") };
                let _ = writeln!(
                    self.out,
                    "    uint8_t *{q} = (uint8_t*){ptr};\n    for (uint64_t {i} = 0; {i} < {len}; {i}++) if ({q}[{i}] >= '{lo}' && {q}[{i}] <= '{hi}') {q}[{i}] {d};"
                );
                "((lust_Unit){})".into()
            }
            // alloc's `checked_mul(n).expect("capacity overflow")`, then a
            // byte copy per round (`T: Copy`).
            B::SliceRepeat => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let et = ctype(&e);
                format!("lust_slice_repeat({ptr}, {len}, {}, sizeof({et}), _Alignof({et}))", vals[1])
            }
            B::SliceRotateLeft | B::SliceRotateRight => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let n = &vals[1];
                let (cond, line) = if b == B::SliceRotateLeft { ("mid <= self.len()", 3904) } else { ("k <= self.len()", 3950) };
                let at = std_loc(SLICE_MOD_RS, line, 9);
                let mid = if b == B::SliceRotateLeft { n.clone() } else { format!("{len} - {n}") };
                let _ = writeln!(
                    self.out,
                    "    if (!({n} <= {len})) lust_panic_cstr(\"assertion failed: {cond}\", {at});\n    lust_slice_rotate_left({ptr}, {len}, sizeof({}), {mid});",
                    ctype(&e)
                );
                "((lust_Unit){})".into()
            }
            B::SlicePartitionPoint => {
                // core: `binary_search_by(|x| if pred(x) { Less } else
                // { Greater }).unwrap_or_else(|i| i)`; the comparator
                // never answers Equal, so the search ends in Err(i).
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let size = c_size_align(self.p, &e).0;
                let f = self.adapter_callee(&ops[1]);
                let adapter = self.partition_adapter(&e, &f);
                let (c, r) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {} {c} = {};", ctype(&tys[1]), vals[1]);
                let _ = writeln!(self.out, "    int64_t {r} = lust_binary_search({ptr}, {len}, {size}, (void*)&{c}, {adapter});");
                if needs_drop_c(self.p, &tys[1]) {
                    self.want(Glue::Drop, &tys[1]);
                    let _ = writeln!(self.out, "    drop_{}(&{c});", mangle(&tys[1]));
                }
                format!("((uint64_t)(-{r} - 1))")
            }
            B::VecExtendFromWithin => {
                // `slice::range` (core's index.rs panics), `reserve`,
                // then each element of the range cloned and pushed in
                // order (the length grows per element, as alloc's
                // `SetLenOnDrop` keeps it).
                let e = vec_elem(&tys[0]);
                let et = ctype(&e);
                let vv = &vals[0];
                let (s, en, i) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {s}, {en};\n    lust_range_check({vv}->len, {}, {}, {}, {}, &{s}, &{en});\n    lust_vec_reserve({vv}, {en} - {s}, sizeof({et}), _Alignof({et}));",
                    vals[1], vals[2], vals[3], vals[4]
                );
                if is_copy_c(self.p, &e) {
                    // std's TrivialClone path: one byte copy past the end,
                    // free for zero-sized elements.
                    let _ = writeln!(self.out, "    memcpy(({et}*){vv}->ptr + {vv}->len, ({et}*){vv}->ptr + {s}, ({en} - {s}) * sizeof({et}));\n    {vv}->len += {en} - {s};");
                } else {
                    self.want(Glue::Clone, &e);
                    let elem = format!("(({et}*){vv}->ptr)[{i}]");
                    let _ = writeln!(
                        self.out,
                        "    for (uint64_t {i} = {s}; {i} < {en}; {i}++) {{ {et} c_ = clone_{}(&{elem}); (({et}*){vv}->ptr)[{vv}->len++] = c_; }}",
                        mangle(&e)
                    );
                }
                "((lust_Unit){})".into()
            }
            B::VecDedupBy | B::VecDedupByKey => {
                // `VecDedup`'s loop with the closure as the test:
                // `same_bucket(&mut current, &mut previous_kept)`; for
                // `dedup_by_key`, `key(a) == key(b)` with the keys
                // dropped in reverse order, as the temporaries are.
                let e = vec_elem(&tys[0]);
                let et = ctype(&e);
                let vv = &vals[0];
                let f = self.adapter_callee(&ops[1]);
                let (c, w, r) = (self.tmp(), self.tmp(), self.tmp());
                let mut body = String::new();
                // panic=unwind: a panic in the closure (or a key's `==`)
                // keeps the element it saw; one in a duplicate's drop
                // counts that one removed. The unchecked rest moves down
                // behind the kept ones (std's `FillGapOnDrop`).
                // Unwind tables (`zc`): cleanup variables do the same as the panic
                // unwinds (the keys, then the gap fill, then the env).
                let zc = self.p.unwind_tables;
                let unw = self.p.unwind && !zc;
                let mine = "lust_unw_pending && lust_unw_mine()";
                let rg = if zc { self.tmp() } else { String::new() };
                if zc {
                    body.push_str("    {\n");
                }
                let _ = writeln!(body, "    {} {c} = {};", ctype(&tys[1]), vals[1]);
                let mut env_disarm = String::new();
                if zc {
                    let (gd, gdis) = self.zc_guard(&c, &tys[1]);
                    env_disarm = gdis;
                    body.push_str(&format!("   {gd}\n"));
                }
                let _ = writeln!(body, "    if ({vv}->len > 1) {{\n      uint64_t {w} = 1, {r} = 1;");
                if zc {
                    let _ = writeln!(
                        body,
                        "      struct lust_retain_guard {rg} __attribute__((cleanup(lust_retain_guard_end))) = {{ (lust_Vec *){vv}, &{r}, &{w}, sizeof({et}), 1 }};"
                    );
                }
                let _ = writeln!(body, "      for (; {r} < {vv}->len; {r}++) {{");
                let cur = format!("(&(({et}*){vv}->ptr)[{r}])");
                let prev = format!("(&(({et}*){vv}->ptr)[{w} - 1])");
                let same = if b == B::VecDedupBy {
                    let same = self.adapter_call_c(&mut body, &f, &format!("&{c}"), &[cur, prev]).0;
                    if unw {
                        let _ = writeln!(body, "      if ({mine}) break;");
                    }
                    same
                } else {
                    let (ka, kt) = self.adapter_call_c(&mut body, &f, &format!("&{c}"), &[cur]);
                    if unw {
                        let _ = writeln!(body, "      if ({mine}) break;");
                    }
                    let (ga, gadis) = if zc { self.zc_guard(&ka, &kt) } else { (String::new(), String::new()) };
                    body.push_str(&ga);
                    let (kb, _) = self.adapter_call_c(&mut body, &f, &format!("&{c}"), &[prev]);
                    let (gb, gbdis) = if zc { self.zc_guard(&kb, &kt) } else { (String::new(), String::new()) };
                    body.push_str(&gb);
                    if unw {
                        let drop_ka = self.unw_cleanup_drop(&ka, &kt);
                        let _ = writeln!(body, "      if ({mine}) {{{drop_ka} break; }}");
                    }
                    let eq = self.eq_expr(&kt, &format!("(&{ka})"), &format!("(&{kb})"));
                    let s = self.tmp();
                    let _ = writeln!(body, "      uint8_t {s} = {eq};");
                    if unw {
                        // `key(a) == key(b)`: both keys drop as the
                        // closure unwinds, the later one first.
                        let (drop_kb, drop_ka) = (self.unw_cleanup_drop(&kb, &kt), self.unw_cleanup_drop(&ka, &kt));
                        let _ = writeln!(body, "      if ({mine}) {{{drop_kb}{drop_ka} break; }}");
                    }
                    if needs_drop_c(self.p, &kt) {
                        self.want(Glue::Drop, &kt);
                        let _ = writeln!(body, "     {gbdis}{gadis} drop_{0}(&{kb}); drop_{0}(&{ka});", mangle(&kt));
                    }
                    s
                };
                let drop_dup = if needs_drop_c(self.p, &e) {
                    self.want(Glue::Drop, &e);
                    if zc {
                        // The duplicate counts removed while its drop runs.
                        format!("{r}++; drop_{}(&(({et}*){vv}->ptr)[{r} - 1]); {r}--; ", mangle(&e))
                    } else {
                        let after = if unw { format!(" if ({mine}) {{ {r}++; break; }}") } else { String::new() };
                        format!("(void)(drop_{}(&(({et}*){vv}->ptr)[{r}]), 0);{after} ", mangle(&e))
                    }
                } else {
                    String::new()
                };
                let _ = writeln!(
                    body,
                    "        if ({same}) {{ {drop_dup}}} else {{ if ({w} != {r}) (({et}*){vv}->ptr)[{w}] = (({et}*){vv}->ptr)[{r}]; {w}++; }}\n      }}"
                );
                if unw {
                    let n = self.tmp();
                    let _ = writeln!(body, "      uint64_t {n} = {vv}->len - {r}; {vv}->len = {w} + {n};");
                    let _ = writeln!(body, "      if ({n} && {w} != {r}) lust_memmove((({et}*){vv}->ptr) + {w}, (({et}*){vv}->ptr) + {r}, {n} * sizeof({et}));\n    }}");
                } else if zc {
                    let _ = writeln!(body, "      {rg}.armed = 0; {vv}->len = {w};\n    }}");
                } else {
                    let _ = writeln!(body, "      {vv}->len = {w};\n    }}");
                }
                if needs_drop_c(self.p, &tys[1]) {
                    self.want(Glue::Drop, &tys[1]);
                    if zc {
                        let _ = writeln!(body, "   {env_disarm} drop_{}(&{c});", mangle(&tys[1]));
                    } else if unw {
                        let drop_c = self.unw_cleanup_drop(&c, &tys[1]);
                        let _ = writeln!(body, "    if ({mine}) {{{drop_c} }} else drop_{}(&{c});", mangle(&tys[1]));
                    } else {
                        let _ = writeln!(body, "    drop_{}(&{c});", mangle(&tys[1]));
                    }
                }
                if zc {
                    body.push_str("    }\n");
                }
                let _ = write!(self.out, "{body}");
                "((lust_Unit){})".into()
            }
            // The `splice` steps on its `vec::Drain` (lower/iter/splice.rs).
            B::SpliceBegin | B::SpliceReserve | B::SpliceGap | B::SplicePut | B::SpliceMoveTail => {
                let CTy::Ref(dt) = &tys[0] else { unreachable!() };
                let CTy::VecDrain(e) = &**dt else { unreachable!() };
                let et = ctype(e);
                let (p, dv) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    lust_VecDrain *{p} = {}; lust_Vec *{dv} = (lust_Vec *){p}->vec;", vals[0]);
                match b {
                    // `drain.by_ref().for_each(drop)`; the tail length.
                    B::SpliceBegin => {
                        if needs_drop_c(self.p, e) {
                            self.want(Glue::Drop, e);
                            let i = self.tmp();
                            let _ = writeln!(self.out, "    for (uint64_t {i} = {p}->front; {i} < {p}->back; {i}++) drop_{}(&(({et}*){dv}->ptr)[{i}]);", mangle(e));
                        }
                        let _ = writeln!(self.out, "    {p}->front = {p}->back;");
                        format!("{p}->tail_len")
                    }
                    B::SpliceReserve => {
                        let _ = writeln!(self.out, "    lust_vec_reserve({dv}, {}, sizeof({et}), _Alignof({et}));", vals[1]);
                        "((lust_Unit){})".into()
                    }
                    B::SpliceGap => format!("({p}->start < {p}->tail_start)"),
                    B::SplicePut => {
                        let _ = writeln!(self.out, "    (({et}*){dv}->ptr)[{p}->start] = {}; {p}->start++; {dv}->len = {p}->start;", vals[1]);
                        "((lust_Unit){})".into()
                    }
                    _ => {
                        // `move_tail(n)`: `buf.reserve(tail_start + tail_len, n)`,
                        // then the tail moves up by n.
                        let (old, n) = (self.tmp(), &vals[1]);
                        let _ = writeln!(
                            self.out,
                            "    uint64_t {old} = {dv}->len; {dv}->len = {p}->tail_start + {p}->tail_len;\n    lust_vec_reserve({dv}, {n}, sizeof({et}), _Alignof({et})); {dv}->len = {old};\n    lust_memmove((({et}*){dv}->ptr) + {p}->tail_start + {n}, (({et}*){dv}->ptr) + {p}->tail_start, {p}->tail_len * sizeof({et})); {p}->tail_start += {n};"
                        );
                        "((lust_Unit){})".into()
                    }
                }
            }
            _ => return None,
        })
    }

    /// The `cmp(ctx, p)` adapter of `partition_point`: `pred(p)` as
    /// `Less` (-1) or `Greater` (1); ctx is the closure.
    fn partition_adapter(&mut self, elem: &CTy, f: &(sync::Callee, u8, CTy)) -> String {
        let name = format!("lust_bcmp_{}_{}", super::names::fn_tag(self.slots.of(self.body.fn_id)), self.adapters);
        self.adapters += 1;
        let pt = ctype(&CTy::Ref(Box::new(elem.clone())));
        let mut body = String::new();
        let (r, _) = self.adapter_call_c(&mut body, f, "ctx", &[format!("(({pt})p)")]);
        let _ = writeln!(body, "  return {r} ? -1 : 1;");
        let _ = writeln!(self.prelude, "static int32_t {name}(void *ctx, const void *p) {{\n{body}}}");
        name
    }
}
