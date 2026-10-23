// Fragment shape recognition for macro matching (ARCH 6.2).
//
// rustc parses a fragment with its full Rust parser. lust's parser
// covers a subset, so a valid fragment the subset cannot parse yet
// (a closure, `x?`, `x.await`, an `unsafe` block, a float pattern,
// a bare `dyn`) would read as "no fragment here" and pick the wrong
// arm or fail the call. This module recognizes those shapes at the
// token-tree level: it only ever answers for a whole slice (or one
// greedy expression end), it builds no AST, and anything it is not
// sure of it refuses, so a refuse stays a reject and never becomes
// a silent accept of token soup rustc rejects. The matcher tries
// the real parser first and this second.
use super::*;
use crate::lexer::{Delim, Tok};

/// A cursor over one tree list. `pending_gt` holds the second half
/// of a `>>` token split by generic parsing, the same trick the
/// real parser uses: reading one `>` from a `>>` leaves one behind.
struct Cur<'a> {
    ts: &'a [Tt],
    i: usize,
    pending_gt: bool,
    pending_ge: bool,
    interner: &'a Interner,
    /// True for the 2024 expression grammar, false for `expr_2021`.
    ed2024: bool,
    /// Set while parsing a condition (struct literals are barred).
    no_struct: bool,
    /// True when the last expression parsed ended in a block-like
    /// tail that needs no `;` as a statement.
    block_like: bool,
    /// Set by a caller that parses an expression statement: the next
    /// `parse_expr_bp` applies rustc's statement rule to its head.
    stmt_start: bool,
    /// True while the head of an expression statement is parsed: a
    /// block-like head (`{}`, `if`, `match`, loops) takes no call or
    /// index after it and ends the statement (only `.` and `?` go on).
    stmt_head: bool,
    depth: u32,
}

impl<'a> Cur<'a> {
    fn new(ts: &'a [Tt], interner: &'a Interner, ed2024: bool, depth: u32) -> Self {
        Cur {
            ts,
            i: 0,
            pending_gt: false,
            pending_ge: false,
            interner,
            ed2024,
            no_struct: false,
            block_like: false,
            stmt_start: false,
            stmt_head: false,
            depth,
        }
    }
    /// A child cursor for a group's inner trees.
    fn child(&self, ts: &'a [Tt]) -> Self {
        Cur::new(ts, self.interner, self.ed2024, self.depth + 1)
    }
    fn tok(&self) -> Option<Tok> {
        if self.pending_gt {
            return Some(Tok::Gt);
        }
        if self.pending_ge {
            return Some(Tok::Ge);
        }
        tok_at(self.ts, self.i).map(|t| t.tok)
    }
    fn tree(&self) -> Option<&'a Tt> {
        if self.pending_gt || self.pending_ge {
            return None;
        }
        self.ts.get(self.i)
    }
    fn at(&self, t: Tok) -> bool {
        self.tok() == Some(t)
    }
    fn bump(&mut self) {
        if self.pending_gt {
            self.pending_gt = false;
        } else if self.pending_ge {
            self.pending_ge = false;
        } else {
            self.i += 1;
        }
    }
    fn eat(&mut self, t: Tok) -> bool {
        if t == Tok::Gt && !self.pending_gt && !self.pending_ge && self.tok() == Some(Tok::Shr) {
            self.i += 1;
            self.pending_gt = true;
            return true;
        }
        if t == Tok::Gt && !self.pending_gt && !self.pending_ge && self.tok() == Some(Tok::ShrEq) {
            self.i += 1;
            self.pending_ge = true;
            return true;
        }
        if self.at(t) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn done(&self) -> bool {
        !self.pending_gt && !self.pending_ge && self.i >= self.ts.len()
    }
    fn ok_depth(&self) -> bool {
        self.depth < 160
    }
    /// The text of the current token when it is one written word.
    /// Reserved words count (`box` heads a pattern).
    fn word(&self) -> Option<String> {
        match self.tok() {
            Some(Tok::Reserved(s)) => Some(self.interner.get(s).to_string()),
            t => t.and_then(|t| seg_text(t, self.interner)),
        }
    }
    /// Skips outer attributes at the cursor. Returns the count.
    fn attrs(&mut self) -> usize {
        let mut n = 0;
        while self.at(Tok::Pound) && matches!(self.ts.get(self.i + 1), Some(Tt::Delim(Delim::Bracket, _, _))) {
            self.i += 2;
            n += 1;
        }
        n
    }
    /// Takes the current tree when it is a group of `d`, advancing.
    fn group(&mut self, d: Delim) -> Option<&'a [Tt]> {
        match self.tree() {
            Some(Tt::Delim(dd, inner, _)) if *dd == d => {
                let inner: &'a [Tt] = inner;
                self.i += 1;
                Some(inner)
            }
            _ => None,
        }
    }
}

/// Top-level comma pieces of a tree list (groups are single trees,
/// so every comma token here is a piece separator).
fn pieces(ts: &[Tt]) -> Vec<&[Tt]> {
    let mut out = Vec::new();
    let mut start = 0;
    for i in 0..=ts.len() {
        if i == ts.len() || matches!(&ts[i], Tt::Tok(t) if t.tok == Tok::Comma) {
            out.push(&ts[start..i]);
            start = i + 1;
        }
    }
    out
}

/// True when every comma piece passes `f`. An empty piece is
/// allowed only as the last one: a trailing comma, or the whole
/// empty list. A `,,` anywhere else does not parse in rustc.
fn pieces_all(ts: &[Tt], f: impl Fn(&[Tt]) -> bool) -> bool {
    let ps = pieces(ts);
    let n = ps.len();
    ps.into_iter().enumerate().all(|(i, p)| if p.is_empty() { i + 1 == n } else { f(p) })
}

/// True for tokens that name one path segment in the shapes here.
fn is_seg(t: Tok) -> bool {
    is_seg_tok(t)
}

/// True for one literal token.
fn is_literal(t: Tok) -> bool {
    matches!(t, Tok::Int(..) | Tok::Float(_) | Tok::Str(..) | Tok::ByteStr(_) | Tok::ByteChar(_) | Tok::Char(..) | Tok::True | Tok::False)
}

// ---------- Paths, generic arguments, types ----------

/// Parses one generic argument list at a `<`: lifetimes, types,
/// const pieces (a literal, a block, a path read as a const), and
/// `Name = value` / `Name: bounds` bindings.
fn generic_args(c: &mut Cur) -> bool {
    if !c.eat(Tok::Lt) {
        return false;
    }
    if c.eat(Tok::Gt) {
        return true; // rustc's path parser accepts empty arguments.
    }
    loop {
        if !c.ok_depth() {
            return false;
        }
        match c.tok() {
            Some(Tok::Lifetime(_)) => c.bump(),
            _ if matches!(c.tree(), Some(Tt::Delim(Delim::Brace, _, _))) => {
                let Some(inner) = c.group(Delim::Brace) else { return false };
                if !block_inner(&mut c.child(inner)) {
                    return false;
                }
            }
            Some(Tok::Minus) => {
                c.bump();
                match c.tok() {
                    Some(t) if is_literal(t) => c.bump(),
                    _ => return false,
                }
            }
            Some(t) if is_literal(t) => c.bump(),
            Some(t) if is_seg(t) => {
                // A binding: one name, then `=` or `:`.
                let save = (c.i, c.pending_gt, c.pending_ge);
                c.bump();
                if c.eat(Tok::Eq) {
                    match c.tok() {
                        Some(t) if is_literal(t) => c.bump(),
                        _ if matches!(c.tree(), Some(Tt::Delim(Delim::Brace, _, _))) => {
                            let Some(inner) = c.group(Delim::Brace) else { return false };
                            if !block_inner(&mut c.child(inner)) {
                                return false;
                            }
                        }
                        _ => {
                            if !parse_ty(c) {
                                return false;
                            }
                        }
                    }
                } else if c.eat(Tok::Colon) {
                    if !parse_bounds(c) {
                        return false;
                    }
                } else {
                    (c.i, c.pending_gt, c.pending_ge) = save;
                    if !parse_ty(c) {
                        return false;
                    }
                }
            }
            _ => {
                if !parse_ty(c) {
                    return false;
                }
            }
        }
        if c.eat(Tok::Gt) {
            return true;
        }
        if !c.eat(Tok::Comma) {
            return false;
        }
        if c.eat(Tok::Gt) {
            return true; // a trailing comma
        }
    }
}

/// Parses generic *parameters* at a `<` in a definition head.
fn generic_params(c: &mut Cur) -> bool {
    if !c.at(Tok::Lt) {
        return true;
    }
    c.bump();
    if c.eat(Tok::Gt) {
        return true;
    }
    loop {
        c.attrs();
        match c.tok() {
            Some(Tok::Lifetime(_)) => {
                c.bump();
                if c.eat(Tok::Colon) && !parse_bounds(c) {
                    return false;
                }
            }
            Some(Tok::Const) => {
                c.bump();
                if !matches!(c.tok(), Some(t) if is_seg(t)) {
                    return false;
                }
                c.bump();
                if !c.eat(Tok::Colon) || !parse_ty(c) {
                    return false;
                }
                if c.eat(Tok::Eq) && !parse_expr_bp(c, 0) {
                    return false;
                }
            }
            Some(t) if is_seg(t) => {
                c.bump();
                if c.eat(Tok::Colon) && !parse_bounds(c) {
                    return false;
                }
                if c.eat(Tok::Eq) && !parse_ty(c) {
                    return false;
                }
            }
            _ => return false,
        }
        if c.eat(Tok::Gt) {
            return true;
        }
        if !c.eat(Tok::Comma) {
            return false;
        }
        if c.eat(Tok::Gt) {
            return true;
        }
    }
}

/// Parses a type-level path: segments with optional generic
/// arguments, optional `Fn(A) -> B` sugar on the last segment, and
/// an optional leading `::`. A qualified `<T as P>` head counts.
fn parse_path_ty(c: &mut Cur) -> bool {
    if c.at(Tok::Lt) {
        return parse_qualified(c, true);
    }
    c.eat(Tok::PathSep);
    loop {
        if !matches!(c.tok(), Some(t) if is_seg(t)) {
            return false;
        }
        c.bump();
        // Generic arguments, plain or turbofish.
        let mut angle = false;
        if c.at(Tok::PathSep) {
            let save = (c.i, c.pending_gt, c.pending_ge);
            c.bump();
            if c.at(Tok::Lt) {
                if !generic_args(c) {
                    return false;
                }
                angle = true;
            } else {
                (c.i, c.pending_gt, c.pending_ge) = save;
            }
        } else if c.at(Tok::Lt) {
            if !generic_args(c) {
                return false;
            }
            angle = true;
        }
        // `Fn(A, B) -> C` sugar ends the path; a segment with `<..>`
        // arguments takes no `(..)` ones.
        if !angle && matches!(c.tree(), Some(Tt::Delim(Delim::Paren, _, _))) {
            let Some(inner) = c.group(Delim::Paren) else { return false };
            if !pieces_all(inner, |p| is_ty(p, c.interner)) {
                return false;
            }
            if c.eat(Tok::Arrow) && !parse_ty(c) {
                return false;
            }
            return true;
        }
        if c.eat(Tok::PathSep) {
            continue;
        }
        return true;
    }
}

/// Parses `<T>` or `<T as P>` followed by `::seg...`. In `ty`
/// position the trailing segments use type rules; in expression
/// and pattern position they end the qualified path itself and
/// the caller keeps parsing postfix forms.
fn parse_qualified(c: &mut Cur, ty: bool) -> bool {
    if !c.eat(Tok::Lt) || !parse_ty(c) {
        return false;
    }
    if c.eat(Tok::As) && !parse_path_ty(c) {
        return false;
    }
    if !c.eat(Tok::Gt) {
        return false;
    }
    // rustc expects `::` and a segment after the closing `>`.
    if !c.at(Tok::PathSep) {
        return false;
    }
    if ty {
        // The rest reads as one more segment chain.
        while c.eat(Tok::PathSep) {
            if !matches!(c.tok(), Some(t) if is_seg(t)) {
                return false;
            }
            c.bump();
            if c.at(Tok::Lt) && !generic_args(c) {
                return false;
            }
        }
    }
    // In expression position the caller consumes `::seg` chains.
    true
}

/// The end of the bounds rustc reads after a path type when `ts[pos]`
/// is `+` (`parse_remaining_bounds`): the `+`, then bounds joined by
/// `+` while one can begin, a trailing `+` included, possibly none.
/// None when a bound begins and does not parse.
pub fn bounds_tail_end(ts: &[Tt], pos: usize, interner: &Interner) -> Option<usize> {
    let mut c = Cur::new(ts, interner, true, 0);
    c.i = pos + 1;
    loop {
        if !bound_start(&c) {
            break;
        }
        if !parse_bound(&mut c) || c.pending_gt || c.pending_ge {
            return None;
        }
        if !c.eat(Tok::Plus) {
            break;
        }
    }
    Some(c.i)
}

/// rustc's `can_begin_bound`: a path, a lifetime, `?`, `!`, `for`,
/// `const`, `async`, `use`, a parenthesized bound, or `[const]`.
fn bound_start(c: &Cur) -> bool {
    match c.tree() {
        Some(Tt::Delim(Delim::Paren, _, _)) => true,
        Some(Tt::Delim(Delim::Bracket, inner, _)) => matches!(inner.first(), Some(Tt::Tok(t)) if t.tok == Tok::Const),
        Some(Tt::Frag(kind, _, _)) => matches!(kind, FragKind::Path | FragKind::Ty),
        Some(Tt::Tok(t)) => {
            is_seg(t.tok)
                || matches!(
                    t.tok,
                    Tok::PathSep | Tok::Lt | Tok::Shl | Tok::Lifetime(_) | Tok::Question | Tok::Bang | Tok::For | Tok::Const | Tok::Async | Tok::Use
                )
        }
        _ => false,
    }
}

/// Parses one trait-bound list (`A + B + 'a`), at least one bound.
fn parse_bounds(c: &mut Cur) -> bool {
    loop {
        if !parse_bound(c) {
            return false;
        }
        if !c.eat(Tok::Plus) {
            return true;
        }
    }
}

/// Parses one trait bound.
fn parse_bound(c: &mut Cur) -> bool {
    c.eat(Tok::Question); // `?Sized`
    if matches!(c.tok(), Some(Tok::Lifetime(_))) {
        c.bump();
        return true;
    }
    if c.at(Tok::For) {
        // A binder: `for<...>`. A bare `for` is not a bound.
        c.bump();
        if !c.at(Tok::Lt) || !generic_params(c) {
            return false;
        }
    }
    if c.at(Tok::Use) {
        // Precise capturing: `use<'a, T>`.
        c.bump();
        return c.at(Tok::Lt) && generic_args(c);
    }
    if matches!(c.tree(), Some(Tt::Delim(Delim::Paren, _, _))) {
        let Some(inner) = c.group(Delim::Paren) else { return false };
        let mut sub = c.child(inner);
        return parse_bounds(&mut sub) && sub.done();
    }
    parse_path_ty(c)
}

/// Parses one type at the cursor.
fn parse_ty(c: &mut Cur) -> bool {
    if !c.ok_depth() {
        return false;
    }
    if let Some(end) = super::match_::macro_call_shape(c.ts, c.i) {
        if !c.pending_gt && !c.pending_ge {
            c.i = end;
            return true;
        }
    }
    match c.tree() {
        // A forwarded fragment is one type only when it is a type or a
        // path (rustc's `can_begin_type`).
        Some(Tt::Frag(kind, _, _)) => {
            if !matches!(kind, FragKind::Ty | FragKind::Path) {
                return false;
            }
            c.i += 1;
            return true;
        }
        Some(Tt::Delim(Delim::Paren, _, _)) => {
            let Some(inner) = c.group(Delim::Paren) else { return false };
            return pieces_all(inner, |p| is_ty(p, c.interner));
        }
        Some(Tt::Delim(Delim::Bracket, _, _)) => {
            let Some(inner) = c.group(Delim::Bracket) else { return false };
            // `[T]` or `[T; n]`.
            let semi = inner.iter().position(|t| matches!(t, Tt::Tok(x) if x.tok == Tok::Semi));
            return match semi {
                None => is_ty(inner, c.interner),
                Some(s) => is_ty(&inner[..s], c.interner) && is_expr(&inner[s + 1..], c.interner, c.ed2024),
            };
        }
        _ => {}
    }
    match c.tok() {
        Some(Tok::Underscore | Tok::Bang) => {
            c.bump();
            true
        }
        Some(Tok::Star) => {
            c.bump();
            (c.eat(Tok::Const) || c.eat(Tok::Mut)) && parse_ty(c)
        }
        Some(Tok::Amp) => {
            c.bump();
            if matches!(c.tok(), Some(Tok::Lifetime(_))) {
                c.bump();
            }
            c.eat(Tok::Mut);
            parse_ty(c)
        }
        Some(Tok::AndAnd) => {
            c.bump();
            if matches!(c.tok(), Some(Tok::Lifetime(_))) {
                c.bump();
            }
            c.eat(Tok::Mut);
            parse_ty(c)
        }
        Some(Tok::Dyn | Tok::Impl) => {
            c.bump();
            // A bare `dyn` or `impl` parses as a type in rustc's
            // fragment parser (the missing bound is judged only
            // if the fragment is ever used as a type).
            if parse_bound(c) {
                while c.eat(Tok::Plus) {
                    if !parse_bound(c) {
                        return false;
                    }
                }
            }
            true
        }
        Some(Tok::For) => {
            c.bump();
            c.at(Tok::Lt) && generic_params(c) && parse_ty(c)
        }
        Some(Tok::Fn | Tok::Unsafe | Tok::Extern) if is_fn_ty_start(c) => parse_fn_ty(c),
        Some(Tok::Lt) => parse_qualified(c, true),
        _ => parse_path_ty(c),
    }
}

/// True when the cursor stands at a function pointer type head.
fn is_fn_ty_start(c: &Cur) -> bool {
    let mut j = c.i;
    let t = |j: usize| tok_at(c.ts, j).map(|x| x.tok);
    if t(j) == Some(Tok::Unsafe) {
        j += 1;
    }
    if t(j) == Some(Tok::Extern) {
        j += 1;
        if matches!(t(j), Some(Tok::Str(..))) {
            j += 1;
        }
    }
    t(j) == Some(Tok::Fn)
}

/// Parses `unsafe extern "C" fn(A) -> B` and its plainer forms.
fn parse_fn_ty(c: &mut Cur) -> bool {
    c.eat(Tok::Unsafe);
    if c.eat(Tok::Extern) && matches!(c.tok(), Some(Tok::Str(..))) {
        c.bump();
    }
    if !c.eat(Tok::Fn) {
        return false;
    }
    let Some(inner) = c.group(Delim::Paren) else { return false };
    let ps = pieces(inner);
    let last = ps.len() - 1;
    for (idx, p) in ps.into_iter().enumerate() {
        if matches!(p, [Tt::Tok(t)] if t.tok == Tok::Ellipsis) || (p.is_empty() && idx == last) {
            continue;
        }
        if p.is_empty() {
            return false;
        }
        // An optional argument name precedes the type.
        let ty_at = if p.len() > 2 && tok_at(p, 1).map(|t| t.tok) == Some(Tok::Colon) { 2 } else { 0 };
        if !is_ty(&p[ty_at..], c.interner) {
            return false;
        }
    }
    !c.eat(Tok::Arrow) || parse_ty(c)
}

/// True when `slice` is exactly one type in full Rust syntax.
pub fn is_ty(slice: &[Tt], interner: &Interner) -> bool {
    if slice.is_empty() {
        return false;
    }
    let mut c = Cur::new(slice, interner, true, 0);
    parse_ty(&mut c) && c.done()
}

// ---------- Patterns ----------

/// True when `slice` is exactly one pattern. `or` allows a
/// top-level `|` (the `pat` fragment; `pat_param` does not). A
/// leading `..=` never begins a pattern fragment in rustc.
pub fn is_pat(slice: &[Tt], interner: &Interner, or: bool) -> bool {
    if slice.is_empty() || matches!(slice.first(), Some(Tt::Tok(t)) if t.tok == Tok::DotDotEq) {
        return false;
    }
    let mut c = Cur::new(slice, interner, true, 0);
    parse_pat(&mut c, or) && c.done()
}

/// Parses one pattern at the cursor.
fn parse_pat(c: &mut Cur, or: bool) -> bool {
    if or {
        c.eat(Tok::Pipe);
    }
    if !parse_pat_one(c) {
        return false;
    }
    while or && c.eat(Tok::Pipe) {
        if !parse_pat_one(c) {
            return false;
        }
    }
    true
}

/// True when the next tree can be a range bound in a pattern.
fn range_bound_start(c: &Cur) -> bool {
    match c.tok() {
        Some(t) if is_literal(t) => true,
        Some(Tok::Minus) => true,
        Some(t) if is_seg(t) => true,
        Some(Tok::PathSep | Tok::Lt) => true,
        _ => false,
    }
}

/// Parses a pattern range bound: a literal or a path.
fn parse_pat_bound(c: &mut Cur) -> bool {
    c.eat(Tok::Minus);
    match c.tok() {
        Some(t) if is_literal(t) => {
            c.bump();
            true
        }
        _ => parse_pat_path(c),
    }
}

/// A range tail after a first bound: `..b`, `..=b`, or `..`.
/// The end may be absent only after `..`.
fn pat_range_tail(c: &mut Cur) -> bool {
    if c.eat(Tok::DotDotEq) {
        return range_bound_start(c) && parse_pat_bound(c);
    }
    if c.eat(Tok::DotDot) && range_bound_start(c) {
        return parse_pat_bound(c);
    }
    true
}

/// Parses a path in pattern position (segments and generic
/// arguments; no struct or tuple tail).
fn parse_pat_path(c: &mut Cur) -> bool {
    if c.at(Tok::Lt) {
        if !parse_qualified(c, false) {
            return false;
        }
        // The segment chain after `<..>::` belongs to the path.
        while c.at(Tok::PathSep) {
            let save = (c.i, c.pending_gt, c.pending_ge);
            c.bump();
            if !matches!(c.tok(), Some(t) if is_seg(t)) {
                (c.i, c.pending_gt, c.pending_ge) = save;
                break;
            }
            c.bump();
        }
        return true;
    }
    c.eat(Tok::PathSep);
    loop {
        if !matches!(c.tok(), Some(t) if is_seg(t)) {
            return false;
        }
        c.bump();
        if c.at(Tok::PathSep) {
            let save = (c.i, c.pending_gt, c.pending_ge);
            c.bump();
            if c.at(Tok::Lt) {
                if !generic_args(c) {
                    return false;
                }
            } else {
                (c.i, c.pending_gt, c.pending_ge) = save;
            }
        }
        if c.eat(Tok::PathSep) {
            continue;
        }
        return true;
    }
}

/// Parses one non-`|` pattern at the cursor.
fn parse_pat_one(c: &mut Cur) -> bool {
    if !c.ok_depth() {
        return false;
    }
    c.attrs();
    if let Some(end) = super::match_::macro_call_shape(c.ts, c.i) {
        if !c.pending_gt && !c.pending_ge {
            c.i = end;
            return true;
        }
    }
    match c.tree() {
        // A forwarded fragment is one pattern when it is a pattern, a
        // path, or a literal (an `expr` only when it holds one).
        Some(Tt::Frag(kind, inner, _)) => {
            let literal_expr = matches!(kind, FragKind::Expr | FragKind::Expr2021) && super::match_::trees_read_literal(inner);
            if !(matches!(kind, FragKind::Pat | FragKind::PatParam | FragKind::Path | FragKind::Literal) || literal_expr) {
                return false;
            }
            c.i += 1;
            return true;
        }
        Some(Tt::Delim(Delim::Paren | Delim::Bracket, _, _)) => {
            let d = match c.tree() {
                Some(Tt::Delim(d, _, _)) => *d,
                _ => unreachable!(),
            };
            let Some(inner) = c.group(d) else { return false };
            return pieces_all(inner, |p| is_pat(p, c.interner, true) || is_rest(p));
        }
        _ => {}
    }
    match c.tok() {
        Some(Tok::DotDot) => {
            c.bump();
            if range_bound_start(c) { parse_pat_bound(c) } else { true }
        }
        Some(Tok::DotDotEq) => {
            c.bump();
            parse_pat_bound(c)
        }
        Some(Tok::Underscore) => {
            c.bump();
            true
        }
        Some(Tok::Minus) => {
            c.bump();
            match c.tok() {
                Some(t) if is_literal(t) => {
                    c.bump();
                    pat_range_tail(c)
                }
                _ => false,
            }
        }
        Some(t) if is_literal(t) => {
            c.bump();
            pat_range_tail(c)
        }
        Some(Tok::Amp) => {
            c.bump();
            c.eat(Tok::Mut);
            parse_pat_one(c)
        }
        Some(Tok::AndAnd) => {
            c.bump();
            c.eat(Tok::Mut);
            parse_pat_one(c)
        }
        Some(Tok::Ref) => {
            c.bump();
            c.eat(Tok::Mut);
            parse_pat_binding(c)
        }
        Some(Tok::Mut) => {
            c.bump();
            parse_pat_binding(c)
        }
        _ if c.word().as_deref() == Some("box") && box_arg_follows(c) => {
            c.bump();
            parse_pat_one(c)
        }
        _ => parse_pat_path_pat(c),
    }
}

/// True when `box` here is the box pattern head, not a binding.
fn box_arg_follows(c: &Cur) -> bool {
    match c.ts.get(c.i + 1) {
        Some(Tt::Delim(_, _, _)) | Some(Tt::Frag(_, _, _)) => true,
        Some(Tt::Tok(t)) => {
            matches!(t.tok, Tok::Ident(_) | Tok::SelfUpper | Tok::Underscore | Tok::Amp | Tok::Ref | Tok::Mut | Tok::Minus | Tok::PathSep)
                || is_literal(t.tok)
        }
        None => false,
    }
}

/// A `..` rest piece inside a tuple or slice pattern.
fn is_rest(p: &[Tt]) -> bool {
    matches!(p, [Tt::Tok(t)] if t.tok == Tok::DotDot)
}

/// Parses `name` plus an optional `@ pat` binding tail.
fn parse_pat_binding(c: &mut Cur) -> bool {
    if !matches!(c.tok(), Some(t) if is_seg(t)) {
        return false;
    }
    c.bump();
    !c.eat(Tok::At) || parse_pat_one(c)
}

/// Parses a path-led pattern: a constant or binding, tuple and
/// struct patterns, an `@` binding, or a range.
fn parse_pat_path_pat(c: &mut Cur) -> bool {
    let start = c.i;
    if !parse_pat_path(c) {
        return false;
    }
    // A struct pattern: `Path { field: pat, .. }`. A field is a name
    // (or tuple index) and `: pat`, or the shorthand `[ref] [mut] name`.
    if let Some(inner) = c.group(Delim::Brace) {
        return pieces_all(inner, |p| {
            if is_rest(p) {
                return true;
            }
            let tok = |i: usize| match p.get(i) {
                Some(Tt::Tok(t)) => Some(t.tok),
                _ => None,
            };
            if tok(1) == Some(Tok::Colon) {
                return matches!(tok(0), Some(Tok::Ident(_) | Tok::Int(_, None, _))) && is_pat(&p[2..], c.interner, true);
            }
            let mut i = 0;
            if tok(i) == Some(Tok::Ref) {
                i += 1;
            }
            if tok(i) == Some(Tok::Mut) {
                i += 1;
            }
            i + 1 == p.len() && matches!(tok(i), Some(Tok::Ident(_)))
        });
    }
    // A tuple struct pattern: `Path(pat, ..)`.
    if let Some(inner) = c.group(Delim::Paren) {
        return pieces_all(inner, |p| is_pat(p, c.interner, true) || is_rest(p));
    }
    if c.eat(Tok::At) {
        return parse_pat_one(c);
    }
    let _ = start;
    pat_range_tail(c)
}

// ---------- Expressions ----------

/// True when `slice` is exactly one expression in full Rust
/// syntax. `ed2024` distinguishes `expr` from `expr_2021`.
pub fn is_expr(slice: &[Tt], interner: &Interner, ed2024: bool) -> bool {
    expr_end(slice, 0, interner, ed2024) == Some(slice.len())
}

/// The greedy end of one expression starting at `pos`, in trees.
pub fn expr_end(ts: &[Tt], pos: usize, interner: &Interner, ed2024: bool) -> Option<usize> {
    let mut c = Cur::new(ts, interner, ed2024, 0);
    c.i = pos;
    if parse_expr_bp(&mut c, 0) && !c.pending_gt && !c.pending_ge && c.i > pos { Some(c.i) } else { None }
}

/// The binding power of a binary operator token, or None.
fn bin_bp(t: Tok) -> Option<u8> {
    use Tok::*;
    Some(match t {
        Eq | PlusEq | MinusEq | StarEq | SlashEq | PercentEq | AmpEq | PipeEq | CaretEq | ShlEq | ShrEq => 2,
        DotDot | DotDotEq => 3,
        OrOr => 4,
        AndAnd => 5,
        EqEq | Ne | Lt | Le | Gt | Ge => 6,
        Pipe => 7,
        Caret => 8,
        Amp => 9,
        Shl | Shr => 10,
        Plus | Minus => 11,
        Star | Slash | Percent => 12,
        As => 13,
        _ => return None,
    })
}

/// True when a forwarded fragment of `kind` is one expression operand
/// (rustc's `can_begin_expr` for a metavariable).
fn expr_frag(kind: FragKind) -> bool {
    matches!(kind, FragKind::Expr | FragKind::Expr2021 | FragKind::Literal | FragKind::Path | FragKind::Block)
}

/// True when the next tree can start an expression operand.
fn operand_start(c: &Cur) -> bool {
    match c.tree() {
        Some(Tt::Delim(_, _, _)) => return true,
        Some(Tt::Frag(kind, _, _)) => return expr_frag(*kind),
        _ => {}
    }
    matches!(
        c.tok(),
        Some(
            Tok::Ident(_)
                | Tok::Reserved(_)
                | Tok::SelfUpper
                | Tok::SelfLower
                | Tok::Crate
                | Tok::Super
                | Tok::Int(..)
                | Tok::Float(_)
                | Tok::Str(..)
                | Tok::ByteStr(_)
                | Tok::ByteChar(_)
                | Tok::Char(..)
                | Tok::True
                | Tok::False
                | Tok::Minus
                | Tok::Star
                | Tok::Amp
                | Tok::AndAnd
                | Tok::Bang
                | Tok::Pipe
                | Tok::OrOr
                | Tok::DotDot
                | Tok::DotDotEq
                | Tok::PathSep
                | Tok::Underscore
                | Tok::Lt
                | Tok::Pound
                | Tok::Lifetime(_)
                | Tok::If
                | Tok::Match
                | Tok::Loop
                | Tok::While
                | Tok::For
                | Tok::Return
                | Tok::Break
                | Tok::Continue
                | Tok::Move
                | Tok::Unsafe
                | Tok::Async
                | Tok::Const
        )
    )
}

/// Parses one expression with operators of binding power over
/// `min_bp`. Sets `block_like` when the whole expression ends in
/// a block-like tail.
fn parse_expr_bp(c: &mut Cur, min_bp: u8) -> bool {
    // rustc's statement rule: an expression statement whose head is
    // block-like ends after it (`{ 1 } - 1` is two statements).
    let outer_head = c.stmt_head;
    c.stmt_head = std::mem::take(&mut c.stmt_start);
    let ok = parse_unary(c);
    let complete = c.stmt_head && c.block_like;
    c.stmt_head = outer_head;
    if !ok {
        return false;
    }
    if complete {
        return true;
    }
    // Comparisons do not chain: `a < b < c` is a parse error in rustc.
    let mut after_cmp = false;
    loop {
        let Some(t) = c.tok() else { return true };
        let Some(bp) = bin_bp(t) else { return true };
        if bp <= min_bp {
            return true;
        }
        let cmp = matches!(t, Tok::EqEq | Tok::Ne | Tok::Lt | Tok::Le | Tok::Gt | Tok::Ge);
        if cmp && after_cmp {
            return false;
        }
        after_cmp = cmp;
        c.bump();
        c.block_like = false;
        match t {
            Tok::As => {
                if !parse_ty(c) {
                    return false;
                }
            }
            Tok::DotDot | Tok::DotDotEq => {
                // The end of a range may be absent after `..`
                // only; `a..=` without an end does not parse.
                if operand_start(c) {
                    if !parse_expr_bp(c, bp) {
                        return false;
                    }
                } else if t == Tok::DotDotEq {
                    return false;
                }
            }
            _ => {
                if !parse_expr_bp(c, bp) {
                    return false;
                }
            }
        }
    }
}

/// Parses a condition: an expression with struct literals barred,
/// with `let` patterns allowed in `&&` chains.
fn parse_cond(c: &mut Cur) -> bool {
    let saved = c.no_struct;
    c.no_struct = true;
    let ok = if c.at(Tok::Let) {
        c.bump();
        parse_pat(c, true) && c.eat(Tok::Eq) && parse_expr_bp(c, 0)
    } else {
        parse_expr_bp(c, 0)
    };
    c.no_struct = saved;
    ok
}

/// Parses prefix forms and one primary with its postfix chain.
fn parse_unary(c: &mut Cur) -> bool {
    if !c.ok_depth() {
        return false;
    }
    c.attrs();
    c.block_like = false;
    if matches!(c.tok(), Some(Tok::Minus | Tok::Bang | Tok::Star | Tok::Amp | Tok::AndAnd)) {
        c.stmt_head = false;
    }
    // A label on a loop or block (written: rustc rejects a forwarded
    // `block` after a label).
    if matches!(c.tok(), Some(Tok::Lifetime(_))) && tok_at(c.ts, c.i + 1).map(|t| t.tok) == Some(Tok::Colon) {
        c.bump();
        c.bump();
        if matches!(c.tree(), Some(Tt::Frag(..))) {
            return false;
        }
        return parse_primary(c);
    }
    match c.tok() {
        Some(Tok::Minus | Tok::Bang | Tok::Star) => {
            c.bump();
            c.depth += 1;
            let ok = parse_unary(c);
            c.depth -= 1;
            ok
        }
        Some(Tok::Amp) => {
            c.bump();
            // `&raw const x` / `&raw mut x`.
            if c.word().as_deref() == Some("raw") {
                c.bump();
                if !(c.eat(Tok::Const) || c.eat(Tok::Mut)) {
                    return false;
                }
            } else {
                c.eat(Tok::Mut);
            }
            c.depth += 1;
            let ok = parse_unary(c);
            c.depth -= 1;
            ok
        }
        Some(Tok::AndAnd) => {
            c.bump();
            c.eat(Tok::Mut);
            c.depth += 1;
            let ok = parse_unary(c);
            c.depth -= 1;
            ok
        }
        Some(Tok::DotDot) => {
            c.bump();
            !operand_start(c) || parse_expr_bp(c, 4)
        }
        Some(Tok::DotDotEq) => {
            // A leading `..=` needs its end (`..` alone is a
            // complete range, `..=` alone is not).
            c.bump();
            operand_start(c) && parse_expr_bp(c, 4)
        }
        Some(Tok::Move) => {
            c.bump();
            c.eat(Tok::Async);
            parse_closure(c)
        }
        Some(Tok::Async) => {
            c.bump();
            c.eat(Tok::Move);
            if matches!(c.tree(), Some(Tt::Delim(Delim::Brace, _, _))) { parse_primary(c) } else { parse_closure(c) }
        }
        Some(Tok::Pipe | Tok::OrOr) => parse_closure(c),
        Some(Tok::Return) => {
            c.bump();
            !operand_start(c) || parse_expr_bp(c, 0)
        }
        Some(Tok::Break) => {
            c.bump();
            if matches!(c.tok(), Some(Tok::Lifetime(_))) {
                c.bump();
            }
            !operand_start(c) || parse_expr_bp(c, 0)
        }
        Some(Tok::Continue) => {
            c.bump();
            if matches!(c.tok(), Some(Tok::Lifetime(_))) {
                c.bump();
            }
            true
        }
        _ => parse_primary(c),
    }
}

/// Parses a closure from its `|` (or `||`) head: parameters, an
/// optional return type, and the body expression.
fn parse_closure(c: &mut Cur) -> bool {
    if c.eat(Tok::OrOr) {
        // No parameters.
    } else if c.at(Tok::Pipe) {
        // The first following `|` closes the parameter list: a
        // parameter pattern cannot hold a bare top-level `|`.
        let Some(close) = (c.i + 1..c.ts.len()).find(|&j| matches!(&c.ts[j], Tt::Tok(t) if t.tok == Tok::Pipe)) else {
            return false;
        };
        let params = &c.ts[c.i + 1..close];
        let ps = pieces(params);
        let last = ps.len() - 1;
        for (idx, p) in ps.into_iter().enumerate() {
            if p.is_empty() {
                if idx != last {
                    return false;
                }
                continue;
            }
            match p.iter().position(|t| matches!(t, Tt::Tok(x) if x.tok == Tok::Colon)) {
                Some(k) if k >= 1 => {
                    if !is_pat(&p[..k], c.interner, false) || !is_ty(&p[k + 1..], c.interner) {
                        return false;
                    }
                }
                _ => {
                    if !is_pat(p, c.interner, false) {
                        return false;
                    }
                }
            }
        }
        c.i = close + 1;
    } else {
        return false;
    }
    if c.eat(Tok::Arrow) && !parse_ty(c) {
        return false;
    }
    parse_expr_bp(c, 0)
}

/// Validates the inside of one `{ }` as a statement list with an
/// optional trailing expression.
fn block_inner(c: &mut Cur) -> bool {
    if !c.ok_depth() {
        return false;
    }
    while !c.done() {
        c.attrs();
        if c.done() {
            break;
        }
        if c.eat(Tok::Semi) {
            continue;
        }
        if starts_item_at(c) {
            if !parse_item(c) {
                return false;
            }
            continue;
        }
        if c.at(Tok::Let) {
            if !parse_let(c) {
                return false;
            }
            if !c.eat(Tok::Semi) {
                return false;
            }
            continue;
        }
        c.stmt_start = true;
        if !parse_expr_bp(c, 0) {
            return false;
        }
        if c.eat(Tok::Semi) {
            continue;
        }
        if c.done() {
            return true;
        }
        if !c.block_like {
            return false;
        }
    }
    true
}

/// Parses a whole `{ }` group at the cursor as a block.
fn parse_block(c: &mut Cur) -> bool {
    match c.group(Delim::Brace) {
        Some(inner) => block_inner(&mut c.child(inner)),
        None => false,
    }
}

/// Parses a `let` at the cursor, without the `;` after it.
fn parse_let(c: &mut Cur) -> bool {
    if !c.eat(Tok::Let) || !parse_pat(c, true) {
        return false;
    }
    if c.eat(Tok::Colon) && !parse_ty(c) {
        return false;
    }
    if c.eat(Tok::Eq) {
        if !parse_expr_bp(c, 0) {
            return false;
        }
        if c.eat(Tok::Else) && !parse_block(c) {
            return false;
        }
    }
    true
}

/// Parses one primary expression and its postfix chain (calls,
/// indexes, fields, `?`). Sets `block_like` when the tail is a
/// block-like form with no postfix after it.
fn parse_primary(c: &mut Cur) -> bool {
    if !c.ok_depth() {
        return false;
    }
    if let Some(end) = super::match_::macro_call_shape(c.ts, c.i) {
        if !c.pending_gt && !c.pending_ge {
            let brace = matches!(c.ts.get(end - 1), Some(Tt::Delim(Delim::Brace, _, _)));
            c.i = end;
            c.block_like = brace;
            return parse_postfix(c);
        }
    }
    match c.tree() {
        Some(Tt::Frag(kind, _, _)) => {
            if !expr_frag(*kind) {
                return false;
            }
            c.i += 1;
            c.block_like = *kind == FragKind::Block;
            return parse_postfix(c);
        }
        Some(Tt::Delim(Delim::Paren, _, _)) => {
            let Some(inner) = c.group(Delim::Paren) else { return false };
            if !pieces_all(inner, |p| is_expr(p, c.interner, c.ed2024)) {
                return false;
            }
            return parse_postfix(c);
        }
        Some(Tt::Delim(Delim::Bracket, _, _)) => {
            let Some(inner) = c.group(Delim::Bracket) else { return false };
            let ok = match inner.iter().position(|t| matches!(t, Tt::Tok(x) if x.tok == Tok::Semi)) {
                Some(s) => is_expr(&inner[..s], c.interner, c.ed2024) && is_expr(&inner[s + 1..], c.interner, c.ed2024),
                None => pieces_all(inner, |p| is_expr(p, c.interner, c.ed2024)),
            };
            return ok && parse_postfix(c);
        }
        Some(Tt::Delim(Delim::Brace, _, _)) => {
            if !parse_block(c) {
                return false;
            }
            c.block_like = true;
            return parse_postfix(c);
        }
        _ => {}
    }
    match c.tok() {
        Some(t) if is_literal(t) => {
            c.bump();
            parse_postfix(c)
        }
        Some(Tok::Underscore) => {
            if !c.ed2024 {
                return false;
            }
            c.bump();
            parse_postfix(c)
        }
        Some(Tok::If) => {
            c.bump();
            if !parse_cond(c) || !parse_block(c) {
                return false;
            }
            c.block_like = true;
            if c.eat(Tok::Else) {
                if c.at(Tok::If) {
                    return parse_primary(c);
                }
                if !parse_block(c) {
                    return false;
                }
                c.block_like = true;
            }
            parse_postfix(c)
        }
        Some(Tok::Match) => {
            c.bump();
            let saved = c.no_struct;
            c.no_struct = true;
            let ok = parse_expr_bp(c, 0);
            c.no_struct = saved;
            if !ok || !parse_arms(c) {
                return false;
            }
            c.block_like = true;
            parse_postfix(c)
        }
        Some(Tok::Loop) => {
            c.bump();
            if !parse_block(c) {
                return false;
            }
            c.block_like = true;
            parse_postfix(c)
        }
        Some(Tok::While) => {
            c.bump();
            if !parse_cond(c) || !parse_block(c) {
                return false;
            }
            c.block_like = true;
            parse_postfix(c)
        }
        Some(Tok::For) => {
            c.bump();
            let saved = c.no_struct;
            c.no_struct = true;
            let ok = parse_pat(c, true) && c.eat(Tok::In) && parse_expr_bp(c, 0);
            c.no_struct = saved;
            if !ok || !parse_block(c) {
                return false;
            }
            c.block_like = true;
            parse_postfix(c)
        }
        Some(Tok::Unsafe) => {
            c.bump();
            if !parse_block(c) {
                return false;
            }
            c.block_like = true;
            parse_postfix(c)
        }
        Some(Tok::Const) => {
            if !c.ed2024 || !matches!(c.ts.get(c.i + 1), Some(Tt::Delim(Delim::Brace, _, _))) {
                return false;
            }
            c.bump();
            if !parse_block(c) {
                return false;
            }
            c.block_like = true;
            parse_postfix(c)
        }
        Some(Tok::Lt) => {
            if !parse_qualified(c, false) {
                return false;
            }
            // The segment chain after `<..>::` belongs to the path.
            while c.eat(Tok::PathSep) {
                if !matches!(c.tok(), Some(t) if is_seg(t)) {
                    return false;
                }
                c.bump();
                // A turbofish on this segment.
                if c.at(Tok::PathSep) {
                    let save = (c.i, c.pending_gt, c.pending_ge);
                    c.bump();
                    if c.at(Tok::Lt) {
                        if !generic_args(c) {
                            return false;
                        }
                    } else {
                        (c.i, c.pending_gt, c.pending_ge) = save;
                    }
                }
            }
            parse_path_tail(c)
        }
        Some(Tok::PathSep) => parse_path_expr(c),
        Some(t) if is_seg(t) => parse_path_expr(c),
        _ => false,
    }
}

/// The postfix chain after a primary: calls, indexes, field and
/// method access (with turbofish), `.await`, and `?`.
fn parse_postfix(c: &mut Cur) -> bool {
    loop {
        match c.tree() {
            Some(Tt::Delim(Delim::Paren | Delim::Bracket, _, _)) if c.stmt_head && c.block_like => return true,
            Some(Tt::Delim(Delim::Paren, _, _)) => {
                let Some(inner) = c.group(Delim::Paren) else { return false };
                if !pieces_all(inner, |p| is_expr(p, c.interner, c.ed2024)) {
                    return false;
                }
                c.block_like = false;
            }
            Some(Tt::Delim(Delim::Bracket, _, _)) => {
                let Some(inner) = c.group(Delim::Bracket) else { return false };
                if !is_expr(inner, c.interner, c.ed2024) {
                    return false;
                }
                c.block_like = false;
            }
            _ if c.at(Tok::Dot) => {
                c.bump();
                c.block_like = false;
                match c.tok() {
                    Some(Tok::Await) => c.bump(),
                    Some(Tok::Int(..)) => c.bump(),
                    // `t.0.1`: the `0.1` is one float token, two tuple
                    // indexes in field position. The parser checks the
                    // text (src/parser.rs) and rejects any other float.
                    Some(Tok::Float(_)) => c.bump(),
                    Some(t) if is_seg(t) => {
                        c.bump();
                        if c.at(Tok::PathSep) {
                            let save = (c.i, c.pending_gt, c.pending_ge);
                            c.bump();
                            if c.at(Tok::Lt) {
                                if !generic_args(c) {
                                    return false;
                                }
                            } else {
                                (c.i, c.pending_gt, c.pending_ge) = save;
                            }
                        }
                    }
                    _ => return false,
                }
            }
            _ if c.at(Tok::Question) => {
                c.bump();
                c.block_like = false;
            }
            _ => return true,
        }
    }
}

/// Parses an expression path from its first segment (or a leading
/// `::`), with turbofish, struct literals, and the postfix chain.
fn parse_path_expr(c: &mut Cur) -> bool {
    c.eat(Tok::PathSep);
    loop {
        if !matches!(c.tok(), Some(t) if is_seg(t)) {
            return false;
        }
        c.bump();
        if c.at(Tok::PathSep) {
            let save = (c.i, c.pending_gt, c.pending_ge);
            c.bump();
            if c.at(Tok::Lt) {
                if !generic_args(c) {
                    return false;
                }
                if c.eat(Tok::PathSep) {
                    continue;
                }
                return parse_postfix(c);
            }
            (c.i, c.pending_gt, c.pending_ge) = save;
        }
        if c.eat(Tok::PathSep) {
            continue;
        }
        break;
    }
    parse_path_tail(c)
}

/// After a whole expression path: a struct literal body when the
/// `{ }` reads as fields, then the postfix chain.
fn parse_path_tail(c: &mut Cur) -> bool {
    if !c.no_struct && matches!(c.tree(), Some(Tt::Delim(Delim::Brace, _, _))) {
        let save = c.i;
        let Some(inner) = c.group(Delim::Brace) else { return false };
        if struct_fields(inner, c.interner, c.ed2024) {
            c.block_like = false;
            return parse_postfix(c);
        }
        c.i = save;
    }
    parse_postfix(c)
}

/// True when a `{ }` body reads as struct literal fields:
/// `name`, `name: expr`, or `..expr` pieces.
fn struct_fields(inner: &[Tt], interner: &Interner, ed2024: bool) -> bool {
    pieces_all(inner, |p| {
        if matches!(p.first(), Some(Tt::Tok(t)) if t.tok == Tok::DotDot) {
            return p.len() > 1 && is_expr(&p[1..], interner, ed2024);
        }
        // `name: expr` (a name or a tuple index), or the shorthand
        // `name`; rustc rejects keywords and numbers as a shorthand.
        match p.iter().position(|t| matches!(t, Tt::Tok(x) if x.tok == Tok::Colon)) {
            Some(1) => {
                matches!(p.first(), Some(Tt::Tok(t)) if matches!(t.tok, Tok::Ident(_) | Tok::Int(_, None, _)))
                    && is_expr(&p[2..], interner, ed2024)
            }
            Some(_) => false,
            None => matches!(p, [Tt::Tok(t)] if matches!(t.tok, Tok::Ident(_))),
        }
    })
}

/// Validates match arms inside one `{ }`.
fn parse_arms(c: &mut Cur) -> bool {
    match c.group(Delim::Brace) {
        Some(inner) => {
            let mut a = c.child(inner);
            while !a.done() {
                a.attrs();
                if a.done() {
                    break;
                }
                if !parse_pat(&mut a, true) {
                    return false;
                }
                if a.eat(Tok::If) && !parse_expr_bp(&mut a, 0) {
                    return false;
                }
                if !a.eat(Tok::FatArrow) {
                    return false;
                }
                if matches!(a.tree(), Some(Tt::Delim(Delim::Brace, _, _))) {
                    if !parse_block(&mut a) {
                        return false;
                    }
                    a.eat(Tok::Comma);
                } else {
                    if !parse_expr_bp(&mut a, 0) {
                        return false;
                    }
                    if !a.done() && !a.eat(Tok::Comma) {
                        return false;
                    }
                }
            }
            true
        }
        None => false,
    }
}

// ---------- Statements and items ----------

/// True when `slice` is exactly one statement: a `let`, an item,
/// or one expression. (A lone `;` is the caller's own case.)
pub fn is_stmt(slice: &[Tt], interner: &Interner) -> bool {
    if slice.is_empty() {
        return false;
    }
    let mut c = Cur::new(slice, interner, true, 0);
    c.attrs();
    if c.at(Tok::Let) {
        return parse_let(&mut c) && c.done();
    }
    if starts_item_at(&c) {
        return parse_item(&mut c) && c.done();
    }
    c.stmt_start = true;
    parse_expr_bp(&mut c, 0) && c.done()
}

/// True when `slice` is exactly one item in full Rust syntax.
pub fn is_item(slice: &[Tt], interner: &Interner) -> bool {
    if slice.is_empty() {
        return false;
    }
    let mut c = Cur::new(slice, interner, true, 0);
    parse_item(&mut c) && c.done()
}

/// True when `tree` is one `{ }` group whose inside reads as a
/// block, for the `block` fragment kind.
pub fn is_block(tree: &Tt, interner: &Interner) -> bool {
    match tree {
        Tt::Delim(Delim::Brace, inner, _) => block_inner(&mut Cur::new(inner, interner, true, 0)),
        _ => false,
    }
}

/// True when the cursor (after attributes and qualifiers) stands
/// at an item keyword.
fn starts_item_at(c: &Cur) -> bool {
    let mut j = c.i;
    loop {
        match tok_at(c.ts, j).map(|t| t.tok) {
            Some(Tok::Pound) if matches!(c.ts.get(j + 1), Some(Tt::Delim(Delim::Bracket, _, _))) => j += 2,
            Some(Tok::Pub) => {
                j += 1;
                if matches!(c.ts.get(j), Some(Tt::Delim(Delim::Paren, _, _))) {
                    j += 1;
                }
            }
            Some(Tok::Const) => {
                // `const NAME` is the item; `const fn` a qualifier.
                if matches!(tok_at(c.ts, j + 1).map(|t| t.tok), Some(Tok::Ident(_) | Tok::Underscore)) {
                    return true;
                }
                j += 1;
            }
            Some(Tok::Async | Tok::Unsafe | Tok::Extern) => j += 1,
            Some(Tok::Fn | Tok::Struct | Tok::Enum | Tok::Impl | Tok::Mod | Tok::Trait | Tok::Type | Tok::Static | Tok::Use) => {
                return true;
            }
            Some(t) if seg_text(t, c.interner).as_deref() == Some("macro_rules") => return true,
            Some(t) if seg_text(t, c.interner).as_deref() == Some("default") => j += 1,
            Some(t) if seg_text(t, c.interner).as_deref() == Some("union") => return true,
            _ => return false,
        }
    }
}

/// Skips a `where` clause: everything up to the item's `{ }` or
/// `;`. False when the clause is empty or never ends.
fn skip_where(c: &mut Cur) -> bool {
    if !c.eat(Tok::Where) {
        return true;
    }
    let start = c.i;
    while !c.done() {
        if matches!(c.tree(), Some(Tt::Delim(Delim::Brace, _, _))) || c.at(Tok::Semi) {
            return c.i > start;
        }
        c.i += 1;
    }
    c.i > start
}

/// Skips to just past the next top-level `;` (for `use` items).
fn skip_to_semi(c: &mut Cur) -> bool {
    let start = c.i;
    while !c.done() {
        if c.eat(Tok::Semi) {
            return c.i > start + 1;
        }
        c.i += 1;
    }
    false
}

/// Validates fn parameters: `self` forms, `pat: ty`, and `...`.
/// A bare type with no pattern stands only in a body-less
/// signature (`allow_bare`), never in a definition.
fn fn_params(inner: &[Tt], interner: &Interner, allow_bare: bool) -> bool {
    pieces_all(inner, |p| {
        if matches!(p, [Tt::Tok(t)] if t.tok == Tok::Ellipsis) {
            return true;
        }
        // A `self` form: `self`, `mut self`, `&self`, `&mut self`,
        // with an optional `: Type` after it.
        let self_at = p.iter().position(|t| matches!(t, Tt::Tok(x) if x.tok == Tok::SelfLower));
        if let Some(s) = self_at {
            let head_ok =
                p[..s].iter().all(|t| matches!(t, Tt::Tok(x) if matches!(x.tok, Tok::Amp | Tok::AndAnd | Tok::Mut | Tok::Lifetime(_))));
            let tail_ok = match p.get(s + 1) {
                None => true,
                Some(Tt::Tok(x)) if x.tok == Tok::Colon => is_ty(&p[s + 2..], interner),
                _ => false,
            };
            return head_ok && tail_ok;
        }
        match p.iter().position(|t| matches!(t, Tt::Tok(x) if x.tok == Tok::Colon)) {
            Some(k) if k >= 1 => {
                // The pattern may be a lone `_` for foreign and
                // trait signatures, where a bare type also stands.
                (is_pat(&p[..k], interner, false) || matches!(&p[..k], [Tt::Tok(t)] if t.tok == Tok::Underscore))
                    && is_ty(&p[k + 1..], interner)
            }
            _ => allow_bare && is_ty(p, interner),
        }
    })
}

/// True when the group after `pub` is a visibility restriction:
/// `crate`, `self`, `super`, or `in` and a module path.
fn restricted_vis(inner: &[Tt]) -> bool {
    match inner {
        [Tt::Tok(t)] => matches!(t.tok, Tok::Crate | Tok::SelfLower | Tok::Super),
        [Tt::Tok(t), rest @ ..] if t.tok == Tok::In => super::match_::mod_path(rest),
        _ => false,
    }
}

/// Validates struct-like named fields.
fn named_fields(inner: &[Tt], interner: &Interner) -> bool {
    pieces_all(inner, |p| {
        let mut s = 0;
        // Attributes and visibility before the field name.
        while matches!(p.get(s), Some(Tt::Tok(t)) if t.tok == Tok::Pound) && matches!(p.get(s + 1), Some(Tt::Delim(Delim::Bracket, _, _))) {
            s += 2;
        }
        if matches!(p.get(s), Some(Tt::Tok(t)) if t.tok == Tok::Pub) {
            s += 1;
            if let Some(Tt::Delim(Delim::Paren, inner, _)) = p.get(s) {
                if !restricted_vis(inner) {
                    return false;
                }
                s += 1;
            }
        }
        matches!(p.get(s), Some(Tt::Tok(t)) if matches!(t.tok, Tok::Ident(_)))
            && matches!(p.get(s + 1), Some(Tt::Tok(t)) if t.tok == Tok::Colon)
            && is_ty(&p[s + 2..], interner)
    })
}

/// Validates the types in a tuple field or variant list.
fn ty_pieces(inner: &[Tt], interner: &Interner) -> bool {
    pieces_all(inner, |p| {
        let mut s = 0;
        while matches!(p.get(s), Some(Tt::Tok(t)) if t.tok == Tok::Pound) && matches!(p.get(s + 1), Some(Tt::Delim(Delim::Bracket, _, _))) {
            s += 2;
        }
        if matches!(p.get(s), Some(Tt::Tok(t)) if t.tok == Tok::Pub) {
            s += 1;
            if matches!(p.get(s), Some(Tt::Delim(Delim::Paren, inner, _)) if restricted_vis(inner)) {
                s += 1;
            }
        }
        is_ty(&p[s..], interner)
    })
}

/// Parses one item at the cursor, advancing past it.
fn parse_item(c: &mut Cur) -> bool {
    if !c.ok_depth() {
        return false;
    }
    c.attrs();
    // Visibility: `pub(..)` must be a restriction here (rustc's E0704).
    if c.eat(Tok::Pub)
        && let Some(Tt::Delim(Delim::Paren, inner, _)) = c.tree()
    {
        if !restricted_vis(inner) {
            return false;
        }
        c.i += 1;
    }
    if c.word().as_deref() == Some("default") {
        c.bump();
    }
    // A `macro_rules!` definition is an item to the fragment parser.
    if c.word().as_deref() == Some("macro_rules") && tok_at(c.ts, c.i + 1).map(|t| t.tok) == Some(Tok::Bang) {
        c.bump();
        c.bump();
        if matches!(c.tok(), Some(t) if is_seg(t)) {
            c.bump();
        }
        return match c.tree() {
            Some(Tt::Delim(d, _, _)) => {
                let d = *d;
                c.i += 1;
                d == Delim::Brace || c.eat(Tok::Semi)
            }
            _ => false,
        };
    }
    // Qualifiers before `fn` (a `const` item is handled below,
    // since its next token names the constant).
    let mut saw_extern = false;
    loop {
        match c.tok() {
            Some(Tok::Async | Tok::Unsafe) => c.bump(),
            Some(Tok::Const) if !matches!(tok_at(c.ts, c.i + 1).map(|t| t.tok), Some(Tok::Ident(_) | Tok::Underscore)) => c.bump(),
            Some(Tok::Extern) => {
                // `extern crate` and an extern block are items of
                // their own, not fn qualifiers.
                if matches!(tok_at(c.ts, c.i + 1).map(|t| t.tok), Some(Tok::Crate))
                    || matches!(c.ts.get(c.i + 1), Some(Tt::Delim(Delim::Brace, _, _)))
                    || (matches!(tok_at(c.ts, c.i + 1).map(|t| t.tok), Some(Tok::Str(..)))
                        && matches!(c.ts.get(c.i + 2), Some(Tt::Delim(Delim::Brace, _, _))))
                {
                    break;
                }
                saw_extern = true;
                c.bump();
                if matches!(c.tok(), Some(Tok::Str(..))) {
                    c.bump();
                }
            }
            _ => break,
        }
    }
    let name = |c: &mut Cur| -> bool {
        if matches!(c.tok(), Some(t) if is_seg(t)) {
            c.bump();
            true
        } else {
            false
        }
    };
    match c.tok() {
        Some(Tok::Fn) => {
            c.bump();
            if !name(c) || !generic_params(c) {
                return false;
            }
            let Some(inner) = c.group(Delim::Paren) else { return false };
            let definition_params = fn_params(inner, c.interner, false);
            let signature_params = definition_params || fn_params(inner, c.interner, true);
            if !signature_params {
                return false;
            }
            if c.eat(Tok::Arrow) && !parse_ty(c) {
                return false;
            }
            if !skip_where(c) {
                return false;
            }
            if matches!(c.tree(), Some(Tt::Delim(Delim::Brace, _, _))) {
                // A definition's parameters need patterns.
                definition_params && parse_block(c)
            } else {
                c.eat(Tok::Semi)
            }
        }
        Some(Tok::Struct) => {
            c.bump();
            if !name(c) || !generic_params(c) || !skip_where(c) {
                return false;
            }
            parse_struct_tail(c)
        }
        _ if c.word().as_deref() == Some("union") => {
            c.bump();
            if !name(c) || !generic_params(c) || !skip_where(c) {
                return false;
            }
            match c.group(Delim::Brace) {
                Some(inner) => named_fields(inner, c.interner),
                None => false,
            }
        }
        Some(Tok::Enum) => {
            c.bump();
            if !name(c) || !generic_params(c) || !skip_where(c) {
                return false;
            }
            let Some(inner) = c.group(Delim::Brace) else { return false };
            pieces_all(inner, |p| {
                let mut s = 0;
                while matches!(p.get(s), Some(Tt::Tok(t)) if t.tok == Tok::Pound)
                    && matches!(p.get(s + 1), Some(Tt::Delim(Delim::Bracket, _, _)))
                {
                    s += 2;
                }
                if !matches!(p.get(s), Some(Tt::Tok(t)) if is_seg(t.tok)) {
                    return false;
                }
                s += 1;
                match p.get(s) {
                    Some(Tt::Delim(Delim::Paren, flds, _)) => {
                        s += 1;
                        if !ty_pieces(flds, c.interner) {
                            return false;
                        }
                    }
                    Some(Tt::Delim(Delim::Brace, flds, _)) => {
                        s += 1;
                        if !named_fields(flds, c.interner) {
                            return false;
                        }
                    }
                    _ => {}
                }
                match p.get(s) {
                    None => true,
                    Some(Tt::Tok(t)) if t.tok == Tok::Eq => s + 1 < p.len() && is_expr(&p[s + 1..], c.interner, true),
                    _ => false,
                }
            })
        }
        Some(Tok::Trait) => {
            c.bump();
            if c.word().as_deref() == Some("auto") {
                c.bump();
            }
            if !name(c) || !generic_params(c) {
                return false;
            }
            if c.eat(Tok::Colon) && !parse_bounds(c) {
                return false;
            }
            skip_where(c) && item_list(c)
        }
        Some(Tok::Impl) => {
            c.bump();
            if !generic_params(c) {
                return false;
            }
            c.eat(Tok::Bang);
            if !parse_ty(c) {
                return false;
            }
            if c.eat(Tok::For) && !parse_ty(c) {
                return false;
            }
            skip_where(c) && item_list(c)
        }
        Some(Tok::Type) => {
            c.bump();
            if !name(c) || !generic_params(c) {
                return false;
            }
            if c.eat(Tok::Colon) && !parse_bounds(c) {
                return false;
            }
            if !skip_where(c) {
                return false;
            }
            if c.eat(Tok::Eq) && !parse_ty(c) {
                return false;
            }
            c.eat(Tok::Semi)
        }
        Some(Tok::Const) => {
            c.bump();
            let named = matches!(c.tok(), Some(t) if is_seg(t)) || c.at(Tok::Underscore);
            if !named {
                return false;
            }
            c.bump();
            if !c.eat(Tok::Colon) || !parse_ty(c) {
                return false;
            }
            if c.eat(Tok::Eq) && !parse_expr_bp(c, 0) {
                return false;
            }
            c.eat(Tok::Semi)
        }
        Some(Tok::Static) => {
            c.bump();
            c.eat(Tok::Mut);
            if !name(c) || !c.eat(Tok::Colon) || !parse_ty(c) {
                return false;
            }
            if c.eat(Tok::Eq) && !parse_expr_bp(c, 0) {
                return false;
            }
            c.eat(Tok::Semi)
        }
        Some(Tok::Mod) => {
            c.bump();
            if !name(c) {
                return false;
            }
            if matches!(c.tree(), Some(Tt::Delim(Delim::Brace, _, _))) { item_list(c) } else { c.eat(Tok::Semi) }
        }
        Some(Tok::Use) => {
            c.bump();
            skip_to_semi(c)
        }
        Some(Tok::Extern) => {
            let _ = saw_extern;
            c.bump();
            if c.eat(Tok::Crate) {
                if !name(c) {
                    return false;
                }
                if c.eat(Tok::As) && !name(c) {
                    return false;
                }
                return c.eat(Tok::Semi);
            }
            if matches!(c.tok(), Some(Tok::Str(..))) {
                c.bump();
            }
            item_list(c)
        }
        _ => false,
    }
}

/// The tail of a struct item after its name and generics.
fn parse_struct_tail(c: &mut Cur) -> bool {
    match c.tree() {
        Some(Tt::Delim(Delim::Brace, _, _)) => match c.group(Delim::Brace) {
            Some(inner) => named_fields(inner, c.interner),
            None => false,
        },
        Some(Tt::Delim(Delim::Paren, _, _)) => match c.group(Delim::Paren) {
            Some(inner) => ty_pieces(inner, c.interner) && c.eat(Tok::Semi),
            None => false,
        },
        _ => c.eat(Tok::Semi),
    }
}

/// Validates an item list inside one `{ }` (trait, impl, module).
fn item_list(c: &mut Cur) -> bool {
    match c.group(Delim::Brace) {
        Some(inner) => {
            let mut sub = c.child(inner);
            while !sub.done() {
                if !parse_item(&mut sub) {
                    return false;
                }
            }
            true
        }
        None => false,
    }
}
