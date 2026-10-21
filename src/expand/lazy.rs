// Static init closures (W-STD-C): `static NAME: TY = PATH(|| BODY);`.
//
// A `static LazyLock` (or any static whose initializer is one call with a
// zero-parameter closure as its only argument) needs a fn pointer in static
// data: the closure coerces to `F = fn() -> T`. The const evaluator has fn
// item values (`ConstValue::FnPtr`), not closures, so this pass moves the
// closure body into a hidden fn right after the static, at the token level:
//
//     static NAME: TY = PATH(__lust_lazy$NAME);
//     fn __lust_lazy$NAME() -> T { BODY }
//
// `LazyLock::new(INIT)` and `LazyCell::new(INIT)` with a plain path `INIT`
// (`Default::default`, `HashMap::new`) hoist the same way, with the body
// `let f: fn() -> T = INIT; f()` (see `hoistable_path`).
//
// `T` is the closure's written return type, else the first type argument
// of the last `LazyLock<..>` / `LazyCell<..>` in `TY`; other statics are
// left alone (and reject in the const evaluator as before). It runs after
// macro expansion and before the item scanner and the parser, so the
// daemon's token scan and the Ast see the same fns in the same order.
//
// Rule zero: a closure there can capture nothing (a static initializer
// has no locals at that position), so the fn has the closure's meaning.
// The name holds a `$`, which no source identifier can, so user code
// cannot name the fn. Elided references in `T` get `'static`, the
// lifetime a static's type elides to.
use crate::diag::Span;
use crate::intern::Interner;
use crate::lexer::{Lexed, Tok, Token};

/// Rewrites every hoistable static init closure in `lexed`. A file with
/// no `static`, or with no `||` and no `LazyLock` / `LazyCell`, comes
/// back unchanged.
pub fn hoist_static_closures(lexed: Lexed, interner: &Interner) -> Lexed {
    let lexed = hoist_lazy_closures(lexed, interner);
    hoist_value_closures(lexed, interner)
}

fn hoist_lazy_closures(lexed: Lexed, interner: &Interner) -> Lexed {
    let toks = &lexed.tokens;
    let lazy_name = |t: &Token| matches!(t.tok, Tok::Ident(s) if matches!(interner.get(s), "LazyLock" | "LazyCell"));
    if !toks.iter().any(|t| t.tok == Tok::Static) || !toks.iter().any(|t| t.tok == Tok::OrOr || lazy_name(t)) {
        return lexed;
    }
    let mut out: Vec<Token> = Vec::with_capacity(toks.len() + 16);
    let mut i = 0;
    while i < toks.len() {
        if toks[i].tok == Tok::Static
            && let Some(h) = hoistable(toks, i, interner)
        {
            out.extend_from_slice(&toks[i..h.open + 1]);
            out.push(Token { tok: Tok::Ident(h.name), span: h.span });
            out.extend_from_slice(&toks[h.close..h.semi + 1]);
            out.extend(cfg_attrs(toks, i, interner));
            let sp = h.span;
            out.push(Token { tok: Tok::Fn, span: sp });
            out.push(Token { tok: Tok::Ident(h.name), span: sp });
            out.push(Token { tok: Tok::LParen, span: sp });
            out.push(Token { tok: Tok::RParen, span: sp });
            out.push(Token { tok: Tok::Arrow, span: sp });
            out.extend(h.ret);
            out.push(Token { tok: Tok::LBrace, span: sp });
            out.extend(h.body);
            out.push(Token { tok: Tok::RBrace, span: sp });
            i = h.semi + 1;
            continue;
        }
        out.push(toks[i].clone());
        i += 1;
    }
    Lexed { tokens: out, strings: lexed.strings }
}

/// One static whose initializer closure moves into a hidden fn.
struct Hoist {
    /// The hidden fn's name.
    name: crate::intern::Sym,
    /// Span for the synthetic tokens: the closure's `||`.
    span: Span,
    /// Token index of the call's `(` and `)`, and of the static's `;`.
    open: usize,
    close: usize,
    semi: usize,
    /// The hidden fn's body tokens.
    body: Vec<Token>,
    /// The hidden fn's return type tokens.
    ret: Vec<Token>,
}

/// The hoist for the `static` keyword at `at`, when the item has the
/// shape `static NAME: TY = PATH(<move> || BODY<,>);` (a trailing comma is allowed).
fn hoistable(toks: &[Token], at: usize, interner: &Interner) -> Option<Hoist> {
    let Tok::Ident(name) = toks.get(at + 1)?.tok else { return None }; // `static mut` stays
    if toks.get(at + 2)?.tok != Tok::Colon {
        return None;
    }
    let ty_start = at + 3;
    let eq = scan_to(toks, ty_start, true, |t| t == Tok::Eq)?;
    // The initializer is an expression: `<` and `>` there may be
    // comparisons (`.filter(|t| t.len() > 2)`), never brackets to count.
    let semi = scan_to(toks, eq + 1, false, |t| t == Tok::Semi)?;
    // PATH: identifiers and `::` (a turbofish is not supported here).
    let mut open = eq + 1;
    while matches!(toks.get(open)?.tok, Tok::Ident(_) | Tok::PathSep) {
        open += 1;
    }
    if open == eq + 1 || toks[open].tok != Tok::LParen {
        return None;
    }
    let close = semi - 1;
    if toks[close].tok != Tok::RParen || matching_close(toks, open)? != close {
        return None;
    }
    if let Some(h) = hoistable_path(toks, name, ty_start..eq, open, close, semi, interner) {
        return Some(h);
    }
    let mut k = open + 1;
    if toks[k].tok == Tok::Move {
        k += 1;
    }
    if toks.get(k)?.tok != Tok::OrOr {
        return None;
    }
    let span = toks[k].span;
    k += 1;
    // One argument only: after the closure comes `)` or a trailing
    // `,)` (`PATH(|| BODY,)`).
    let (ret, body) = if toks.get(k)?.tok == Tok::Arrow {
        // `|| -> R { .. }`: the body is the block after the written type.
        let lb = scan_to(toks, k + 1, true, |t| t == Tok::LBrace)?;
        let rb = matching_close(toks, lb)?;
        let trailing = rb + 2 == close && toks[rb + 1].tok == Tok::Comma;
        if lb >= close || !(rb + 1 == close || trailing) {
            return None;
        }
        (toks[k + 1..lb].to_vec(), lb..rb + 1)
    } else {
        let end = match scan_to(toks, k, false, |t| t == Tok::Comma) {
            Some(c) if c + 1 == close => c,
            Some(c) if c < close => return None,
            _ => close,
        };
        (lazy_value_ty(&toks[ty_start..eq], interner)?, k..end)
    };
    if body.is_empty() {
        return None;
    }
    let hidden = interner.intern(&format!("__lust_lazy${}", interner.get(name)));
    Some(Hoist { name: hidden, span, open, close, semi, body: toks[body].to_vec(), ret: static_lifetimes(ret, span, interner) })
}

/// The hoist for `static NAME: TY = LazyLock::new(INIT);` (or
/// `LazyCell::new`) whose `INIT` is a plain or qualified path
/// (`Default::default`, `HashMap::new`, a user fn, `<S as Default>::default`):
/// the hidden fn is
/// `{ let f: fn() -> T = INIT; f() }`. The written fn pointer type keeps
/// rustc's coercion of `INIT` to `F = fn() -> T` exact (a `fn() -> !` or
/// a `fn() -> &[u8; 2]` for `T = &[u8]` rejects, as there), and gives
/// a std fn with no item value its eta closure's place.
fn hoistable_path(
    toks: &[Token],
    name: crate::intern::Sym,
    ty: std::ops::Range<usize>,
    open: usize,
    close: usize,
    semi: usize,
    interner: &Interner,
) -> Option<Hoist> {
    let ctor = open >= ty.end + 4
        && matches!(toks[open - 1].tok, Tok::Ident(s) if interner.get(s) == "new")
        && toks[open - 2].tok == Tok::PathSep
        && matches!(toks[open - 3].tok, Tok::Ident(s) if matches!(interner.get(s), "LazyLock" | "LazyCell"));
    if !ctor {
        return None;
    }
    let mut end = close;
    if toks[end - 1].tok == Tok::Comma {
        end -= 1;
    }
    let init = &toks[open + 1..end];
    // A path, also with generic args (`key::<Rc<T>>`, whose `>>` is one
    // token; a comma only inside the angle brackets), and with a `crate`,
    // `super` or `self` segment (the hidden fn sits in the same module).
    let mut depth = 0i32;
    let path_like = !init.is_empty()
        && init.iter().all(|t| {
            match t.tok {
                Tok::Lt => depth += 1,
                Tok::Gt => depth -= 1,
                Tok::Shr => depth -= 2,
                Tok::Comma => return depth > 0,
                _ => {}
            }
            depth >= 0
                && matches!(
                    t.tok,
                    Tok::Ident(_) | Tok::Crate | Tok::Super | Tok::SelfLower | Tok::PathSep | Tok::Lt | Tok::Gt | Tok::Shr | Tok::As | Tok::Comma
                )
        })
        && depth == 0
        && matches!(init.last()?.tok, Tok::Ident(_) | Tok::Gt | Tok::Shr);
    if !path_like {
        return None;
    }
    let span = init[0].span;
    let ret = static_lifetimes(lazy_value_ty(&toks[ty], interner)?, span, interner);
    let f = interner.intern("__lust_lazy$f");
    let mut body = vec![
        Token { tok: Tok::Let, span },
        Token { tok: Tok::Ident(f), span },
        Token { tok: Tok::Colon, span },
        Token { tok: Tok::Fn, span },
        Token { tok: Tok::LParen, span },
        Token { tok: Tok::RParen, span },
        Token { tok: Tok::Arrow, span },
    ];
    body.extend(ret.iter().cloned());
    body.push(Token { tok: Tok::Eq, span });
    body.extend_from_slice(init);
    body.extend([
        Token { tok: Tok::Semi, span },
        Token { tok: Tok::Ident(f), span },
        Token { tok: Tok::LParen, span },
        Token { tok: Tok::RParen, span },
    ]);
    let hidden = interner.intern(&format!("__lust_lazy${}", interner.get(name)));
    Some(Hoist { name: hidden, span, open, close, semi, body, ret })
}

/// The first index at or after `from` whose token satisfies `want`, at
/// bracket depth 0 (parens, brackets, braces, and with `angles` angle
/// brackets: in a type, not in an expression), or None when the
/// enclosing group closes first.
fn scan_to(toks: &[Token], from: usize, angles: bool, want: impl Fn(Tok) -> bool) -> Option<usize> {
    let mut depth = 0i32;
    for (i, t) in toks.iter().enumerate().skip(from) {
        if depth == 0 && want(t.tok) {
            return Some(i);
        }
        match t.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::Lt if angles => depth += 1,
            Tok::Gt if angles => {
                depth -= 1;
                if depth < 0 {
                    return None;
                }
            }
            Tok::RParen | Tok::RBracket | Tok::RBrace => {
                depth -= 1;
                if depth < 0 {
                    return None;
                }
            }
            Tok::Eof => return None,
            _ => {}
        }
    }
    None
}

/// The index of the token closing the group opened at `open`.
fn matching_close(toks: &[Token], open: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (i, t) in toks.iter().enumerate().skip(open) {
        match t.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            Tok::Eof => return None,
            _ => {}
        }
    }
    None
}

/// `T` of the last `LazyLock<T, ..>` or `LazyCell<T, ..>` in a static's
/// type tokens.
fn lazy_value_ty(ty: &[Token], interner: &Interner) -> Option<Vec<Token>> {
    let at = ty.iter().rposition(|t| matches!(t.tok, Tok::Ident(s) if matches!(interner.get(s), "LazyLock" | "LazyCell")))?;
    if ty.get(at + 1)?.tok != Tok::Lt {
        return None;
    }
    let mut depth = 0i32;
    for (i, t) in ty.iter().enumerate().skip(at + 2) {
        match t.tok {
            Tok::Lt | Tok::LParen | Tok::LBracket => depth += 1,
            Tok::Gt | Tok::RParen | Tok::RBracket if depth > 0 => depth -= 1,
            Tok::Gt | Tok::Comma if depth == 0 => return if i > at + 2 { Some(ty[at + 2..i].to_vec()) } else { None },
            _ => {}
        }
    }
    None
}

/// Gives every elided reference in a return type the `'static` lifetime
/// (`&str` to `&'static str`, `'_` to `'static`), as the static's type
/// means them.
fn static_lifetimes(ty: Vec<Token>, span: Span, interner: &Interner) -> Vec<Token> {
    let st = Tok::Lifetime(interner.intern("static"));
    let mut out = Vec::with_capacity(ty.len() + 2);
    for (i, t) in ty.iter().enumerate() {
        let next_is_lifetime = matches!(ty.get(i + 1).map(|x| x.tok), Some(Tok::Lifetime(_)));
        match t.tok {
            Tok::Amp => {
                out.push(t.clone());
                if !next_is_lifetime {
                    out.push(Token { tok: st, span });
                }
            }
            // `&&T`: the outer `&` is always elided here.
            Tok::AndAnd => {
                out.push(Token { tok: Tok::Amp, span: t.span });
                out.push(Token { tok: st, span });
                out.push(Token { tok: Tok::Amp, span: t.span });
                if !next_is_lifetime {
                    out.push(Token { tok: st, span });
                }
            }
            Tok::Lifetime(s) if interner.get(s) == "_" => out.push(Token { tok: st, span: t.span }),
            _ => out.push(t.clone()),
        }
    }
    out
}

/// The `#[cfg(..)]` attributes in front of the `static` at `at` (after
/// any visibility), so the hidden fn exists exactly when the static does.
fn cfg_attrs(toks: &[Token], at: usize, interner: &Interner) -> Vec<Token> {
    // Step back over `pub`, `pub(crate)`, `pub(in path)`.
    let mut s = at;
    if s > 0 && toks[s - 1].tok == Tok::RParen {
        let mut j = s - 1;
        let mut depth = 0;
        loop {
            match toks[j].tok {
                Tok::RParen => depth += 1,
                Tok::LParen => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
            if j == 0 {
                return Vec::new();
            }
            j -= 1;
        }
        if j > 0 && toks[j - 1].tok == Tok::Pub {
            s = j - 1;
        }
    } else if s > 0 && toks[s - 1].tok == Tok::Pub {
        s -= 1;
    }
    // Then over `#[..]` groups, keeping the `cfg` ones in order.
    let mut groups: Vec<std::ops::Range<usize>> = Vec::new();
    while s >= 3 && toks[s - 1].tok == Tok::RBracket {
        let mut j = s - 1;
        let mut depth = 0;
        loop {
            match toks[j].tok {
                Tok::RBracket => depth += 1,
                Tok::LBracket => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
            if j == 0 {
                return Vec::new();
            }
            j -= 1;
        }
        if j == 0 || toks[j - 1].tok != Tok::Pound {
            break;
        }
        groups.push(j - 1..s);
        s = j - 1;
    }
    let mut out = Vec::new();
    for g in groups.into_iter().rev() {
        let is_cfg = matches!(toks.get(g.start + 2).map(|t| t.tok), Some(Tok::Ident(n)) if interner.get(n) == "cfg")
            && toks.get(g.start + 3).is_some_and(|t| t.tok == Tok::LParen);
        if is_cfg {
            out.extend_from_slice(&toks[g]);
        }
    }
    out
}

// Closures in const and static values (census-10): `const CASES: [Case; 2]
// = [Case { start: |b| .. }, ..];`, each closure coerced to a fn pointer
// field. The const evaluator runs no closure, and the closure has no body
// fn of its own until a checked fn holds it, so the initializer's tokens
// are copied into a hidden fn after the item:
//
//     const CASES: [Case; 2] = [Case { start: |b| .. }, ..];
//     fn __lust_cinit$CASES$LO() -> [Case; 2] { [Case { start: |b| .. }, ..] }
//
// The hidden fn checks as any fn does, so each closure gets its type from
// its position and a body fn (check/generics.rs `register_closures`). The
// copied tokens keep their spans, so a closure of the item's value and its
// copy in the fn have one span, and the evaluator names the copy's body fn
// for the value's closure (`ConstValue::ClosureFn`). `LO` is the item
// name's offset: two consts of one name in two blocks get two fns. The fn
// stands in for the initializer's own check (check/const_body.rs skips the
// item), and lowers as an initializer does (`Program::is_value_init_fn`).
// Elided references in the type get `'static`, the lifetime a const's type
// elides to, except inside fn pointer types and `Fn` sugar, whose elided
// lifetimes are their own.
//
// An item in an `impl` or `trait` body (an associated const) is left
// alone: a hidden fn there would be an associated fn.

/// The name prefix of the hidden fns that hold a const or static value
/// with closures.
pub const VALUE_INIT_PREFIX: &str = "__lust_cinit$";

/// Copies every const or static initializer that holds a closure into a
/// hidden fn after its item. A file with no `const` or `static`, or with
/// no `|`, comes back unchanged.
fn hoist_value_closures(lexed: Lexed, interner: &Interner) -> Lexed {
    let toks = &lexed.tokens;
    if !toks.iter().any(|t| matches!(t.tok, Tok::Const | Tok::Static)) || !toks.iter().any(|t| matches!(t.tok, Tok::Pipe | Tok::OrOr)) {
        return lexed;
    }
    // Hidden fns by the index of their item's `;`.
    let mut adds: Vec<(usize, Vec<Token>)> = Vec::new();
    // Per open `{`: true when it opens an `impl` or `trait` body.
    let mut stack: Vec<bool> = Vec::new();
    let mut header_assoc = false;
    let mut i = 0;
    while i < toks.len() {
        match toks[i].tok {
            Tok::Impl | Tok::Trait if item_start(toks, i) => header_assoc = true,
            Tok::LBrace => {
                stack.push(header_assoc);
                header_assoc = false;
            }
            Tok::RBrace => {
                stack.pop();
                header_assoc = false;
            }
            Tok::Semi => header_assoc = false,
            Tok::Const | Tok::Static if stack.last() != Some(&true) && item_start(toks, i) => {
                if let Some((semi, f)) = value_init_fn(toks, i, interner) {
                    adds.push((semi, f));
                    i = semi + 1;
                    header_assoc = false;
                    continue;
                }
            }
            _ => {}
        }
        i += 1;
    }
    if adds.is_empty() {
        return lexed;
    }
    let mut out: Vec<Token> = Vec::with_capacity(toks.len() + adds.iter().map(|(_, f)| f.len()).sum::<usize>());
    let mut next = 0;
    for (semi, f) in adds {
        out.extend_from_slice(&toks[next..semi + 1]);
        out.extend(f);
        next = semi + 1;
    }
    out.extend_from_slice(&toks[next..]);
    Lexed { tokens: out, strings: lexed.strings }
}

/// True when the keyword at `at` can start an item: it follows an item
/// boundary, an attribute, or a visibility.
fn item_start(toks: &[Token], at: usize) -> bool {
    at == 0 || matches!(toks[at - 1].tok, Tok::Semi | Tok::LBrace | Tok::RBrace | Tok::RBracket | Tok::Pub | Tok::RParen | Tok::Unsafe)
}

/// The hidden fn for the `const` or `static` at `at` when its item is
/// `const NAME: TY = INIT;` (or a non-`mut` static) and `INIT` holds a
/// closure: the index of the item's `;` and the fn's tokens.
fn value_init_fn(toks: &[Token], at: usize, interner: &Interner) -> Option<(usize, Vec<Token>)> {
    let Tok::Ident(name) = toks.get(at + 1)?.tok else { return None };
    if toks.get(at + 2)?.tok != Tok::Colon {
        return None;
    }
    let ty_start = at + 3;
    let eq = scan_to(toks, ty_start, true, |t| t == Tok::Eq)?;
    let semi = scan_to(toks, eq + 1, false, |t| t == Tok::Semi)?;
    let init = &toks[eq + 1..semi];
    // A closure starts an operand: `|`/`||` after `=`, an opening
    // bracket, a `,`, a `:` (a field), `=>`, `;`, `return` or `move`.
    let opens_operand = |k: usize| {
        let prev = if k == 0 { Tok::Eq } else { init[k - 1].tok };
        matches!(prev, Tok::Eq | Tok::LParen | Tok::LBracket | Tok::LBrace | Tok::Comma | Tok::Colon | Tok::FatArrow | Tok::Semi | Tok::Return | Tok::Move)
    };
    if !init.iter().enumerate().any(|(k, t)| matches!(t.tok, Tok::Pipe | Tok::OrOr) && opens_operand(k)) {
        return None;
    }
    let span = toks[at + 1].span;
    let hidden = interner.intern(&format!("{VALUE_INIT_PREFIX}{}${}", interner.get(name), span.lo));
    let mut f = cfg_attrs(toks, at, interner);
    f.extend([
        Token { tok: Tok::Fn, span },
        Token { tok: Tok::Ident(hidden), span },
        Token { tok: Tok::LParen, span },
        Token { tok: Tok::RParen, span },
        Token { tok: Tok::Arrow, span },
    ]);
    f.extend(value_lifetimes(&toks[ty_start..eq], span, interner));
    f.push(Token { tok: Tok::LBrace, span });
    f.extend_from_slice(init);
    f.push(Token { tok: Tok::RBrace, span });
    Some((semi, f))
}

/// `static_lifetimes` of a const's type, with the fn pointer types and
/// `Fn`/`FnMut`/`FnOnce` sugar in it copied as written: their elided
/// lifetimes are bound there, not `'static`.
fn value_lifetimes(ty: &[Token], span: Span, interner: &Interner) -> Vec<Token> {
    let mut out = Vec::with_capacity(ty.len() + 4);
    let mut plain: Vec<Token> = Vec::new();
    let mut i = 0;
    while i < ty.len() {
        let sugar = matches!(ty[i].tok, Tok::Ident(s) if matches!(interner.get(s), "Fn" | "FnMut" | "FnOnce"));
        if (ty[i].tok == Tok::Fn || sugar) && ty.get(i + 1).is_some_and(|t| t.tok == Tok::LParen) {
            let Some(close) = matching_close(ty, i + 1) else { break };
            let mut end = close + 1;
            if ty.get(end).is_some_and(|t| t.tok == Tok::Arrow) {
                end = ret_ty_end(ty, end + 1);
            }
            out.extend(static_lifetimes(std::mem::take(&mut plain), span, interner));
            out.extend_from_slice(&ty[i..end]);
            i = end;
            continue;
        }
        plain.push(ty[i].clone());
        i += 1;
    }
    out.extend(static_lifetimes(plain, span, interner));
    out
}

/// The end of the return type that starts at `from` in a type's tokens:
/// the first `,`, `;` or `=` outside its own brackets, or the bracket
/// (or `>`) that closes the group around it.
fn ret_ty_end(ty: &[Token], from: usize) -> usize {
    let mut depth = 0i32;
    for (i, t) in ty.iter().enumerate().skip(from) {
        match t.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace | Tok::Lt => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace | Tok::Gt if depth == 0 => return i,
            Tok::Shr if depth <= 1 => return i,
            Tok::RParen | Tok::RBracket | Tok::RBrace | Tok::Gt => depth -= 1,
            Tok::Shr => depth -= 2,
            Tok::Comma | Tok::Semi | Tok::Eq if depth == 0 => return i,
            _ => {}
        }
    }
    ty.len()
}
