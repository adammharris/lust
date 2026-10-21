// Recursive-descent parser with precedence climbing for binary operators.
// Rust syntax that lust rejects on purpose gets its own stable error code here:
// unsupported lifetime positions and user macros keep their original codes
// (L0203, L0401), `unsafe`
// and `async` keep theirs (L0404, L0405), and each AST v2 form whose parser
// lands later rejects with the Appendix A code for its area (docs/ARCH.md S3b).
use crate::ast::*;
use crate::diag::{Diag, Span, not_yet};
use crate::intern::{Interner, Known, Sym};
use crate::lexer::{Delim, Lexed, Tok, Token, TokenTree, decode_byte_char, decode_byte_str};

// Stable Appendix A codes for AST v2 forms the parser recognizes but does not
// build yet. Each code's registry row and explain page name its area.
#[allow(dead_code)] // Module forms parse now; the resolver rejects the rest.
const C_MOD: &str = "L0505"; // modules, imports, and module paths
const C_ATTR: &str = "L0522"; // cfg and known-but-unhandled attributes
const C_TY: &str = "L0602"; // type forms and type aliases
const C_TRAIT: &str = "L0614"; // traits, generics, and where clauses
const C_ASSOC: &str = "L0621"; // associated items and qualified paths
const C_CONST: &str = "L0632"; // const and static items, const generics
const C_LIT: &str = "L0641"; // C string literals and other std-surface syntax
#[allow(dead_code)] // Typed receivers parse now; collect rejects them until method resolution lands.
const C_METHOD: &str = "L0721"; // method and receiver forms
const C_EXTERN: &str = "L0810"; // extern blocks and foreign items
const C_CORE: &str = "L0820"; // core expression, pattern, and statement forms

fn unsafe_error(span: Span) -> Diag {
    Diag::new("L0404", span, "`unsafe` is not supported", "Remove the unsafe code.")
}

fn async_error(span: Span) -> Diag {
    Diag::new("L0405", span, "`async` is not supported", "Use std::thread and channels.")
}

type PResult<T> = Result<T, Diag>;

mod attrs;
mod hrtb;

/// The depth of each arena node built so far (1 for a leaf, else one
/// more than its deepest child), index-aligned with the `Ast` arenas.
/// Nodes that were already in the `Ast` when this parser started (a
/// `parse_body` append) have no entry and read as 1; they were guarded
/// by the parse that built them.
#[derive(Default)]
struct Depths {
    exprs: Vec<u32>,
    tys: Vec<u32>,
    pats: Vec<u32>,
    blocks: Vec<u32>,
}

pub struct Parser<'a> {
    toks: &'a [Token],
    pos: usize,
    /// The `(` of each parenthesized expression (outermost), which the
    /// AST drops: a binary, cast, or postfix expression that starts with
    /// one spans from it, as in rustc (panic locations read it).
    paren_lo: std::collections::HashMap<u32, Span>,
    /// Types written in parentheses, by TyId (see `Ast::paren_tys`).
    paren_tys: Vec<u32>,
    ast: Ast,
    interner: &'a Interner,
    known: &'a Known,
    /// Added to string-literal token indexes: where this token list's strings start in the AST.
    str_base: u32,
    /// Current nesting depth, capped so pathological input cannot overflow the stack.
    depth: u32,
    /// The first form (by span) that parses into AST v2 shapes but
    /// later stages do not support yet: the parser builds the shape
    /// and records the reject it used to emit on sight, so the
    /// error a user sees is still the first one in the file.
    /// `parse` returns it after the parse, or in place of a later
    /// hard error.
    deferred: Option<Diag>,
    /// True while parsing an `if` or `while` condition, where `let` may
    /// appear as a chain element.
    let_ok: bool,
    /// `#[allow(..)]`, `#[warn(..)]`, and `#[expect(..)]` attributes of
    /// enclosing scopes (crate and module inner attrs, outer attrs on enclosing `mod`/`impl`/`trait` items,
    /// impl and trait inner attrs). Every `FnDef` parsed inherits a copy,
    /// which is how the overflow lint sees a scope-level allow. Frames
    /// are length marks: push by extending, pop by truncating.
    scope_allows: Vec<Attr>,
    /// Set by an expression context where Rust permits inner attributes
    /// at the start of a block (a statement or block tail, a call, array,
    /// or tuple element). Taken by the next prefix or block parse, so a
    /// nested subexpression does not inherit it.
    block_inner_ok: bool,
    /// Arena node depths, for the `MAX_AST_DEPTH` guard in `push_expr`.
    depths: Depths,
    /// True for a cfg-disabled syntax check (`check_cfg_syntax`): the
    /// parse must report grammar errors only, as rustc does before it
    /// strips disabled code. Unsupported-but-valid forms, unknown
    /// attributes, and macro calls do not reject in this mode; a macro
    /// call is one opaque node whose body is not parsed.
    cfg_syntax: bool,
    /// True while a cfg syntax check parses one foreign item of an
    /// extern block, where a variadic `...` parameter is grammar.
    cfg_foreign: bool,
    /// The second half of a token split in two, still to be read: the
    /// `=` of a `>=` consumed as the `>` that closes generic arguments,
    /// or the second `<` of a `<<` consumed as the `<` that opens them
    /// (`Extend<<T as Tr>::Item>`). The lexer makes each one token;
    /// rustc splits it in these positions.
    split: Option<(Tok, Span)>,
    /// True inside a fn body or a const value: an anonymous const there
    /// is checked with its body, so it gets no `Ast::anon_consts` entry.
    in_body: bool,
}

/// The deepest nesting lust parses (parentheses, prefix operators, blocks, types,
/// patterns, operator or method chains, else-if chains, assignments, and closures).
/// Real code stays far below this.
const MAX_DEPTH: u32 = 2000;

/// The deepest AST lust accepts, counting every node on the longest
/// path (expressions, types, patterns, and blocks). This bounds what
/// combinations of the per-shape `MAX_DEPTH` caps can build: a chain
/// of 2000 whose first term holds another parenthesized chain of 2000,
/// repeated, is far deeper than either cap alone, and every later pass
/// walks that depth. Later passes run on `pool::STACK_SIZE` stacks,
/// which hold this depth with a wide margin; past it the parser
/// rejects with L9001 instead of letting a later pass overflow.
const MAX_AST_DEPTH: u32 = 16384;

/// Parses a whole file (or chunk) into an `Ast`. Stops at the first error.
pub fn parse(lexed: &Lexed, interner: &Interner, known: &Known) -> PResult<Ast> {
    parse_tokens(&lexed.tokens, lexed.strings.clone(), interner, known, &[], false)
}

/// The file-level `allow` inner attributes a whole parse of `lexed`
/// scopes over its items, read from the leading inner run only. A
/// caller that parses one file in pieces (driver chunks, resolver
/// segments) seeds each later piece with this list, so a piece parse
/// builds the same item attributes as the parse in place. An error
/// in the run reads as no allows; the real parse reports it.
pub fn leading_allows(lexed: &Lexed, interner: &Interner, known: &Known) -> Vec<Attr> {
    let mut p = Parser {
        toks: &lexed.tokens,
        pos: 0,
        paren_lo: Default::default(),
        paren_tys: Vec::new(),
        ast: Ast::default(),
        interner,
        known,
        str_base: 0,
        depth: 0,
        deferred: None,
        let_ok: false,
        scope_allows: Vec::new(),
        block_inner_ok: false,
        depths: Depths::default(),
        cfg_syntax: false,
        cfg_foreign: false,
        split: None,
        in_body: false,
    };
    match p.inner_attributes() {
        Ok(inner) => inner.attrs.iter().filter(|a| is_allow(a, known)).cloned().collect(),
        Err(_) => Vec::new(),
    }
}

/// Like `parse`, for a piece of a file after its first piece: items
/// start under `seed_allows` (from `leading_allows`), exactly as a
/// whole parse scopes the file's inner allows over them. A leading
/// inner run in the piece itself still wins, as in `parse`.
pub fn parse_seeded(lexed: &Lexed, interner: &Interner, known: &Known, seed_allows: &[Attr]) -> PResult<Ast> {
    parse_tokens(&lexed.tokens, lexed.strings.clone(), interner, known, seed_allows, false)
}

/// Parses the whole items in `lexed.tokens[range]` into their own `Ast`, as `parse` parses
/// them in place. The resolver parses a big file in item segments in parallel this way
/// (`resolve::worklist::item_segments`). The `Ast` holds only the strings its tokens name
/// (`Tok::string_indices`), re-indexed from zero, so it stands alone like any chunk `Ast`.
pub fn parse_items(lexed: &Lexed, range: std::ops::Range<usize>, interner: &Interner, known: &Known) -> PResult<Ast> {
    parse_items_seeded(lexed, range, interner, known, &[])
}

/// Like `parse_items`, for a segment after the file's first: items
/// start under `seed_allows` (from `leading_allows` on the whole
/// file), as `parse_seeded` does for chunks.
pub fn parse_items_seeded(
    lexed: &Lexed,
    range: std::ops::Range<usize>,
    interner: &Interner,
    known: &Known,
    seed_allows: &[Attr],
) -> PResult<Ast> {
    let toks = &lexed.tokens[range];
    let lo = toks.iter().flat_map(|t| t.tok.string_indices()).min().unwrap_or(0);
    let hi = toks.iter().flat_map(|t| t.tok.string_indices()).max().map_or(lo, |i| i + 1);
    let mut v: Vec<Token> = toks
        .iter()
        .map(|&t| {
            let mut t = t;
            for i in t.tok.string_indices_mut().into_iter().flatten() {
                *i -= lo;
            }
            t
        })
        .collect();
    if v.last().map(|t| t.tok) != Some(Tok::Eof) {
        let end = v.last().map_or(Span::default(), |t| t.span);
        v.push(Token { tok: Tok::Eof, span: Span { lo: end.hi, ..end } });
    }
    parse_tokens(&v, lexed.strings[lo as usize..hi as usize].to_vec(), interner, known, seed_allows, false)
}

/// The item loop of `parse` over one token list (ending in `Eof`) and its string table.
fn parse_tokens(
    toks: &[Token],
    strings: Vec<String>,
    interner: &Interner,
    known: &Known,
    seed_allows: &[Attr],
    cfg_syntax: bool,
) -> PResult<Ast> {
    let mut p = Parser {
        toks,
        pos: 0,
        paren_lo: Default::default(),
        paren_tys: Vec::new(),
        ast: Ast::default(),
        interner,
        known,
        str_base: 0,
        depth: 0,
        deferred: None,
        let_ok: false,
        scope_allows: seed_allows.to_vec(),
        block_inner_ok: false,
        depths: Depths::default(),
        cfg_syntax,
        cfg_foreign: false,
        split: None,
        in_body: false,
    };
    p.ast.strings = strings;
    p.ast.reserve_for_tokens(toks.len());
    // Inner attributes are permitted only here, before the first item
    // (and before any outer attribute): they scope over the whole file.
    // A seeded piece with no inner run of its own keeps the seed, so its
    // items carry the same allows as in a whole parse.
    match p.inner_attributes() {
        Ok(inner) => {
            attrs::check_target(&inner.attrs, "crates", 0, interner)?;
            if !inner.attrs.is_empty() {
                p.scope_allows = inner.attrs.iter().filter(|a| is_allow(a, known)).cloned().collect();
            }
            p.ast.inner_attrs = inner.attrs;
        }
        Err(hard) => return Err(hard),
    }
    while p.peek() != Tok::Eof {
        let before = p.pos;
        let item = match p.item() {
            Ok(item) => item,
            Err(hard) => return Err(p.earlier(hard)),
        };
        if let Some(item) = item {
            p.ast.items.push(item);
        }
        // No parse loop may spin in place on bad input: each round must consume a token.
        if p.pos == before {
            return Err(p.earlier(syntax(p.span(), format!("expected an item, found {}", tok_name(p.peek())))));
        }
    }
    if let Some(d) = p.deferred.take() {
        return Err(d);
    }
    p.finish_parens();
    Ok(p.ast)
}

/// A parsed function body: its block, and its expression and pattern ranges.
pub type ParsedBody = (BlockId, (u32, u32), (u32, u32));

/// What one run of attributes in front of an item or part of an item yielded:
/// the derive list and `#[test]` flag today's stages read, plus the recorded
/// attributes later stages will read.
#[derive(Default)]
struct ParsedAttrs {
    derives: Vec<(Sym, Span)>,
    is_test: bool,
    attrs: Vec<Attr>,
}

/// Attributes the resolver reads (docs/ARCH.md section 1.6): parsed and
/// recorded like `derive`, then honored by cfg stripping and module
/// loading. `cfg!` the macro is a separate form and stays with W-MACRO.
const RESOLVE_ATTRS: &[&str] = &["cfg", "cfg_attr", "path", "macro_use", "macro_export", "no_implicit_prelude"];

/// The attributes `thread_local!` puts on each static it declares
/// (expand/builtin.rs), lazy and `const { .. }` form. No source text can
/// spell these names, so only that expansion makes them; collect reads
/// them (check/tls.rs).
pub const TLS_ATTR: &str = "thread_local!";
pub const TLS_CONST_ATTR: &str = "thread_local!const";

/// Rust attribute names lust knows by name but does not handle yet
/// (docs/ARCH.md section 1.6 lists what each later package must honor).
/// These reject with L0522; any other name rejects with L0402.
const KNOWN_ATTRS: &[&str] = &[
    "repr",
    "inline",
    "cold",
    "must_use",
    "track_caller",
    "deprecated",
    "doc",
    "bench",
    "default",
    "target_feature",
    "link_section",
    "export_name",
    "link",
    "no_mangle",
    "no_link",
    "crate_type",
    "crate_name",
    "recursion_limit",
    "type_length_limit",
    "feature",
];

/// Parses one function body (`tokens` runs from its `{` to its `}`) and appends it to `ast`.
/// Returns the body block and the new expression and pattern ranges for the function.
pub fn parse_body(tokens: &[Token], strings: &[String], ast: &mut Ast, interner: &Interner, known: &Known) -> PResult<ParsedBody> {
    parse_body_seeded(tokens, strings, ast, interner, known, &[])
}

/// `parse_body` under the enclosing scopes' `allow` attributes
/// (`scope_allows`), which a whole parse seeds into each nested fn's
/// attributes: the body patch re-parses a body whose fn sits under them.
pub fn parse_body_seeded(
    tokens: &[Token],
    strings: &[String],
    ast: &mut Ast,
    interner: &Interner,
    known: &Known,
    seed_allows: &[Attr],
) -> PResult<ParsedBody> {
    let mut toks = tokens.to_vec();
    let end = tokens.last().map_or(Span::default(), |t| t.span);
    toks.push(Token { tok: Tok::Eof, span: Span { lo: end.hi, ..end } });
    let str_base = ast.strings.len() as u32;
    ast.strings.extend_from_slice(strings);
    let mut p = Parser {
        toks: &toks,
        pos: 0,
        paren_lo: Default::default(),
        paren_tys: Vec::new(),
        ast: std::mem::take(ast),
        interner,
        known,
        str_base,
        depth: 0,
        deferred: None,
        let_ok: false,
        scope_allows: seed_allows.to_vec(),
        block_inner_ok: false,
        depths: Depths::default(),
        cfg_syntax: false,
        cfg_foreign: false,
        split: None,
        in_body: false,
    };
    let (e0, p0) = (p.ast.exprs.len() as u32, p.ast.pats.len() as u32);
    // A fn body block permits inner attributes at its start.
    p.block_inner_ok = true;
    p.in_body = true;
    let body = p.block();
    let ranges = ((e0, p.ast.exprs.len() as u32), (p0, p.ast.pats.len() as u32));
    let deferred = p.deferred.take();
    p.finish_parens();
    *ast = p.ast;
    let body = match (body, deferred) {
        (Err(hard), Some(d)) if d.span.lo <= hard.span.lo => return Err(d),
        (Ok(_), Some(d)) => return Err(d),
        (body, _) => body?,
    };
    Ok((body, ranges.0, ranges.1))
}

/// Fragment probes for macro matching (src/expand, ARCH 6.2): each returns
/// true when `toks` parses as exactly one fragment of the named kind with
/// this parser. `toks` has no final `Eof`; one is added. String-literal
/// tokens in `toks` index into `strings`, as in a `Lexed`.
fn probe_with(toks: &[Token], strings: &[String], interner: &Interner, known: &Known, f: impl FnOnce(&mut Parser) -> bool) -> bool {
    let mut v: Vec<Token> = toks.to_vec();
    let end = toks.last().map_or(Span::default(), |t| t.span);
    v.push(Token { tok: Tok::Eof, span: Span { lo: end.hi, ..end } });
    let mut ast = Ast::default();
    ast.strings = strings.to_vec();
    let mut p = Parser {
        toks: &v,
        pos: 0,
        paren_lo: Default::default(),
        paren_tys: Vec::new(),
        ast,
        interner,
        known,
        str_base: 0,
        depth: 0,
        deferred: None,
        let_ok: false,
        scope_allows: Vec::new(),
        block_inner_ok: false,
        depths: Depths::default(),
        cfg_syntax: false,
        cfg_foreign: false,
        split: None,
        in_body: false,
    };
    f(&mut p)
}

/// True when `toks` is exactly one expression.
pub fn probe_expr(toks: &[Token], strings: &[String], interner: &Interner, known: &Known) -> bool {
    probe_with(toks, strings, interner, known, |p| p.expr().is_ok() && p.peek() == Tok::Eof)
}

/// How many leading tokens of `toks` one greedy expression parse
/// consumes (Ok), or how far it read when no expression parses there
/// (Err). The matcher uses this as rustc's fragment parser does (one
/// parse, no trying every end), and reads the position to tell whether
/// a parse of a prefix reads the same as one of the whole input.
/// Added for W-MACRO.
pub fn probe_expr_end(toks: &[Token], strings: &[String], interner: &Interner, known: &Known) -> Result<usize, usize> {
    let mut v: Vec<Token> = toks.to_vec();
    let end = toks.last().map_or(Span::default(), |t| t.span);
    v.push(Token { tok: Tok::Eof, span: Span { lo: end.hi, ..end } });
    let mut ast = Ast::default();
    ast.strings = strings.to_vec();
    let mut p = Parser {
        toks: &v,
        pos: 0,
        paren_lo: Default::default(),
        paren_tys: Vec::new(),
        ast,
        interner,
        known,
        str_base: 0,
        depth: 0,
        deferred: None,
        let_ok: false,
        scope_allows: Vec::new(),
        block_inner_ok: false,
        depths: Depths::default(),
        cfg_syntax: false,
        cfg_foreign: false,
        split: None,
        in_body: false,
    };
    match p.expr() {
        Ok(_) => Ok(p.pos),
        Err(_) => Err(p.pos),
    }
}

/// True when `toks` is exactly one type.
pub fn probe_ty(toks: &[Token], strings: &[String], interner: &Interner, known: &Known) -> bool {
    probe_with(toks, strings, interner, known, |p| p.ty().is_ok() && p.peek() == Tok::Eof)
}

/// True when `toks` is exactly one pattern.
pub fn probe_pat(toks: &[Token], strings: &[String], interner: &Interner, known: &Known) -> bool {
    probe_with(toks, strings, interner, known, |p| p.pattern().is_ok() && p.peek() == Tok::Eof)
}

/// True when `toks` (braces included) is exactly one block.
pub fn probe_block(toks: &[Token], strings: &[String], interner: &Interner, known: &Known) -> bool {
    probe_with(toks, strings, interner, known, |p| {
        // A `block` fragment may start with inner attributes, as in rustc.
        p.block_inner_ok = true;
        p.block().is_ok() && p.peek() == Tok::Eof
    })
}

/// True when `toks` is exactly one statement: wrapped in a block it parses
/// as one statement (an expression statement without `;` becomes the block
/// tail, which still counts as the one statement rustc's `stmt` fragment
/// accepts). A trailing `;` in `toks` is the caller's to include or not.
pub fn probe_stmt(toks: &[Token], strings: &[String], interner: &Interner, known: &Known) -> bool {
    let span = toks.first().map_or(Span::default(), |t| t.span);
    let mut wrapped = Vec::with_capacity(toks.len() + 2);
    wrapped.push(Token { tok: Tok::LBrace, span });
    wrapped.extend_from_slice(toks);
    wrapped.push(Token { tok: Tok::RBrace, span });
    probe_with(&wrapped, strings, interner, known, |p| match p.block() {
        Ok(b) if p.peek() == Tok::Eof => {
            let block = p.ast.block(b);
            block.stmts.len() + usize::from(block.tail.is_some()) == 1
        }
        _ => false,
    })
}

/// Hint for `check_cfg_syntax`: how the expander bounded the disabled
/// node. An item-shaped node tries item contexts first; any other node
/// tries statement contexts first. Every other context still runs when
/// the early ones fail with a syntax error.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CfgSyntaxHint {
    Item,
    Node,
}

/// Syntax-checks one cfg-disabled node, as rustc parses all code before
/// it strips disabled items: grammar errors (L0001) reject, while name,
/// type, and unsupported-form errors do not. `toks` is the flattened
/// node including its attribute run, with no final `Eof`; string tokens
/// index `strings`. The node is parsed inside small wrapper templates,
/// one per grammar position a cfg can sit in (item, impl or trait item,
/// statement, field, variant, match arm, and so on), and it is clean
/// when any one position parses it or stops only at an unsupported
/// form this parser cannot build (a non-L0001 reject, whose tail this
/// check cannot see past). No name resolution or type check runs, and
/// the built AST is dropped. A node in a brace group (`in_brace`: a file,
/// module, block, or braced body) is never a tuple field, a
/// comma-separated expression, or a type, so those positions are not
/// tried there (`#[cfg(any())] pub default` is no tuple field).
pub fn check_cfg_syntax(toks: &[Token], strings: &[String], interner: &Interner, known: &Known, hint: CfgSyntaxHint, in_brace: bool) -> PResult<()> {
    if toks.iter().all(|t| t.tok == Tok::Eof) {
        return Ok(());
    }
    // Remap string indices to a small local table so each trial parse
    // does not clone the file's whole string table.
    let mut used: Vec<u32> = toks.iter().flat_map(|t| t.tok.string_indices()).collect();
    used.sort_unstable();
    used.dedup();
    let local_strings: Vec<String> = used.iter().map(|&i| strings.get(i as usize).cloned().unwrap_or_default()).collect();
    let node: Vec<Token> = toks
        .iter()
        .filter(|t| t.tok != Tok::Eof)
        .map(|&t| {
            let mut t = t;
            for i in t.tok.string_indices_mut().into_iter().flatten() {
                *i = used.binary_search(i).unwrap_or(0) as u32;
            }
            t
        })
        .collect();
    if node.is_empty() {
        return Ok(());
    }
    let first_span = node.first().map_or(Span::default(), |t| t.span);
    let last_span = node.last().map_or(Span::default(), |t| t.span);
    // Wrapper templates by grammar position, as (prefix, suffix) source.
    const ITEMS: (&str, &str) = ("", "");
    const IMPL_ITEMS: (&str, &str) = ("struct CfgS; impl CfgS {", "}");
    const TRAIT_ITEMS: (&str, &str) = ("trait CfgT {", "}");
    const STMT: (&str, &str) = ("fn cfgf() {", "}");
    const ARM: (&str, &str) = ("fn cfgf() { match 0 {", "} }");
    const FIELD: (&str, &str) = ("struct CfgS {", "}");
    const TUPLE_FIELD: (&str, &str) = ("struct CfgS(", ");");
    const VARIANT: (&str, &str) = ("enum CfgE {", "}");
    const PARAM: (&str, &str) = ("fn cfgf(", ") {}");
    const EXPR_COMMA: (&str, &str) = ("fn cfgf() { let _ = [", "]; }");
    const LIT_FIELD: (&str, &str) = ("fn cfgf() { let _ = CfgS {", "}; }");
    const PAT_FIELD: (&str, &str) = ("fn cfgf() { let CfgS {", ".. } = x; }");
    const GENERIC: (&str, &str) = ("fn cfgf<", ">() {}");
    const TYPE: (&str, &str) = ("type CfgA = ", ";");
    const PATTERN: (&str, &str) = ("fn cfgf() { let ", " = x; }");
    const WHERE_PRED: (&str, &str) = ("fn cfgf() where ", " {}");
    let mut order: Vec<(&str, &str)> = match hint {
        CfgSyntaxHint::Item => vec![
            ITEMS,
            IMPL_ITEMS,
            TRAIT_ITEMS,
            STMT,
            ARM,
            FIELD,
            VARIANT,
            PARAM,
            TUPLE_FIELD,
            LIT_FIELD,
            PAT_FIELD,
            EXPR_COMMA,
            GENERIC,
            TYPE,
            PATTERN,
            WHERE_PRED,
        ],
        CfgSyntaxHint::Node => vec![
            STMT,
            ARM,
            ITEMS,
            IMPL_ITEMS,
            TRAIT_ITEMS,
            FIELD,
            PARAM,
            TUPLE_FIELD,
            VARIANT,
            LIT_FIELD,
            PAT_FIELD,
            EXPR_COMMA,
            GENERIC,
            TYPE,
            PATTERN,
            WHERE_PRED,
        ],
    };
    if in_brace {
        order.retain(|c| ![TUPLE_FIELD, EXPR_COMMA, TYPE].contains(c));
    }
    // A top-level `=>` is a match arm wherever the hint came from.
    let mut depth = 0usize;
    let mut has_arm = false;
    for t in &node {
        match t.tok {
            Tok::LParen | Tok::LBrace | Tok::LBracket => depth += 1,
            Tok::RParen | Tok::RBrace | Tok::RBracket => depth = depth.saturating_sub(1),
            Tok::FatArrow if depth == 0 => has_arm = true,
            _ => {}
        }
    }
    if has_arm {
        order.retain(|c| *c != ARM);
        order.insert(0, ARM);
    }
    let template_toks = |src: &str, span: Span| -> Vec<Token> {
        if src.is_empty() {
            return Vec::new();
        }
        match crate::lexer::lex(src, span.file, 0, interner) {
            Ok(lexed) => lexed
                .tokens
                .into_iter()
                .filter(|t| t.tok != Tok::Eof)
                .map(|mut t| {
                    t.span = span;
                    t
                })
                .collect(),
            Err(_) => Vec::new(),
        }
    };
    let mut first_err: Option<Diag> = None;
    for (prefix, suffix) in order {
        let mut trial = template_toks(prefix, first_span);
        trial.extend_from_slice(&node);
        trial.extend(template_toks(suffix, last_span));
        trial.push(Token { tok: Tok::Eof, span: Span { lo: last_span.hi, ..last_span } });
        match parse_tokens(&trial, local_strings.clone(), interner, known, &[], true) {
            Ok(_) => return Ok(()),
            Err(d) if d.code != "L0001" => return Ok(()),
            Err(d) => {
                if first_err.is_none() {
                    first_err = Some(d);
                }
            }
        }
    }
    Err(first_err.unwrap_or_else(|| syntax(first_span, "invalid syntax in cfg-disabled code")))
}

/// Converts a flat token slice into nested token trees. Unbalanced input
/// nests on a best-effort basis; attribute contents are stored, not checked.
fn token_trees(toks: &[Token]) -> Vec<TokenTree> {
    fn delim_of(t: Tok) -> Option<Delim> {
        match t {
            Tok::LParen => Some(Delim::Paren),
            Tok::LBracket => Some(Delim::Bracket),
            Tok::LBrace => Some(Delim::Brace),
            _ => None,
        }
    }
    fn closes(open: Delim, t: Tok) -> bool {
        matches!((open, t), (Delim::Paren, Tok::RParen) | (Delim::Bracket, Tok::RBracket) | (Delim::Brace, Tok::RBrace))
    }
    fn build(toks: &[Token], pos: &mut usize, close: Option<Delim>, depth: u32) -> Vec<TokenTree> {
        let mut out = Vec::new();
        while let Some(t) = toks.get(*pos) {
            if close.is_some_and(|d| closes(d, t.tok)) {
                *pos += 1;
                break;
            }
            *pos += 1;
            if let Some(d) = delim_of(t.tok).filter(|_| depth < MAX_DEPTH) {
                let inner = build(toks, pos, Some(d), depth + 1);
                out.push(TokenTree::Delim(d, inner, t.span));
            } else {
                out.push(TokenTree::Token(*t));
            }
        }
        out
    }
    let mut pos = 0;
    build(toks, &mut pos, None, 0)
}

/// A width or precision a format spec takes from an argument: `name$`,
/// `N$`, or (precision only) `*`, the next positional argument.
enum FmtCount {
    Name(String),
    Index(usize),
    Next,
}

/// Parses one format spec (the text after the `:`), with the width and
/// precision it takes from arguments. `Err(true)` is a form Rust has but
/// the subset does not; `Err(false)` is invalid in Rust.
fn parse_fmt_spec(fmt: &str) -> Result<(FmtSpec, Option<FmtCount>, Option<FmtCount>), bool> {
    let mut s = FmtSpec::default();
    let cs: Vec<char> = fmt.chars().collect();
    let mut i = 0usize;
    let digit_run = |cs: &[char], mut j: usize| -> (Option<u32>, usize) {
        let mut v: u64 = 0;
        let start = j;
        while j < cs.len() && cs[j].is_ascii_digit() {
            v = v.saturating_mul(10).saturating_add(cs[j] as u64 - '0' as u64);
            j += 1;
        }
        (if j > start { Some(v.min(u32::MAX as u64) as u32) } else { None }, j)
    };
    // [[fill]align]
    if i + 1 < cs.len() && matches!(cs[i + 1], '<' | '>' | '^') && cs[i] != '{' && cs[i] != '}' {
        s.fill = cs[i] as u32;
        s.align = cs[i + 1] as u8;
        i += 2;
    } else if i < cs.len() && matches!(cs[i], '<' | '>' | '^') {
        s.align = cs[i] as u8;
        i += 1;
    }
    // [sign]
    if i < cs.len() && cs[i] == '+' {
        s.plus = true;
        i += 1;
    } else if i < cs.len() && cs[i] == '-' {
        s.minus = true;
        i += 1;
    }
    // [#]
    if i < cs.len() && cs[i] == '#' {
        s.alt = true;
        i += 1;
    }
    // [0] (but `0$` is a width from argument 0)
    if i < cs.len() && cs[i] == '0' && cs.get(i + 1) != Some(&'$') {
        s.zero = true;
        i += 1;
    }
    // A count from an argument: `name$` or `N$`, with its end.
    let count_arg = |cs: &[char], j: usize| -> Option<(FmtCount, usize)> {
        let mut k = j;
        while k < cs.len() && (cs[k].is_alphanumeric() || cs[k] == '_') {
            k += 1;
        }
        if k == j || cs.get(k) != Some(&'$') {
            return None;
        }
        let text: String = cs[j..k].iter().collect();
        if cs[j].is_ascii_digit() {
            text.parse().ok().map(|n| (FmtCount::Index(n), k + 1))
        } else {
            Some((FmtCount::Name(text), k + 1))
        }
    };
    // [width]
    let mut width_arg = None;
    if let Some((c, j)) = count_arg(&cs, i) {
        width_arg = Some(c);
        i = j;
    } else if i < cs.len() && cs[i].is_ascii_digit() {
        let (w, j) = digit_run(&cs, i);
        s.width = w;
        i = j;
    }
    // [.precision]
    let mut precision_arg = None;
    if i < cs.len() && cs[i] == '.' {
        i += 1;
        if cs.get(i) == Some(&'*') {
            precision_arg = Some(FmtCount::Next);
            i += 1;
        } else if let Some((c, j)) = count_arg(&cs, i) {
            precision_arg = Some(c);
            i = j;
        } else {
            let (p, j) = digit_run(&cs, i);
            if p.is_none() {
                return Err(false);
            }
            s.precision = p;
            i = j;
        }
    }
    // [kind]
    let kind = match cs.get(i) {
        None => FmtKind::Display,
        Some('?') => {
            i += 1;
            FmtKind::Debug
        }
        // `x?` and `X?`: Debug with hex integers.
        Some(&c @ ('x' | 'X')) if cs.get(i + 1) == Some(&'?') => {
            i += 2;
            s.debug_hex = if c == 'x' { 1 } else { 2 };
            FmtKind::Debug
        }
        Some('x') => {
            i += 1;
            FmtKind::LowerHex
        }
        Some('X') => {
            i += 1;
            FmtKind::UpperHex
        }
        Some('o') => {
            i += 1;
            FmtKind::Octal
        }
        Some('b') => {
            i += 1;
            FmtKind::Binary
        }
        Some('e') => {
            i += 1;
            FmtKind::LowerExp
        }
        Some('E') => {
            i += 1;
            FmtKind::UpperExp
        }
        Some('p') => {
            i += 1;
            FmtKind::Pointer
        }
        Some(_) => return Err(false),
    };
    if i != cs.len() {
        return Err(false);
    }
    s.kind = kind;
    Ok((s, width_arg, precision_arg))
}

fn syntax(span: Span, msg: impl Into<String>) -> Diag {
    Diag::new("L0001", span, msg, "Fix the syntax. Lust uses Rust syntax.")
}

/// An item kind in the plural, as rustc names attribute targets.
fn item_kind_plural(kind: &ItemKind) -> &'static str {
    match kind {
        ItemKind::Fn(_) => "functions",
        ItemKind::Struct(_) => "structs",
        ItemKind::Enum(_) => "enums",
        ItemKind::Union(_) => "unions",
        ItemKind::Impl(_) => "impl blocks",
        ItemKind::Use(_) => "use statements",
        ItemKind::Mod(_) => "modules",
        ItemKind::Trait(_) => "traits",
        ItemKind::Type(_) => "type aliases",
        ItemKind::Const(_) => "constants",
        ItemKind::Static(_) => "statics",
        ItemKind::MacroRules(_) | ItemKind::MacroCall(_) => "macro calls",
        ItemKind::ExternCrate(_) => "extern crates",
        ItemKind::ExternBlock(_) => "extern blocks",
    }
}

/// A visibility written where Rust permits none (rustc E0449): on an
/// `impl` block, a trait item, or an item of a trait impl.
fn vis_not_permitted(span: Span) -> Diag {
    Diag::new(
        "L0001",
        span,
        "visibility qualifiers are not permitted here",
        "Remove the visibility: these items take the visibility of their trait or type.",
    )
}

/// True when `attr` lowers a lint: `#[allow(..)]`, `#[warn(..)]`, or
/// `#[expect(..)]` (the attributes the parser propagates from an enclosing
/// scope onto each `FnDef` in it). A deny-by-default lint at warn no longer
/// fails the build, and an unmet expectation is only a warning. `deny` and
/// `forbid` of a rustc lint are L0531, so they never reach a lint here.
fn is_allow(attr: &Attr, known: &Known) -> bool {
    attr.path.len() == 1 && [known.allow, known.warn, known.expect].contains(&attr.path[0].name)
}

/// A token's name for error messages. Never shows the payload, so internal ids (interned
/// symbol numbers, string indexes) cannot leak into diagnostics.
fn tok_name(t: Tok) -> &'static str {
    use Tok::*;
    match t {
        Ident(_) => "identifier",
        Reserved(_) => "reserved keyword",
        Int(..) => "integer literal",
        Float(_) => "float literal",
        Str(..) => "string literal",
        DocStr(_) => "doc comment string",
        ByteStr(_) => "byte string literal",
        ByteChar(_) => "byte char literal",
        Char(..) => "char literal",
        Lifetime(_) => "lifetime",
        As => "`as`",
        Break => "`break`",
        Const => "`const`",
        Continue => "`continue`",
        Else => "`else`",
        Enum => "`enum`",
        False => "`false`",
        Fn => "`fn`",
        For => "`for`",
        If => "`if`",
        Impl => "`impl`",
        In => "`in`",
        Let => "`let`",
        Loop => "`loop`",
        Match => "`match`",
        Mod => "`mod`",
        Mut => "`mut`",
        Pub => "`pub`",
        Ref => "`ref`",
        Return => "`return`",
        SelfLower => "`self`",
        SelfUpper => "`Self`",
        Static => "`static`",
        Struct => "`struct`",
        Trait => "`trait`",
        True => "`true`",
        Type => "`type`",
        Unsafe => "`unsafe`",
        Use => "`use`",
        Where => "`where`",
        While => "`while`",
        Async => "`async`",
        Dyn => "`dyn`",
        Move => "`move`",
        Crate => "`crate`",
        Super => "`super`",
        Extern => "`extern`",
        Await => "`await`",
        LParen => "`(`",
        RParen => "`)`",
        LBrace => "`{`",
        RBrace => "`}`",
        LBracket => "`[`",
        RBracket => "`]`",
        Comma => "`,`",
        Semi => "`;`",
        Colon => "`:`",
        PathSep => "`::`",
        Dot => "`.`",
        DotDot => "`..`",
        DotDotEq => "`..=`",
        Ellipsis => "`...`",
        Arrow => "`->`",
        FatArrow => "`=>`",
        Eq => "`=`",
        EqEq => "`==`",
        Ne => "`!=`",
        Lt => "`<`",
        Le => "`<=`",
        Gt => "`>`",
        Ge => "`>=`",
        Plus => "`+`",
        Minus => "`-`",
        Star => "`*`",
        Slash => "`/`",
        Percent => "`%`",
        PlusEq => "`+=`",
        MinusEq => "`-=`",
        StarEq => "`*=`",
        SlashEq => "`/=`",
        PercentEq => "`%=`",
        AmpEq => "`&=`",
        PipeEq => "`|=`",
        CaretEq => "`^=`",
        ShlEq => "`<<=`",
        Amp => "`&`",
        AndAnd => "`&&`",
        Pipe => "`|`",
        OrOr => "`||`",
        Caret => "`^`",
        Bang => "`!`",
        Pound => "`#`",
        Question => "`?`",
        Underscore => "`_`",
        Shl => "`<<`",
        Shr => "`>>`",
        ShrEq => "`>>=`",
        Dollar => "`$`",
        At => "`@`",
        Eof => "end of file",
    }
}

/// The L0203 reject for a lifetime where lust does not take one yet:
/// lifetime params on type aliases and associated types, `for<'a>`
/// types, and a lifetime token in an identifier position.
fn lifetime_error(span: Span) -> Diag {
    Diag::new(
        "L0203",
        span,
        "a lifetime is not supported in this position yet",
        "Lifetime params work on fns, structs, enums, impls, and type aliases; elsewhere, elide the lifetime or use `'static`.",
    )
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Tok {
        if let Some((t, _)) = self.split {
            return t;
        }
        self.toks[self.pos].tok
    }
    fn peek_at(&self, n: usize) -> Tok {
        if let Some((t, _)) = self.split {
            if n == 0 {
                return t;
            }
            return self.toks.get(self.pos + n - 1).map_or(Tok::Eof, |t| t.tok);
        }
        self.toks.get(self.pos + n).map_or(Tok::Eof, |t| t.tok)
    }
    fn span(&self) -> Span {
        if let Some((_, sp)) = self.split {
            return sp;
        }
        self.toks[self.pos].span
    }
    fn prev_span(&self) -> Span {
        self.toks[self.pos.saturating_sub(1)].span
    }
    fn bump(&mut self) -> Token {
        if let Some((tok, span)) = self.split.take() {
            return Token { tok, span };
        }
        let t = self.toks[self.pos];
        if t.tok != Tok::Eof {
            self.pos += 1;
        }
        t
    }
    /// Consumes a `>=` token as the `>` closing generic arguments,
    /// leaving its `=` half for the next read. Only `eat` and
    /// `expect` of `Tok::Gt` split this way.
    fn eat_split_ge(&mut self) -> Option<Span> {
        if self.split.is_none() && self.toks[self.pos].tok == Tok::Ge {
            let t = self.bump();
            self.split = Some((Tok::Eq, t.span));
            Some(t.span)
        } else {
            None
        }
    }
    /// Consumes a `<<` token as the `<` opening generic arguments or a
    /// qualified path, leaving its second `<` for the next read. Only
    /// `eat` and `expect` of `Tok::Lt` split this way.
    fn eat_split_shl(&mut self) -> Option<Span> {
        if self.split.is_none() && self.toks[self.pos].tok == Tok::Shl {
            let t = self.bump();
            let mid = t.span.lo + 1;
            self.split = Some((Tok::Lt, Span { lo: mid, ..t.span }));
            Some(Span { hi: mid, ..t.span })
        } else {
            None
        }
    }
    /// True at a `<` that may open generic arguments or a qualified
    /// path, including the first half of a `<<`.
    fn at_lt(&self) -> bool {
        matches!(self.peek(), Tok::Lt | Tok::Shl)
    }
    fn eat(&mut self, t: Tok) -> bool {
        if t == Tok::Gt && self.eat_split_ge().is_some() {
            return true;
        }
        if t == Tok::Lt && self.eat_split_shl().is_some() {
            return true;
        }
        if self.peek() == t {
            self.bump();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, t: Tok, what: &str) -> PResult<Span> {
        if t == Tok::Gt
            && let Some(sp) = self.eat_split_ge()
        {
            return Ok(sp);
        }
        if t == Tok::Lt
            && let Some(sp) = self.eat_split_shl()
        {
            return Ok(sp);
        }
        if self.peek() == t {
            Ok(self.bump().span)
        } else {
            Err(syntax(self.span(), format!("expected {what}, found {}", tok_name(self.peek()))))
        }
    }
    fn ident(&mut self) -> PResult<(Sym, Span)> {
        match self.peek() {
            Tok::Ident(s) => Ok((s, self.bump().span)),
            Tok::SelfUpper => Ok((self.known.self_type, self.bump().span)),
            Tok::Reserved(_) => Err(self.reserved_error(self.span())),
            // A lifetime is never an identifier in rustc grammar, so a
            // cfg syntax check reports it as L0001, not the L0203 reject.
            Tok::Lifetime(_) if self.cfg_syntax => Err(syntax(self.span(), "expected identifier, found lifetime")),
            Tok::Lifetime(_) => Err(lifetime_error(self.span())),
            t => Err(syntax(self.span(), format!("expected identifier, found {}", tok_name(t)))),
        }
    }
    /// The error for a reserved keyword (`gen`, `try`, ...) used where an identifier belongs.
    fn reserved_error(&self, span: Span) -> Diag {
        let Tok::Reserved(s) = self.toks[self.pos.min(self.toks.len() - 1)].tok else {
            return syntax(span, "expected identifier");
        };
        let name = self.interner.get(s);
        Diag::new(
            "L0001",
            span,
            format!("expected identifier, found reserved keyword `{name}`"),
            format!("Rename it, or write `r#{name}` to use it as an identifier."),
        )
    }

    /// The rejection for an AST v2 form that starts at the current token.
    fn reject(&self, code: &'static str, what: &str) -> Diag {
        not_yet(code, self.span(), what)
    }

    /// Records the reject for a form the parser builds but later
    /// stages do not support yet, keeping the earliest by span.
    /// See the `deferred` field. The `MAX_AST_DEPTH` guard defers
    /// this way (see `note_depth`).
    fn defer(&mut self, d: Diag) {
        // A cfg syntax check reports grammar errors only: a deferred
        // unsupported-form reject must not hide a later L0001.
        if self.cfg_syntax && d.code != "L0001" {
            return;
        }
        if self.deferred.as_ref().is_none_or(|old| d.span.lo < old.span.lo) {
            self.deferred = Some(d);
        }
    }

    /// The earlier of the deferred reject and a hard parse error.
    fn earlier(&mut self, hard: Diag) -> Diag {
        match self.deferred.take() {
            Some(d) if d.span.lo <= hard.span.lo => d,
            _ => hard,
        }
    }

    /// True when the current token is the identifier `name` (for weak keywords
    /// such as `union`, `macro_rules`, and `raw`).
    fn at_ident(&self, name: &str) -> bool {
        matches!(self.peek(), Tok::Ident(s) if self.interner.get(s) == name)
    }

    /// True at a macro call head: a path of one or more segments ending in `!`
    /// (for example `a::b!(..)`). Bounded: stops at the first other token.
    fn at_path_macro_call(&self) -> bool {
        let mut j = self.pos;
        loop {
            match self.toks.get(j).map(|t| t.tok) {
                Some(Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super | Tok::SelfLower) => j += 1,
                _ => return false,
            }
            match self.toks.get(j).map(|t| t.tok) {
                Some(Tok::Bang) => return true,
                Some(Tok::PathSep) => j += 1,
                _ => return false,
            }
        }
    }

    /// True at a macro call whose group is a `{}` (`m! {..}`, or
    /// `macro_rules! name {..}`). In statement position rustc ends the
    /// statement at its `}`, unless a `.` or `?` follows.
    fn at_brace_macro_call(&self) -> bool {
        if !self.at_path_macro_call() {
            return false;
        }
        let mut j = self.pos;
        while self.toks.get(j).map(|t| t.tok) != Some(Tok::Bang) {
            j += 1;
        }
        match self.toks.get(j + 1).map(|t| t.tok) {
            Some(Tok::LBrace) => true,
            Some(Tok::Ident(_)) => self.toks.get(j + 2).map(|t| t.tok) == Some(Tok::LBrace),
            _ => false,
        }
    }

    /// Parses visibility: `pub`, `pub(crate)`, `pub(self)`, `pub(super)`, or
    /// `pub(in path)`; the restricted path holds the path's segments.
    fn vis(&mut self) -> PResult<Vis> {
        self.vis_ctx(false)
    }

    /// `vis`, where `before_ty` says a type follows (a tuple field): there
    /// `pub (T)` is `pub` and the type. Anywhere else a group after `pub`
    /// that is not a restriction is an error, as in rustc (E0704).
    fn vis_ctx(&mut self, before_ty: bool) -> PResult<Vis> {
        if !self.eat(Tok::Pub) {
            return Ok(Vis::Private);
        }
        if self.peek() != Tok::LParen {
            return Ok(Vis::Public);
        }
        let short = matches!(self.peek_at(1), Tok::Crate | Tok::SelfLower | Tok::Super) && self.peek_at(2) == Tok::RParen;
        if !short && self.peek_at(1) != Tok::In {
            if before_ty {
                return Ok(Vis::Public);
            }
            return Err(syntax(
                self.span(),
                "incorrect visibility restriction; write `pub(crate)`, `pub(self)`, `pub(super)`, or `pub(in path)`",
            ));
        }
        let start = self.bump().span;
        self.eat(Tok::In);
        if !short {
            self.eat(Tok::PathSep);
        }
        let mut path = Vec::new();
        loop {
            match self.bump().tok {
                Tok::Ident(s) => path.push(PathSeg::plain(s)),
                Tok::Crate => path.push(PathSeg::plain(self.interner.intern("crate"))),
                Tok::Super => path.push(PathSeg::plain(self.interner.intern("super"))),
                Tok::SelfLower => path.push(PathSeg::plain(self.known.self_value)),
                Tok::SelfUpper => path.push(PathSeg::plain(self.known.self_type)),
                _ => return Err(syntax(self.prev_span(), "expected a module path in `pub(in ...)`")),
            }
            if !self.eat(Tok::PathSep) {
                break;
            }
        }
        if self.peek() != Tok::RParen {
            return Err(syntax(self.span(), "expected `)` after a visibility path"));
        }
        let end = self.bump().span;
        Ok(Vis::Restricted { path, span: start.to(end) })
    }

    /// True when the token after the current one starts where the current one ends, in
    /// the same file: the two were lexed as one punctuator with no space between them.
    fn next_touches(&self) -> bool {
        let a = self.toks[self.pos].span;
        let b = self.toks[self.pos + 1].span;
        a.file == b.file && a.hi == b.lo
    }
    /// True if the next two tokens are `>` `>` with no space, which means a right shift.
    fn at_shr(&self) -> bool {
        self.peek() == Tok::Gt && self.peek_at(1) == Tok::Gt && self.next_touches()
    }
    /// True at a `>>=`: lexed as `>` followed by `>=`, touching.
    fn at_shr_assign(&self) -> bool {
        self.peek() == Tok::Gt && self.peek_at(1) == Tok::Ge && self.next_touches()
    }

    /// Runs `f` one nesting level deeper, or errors past `MAX_DEPTH`.
    fn nest<T>(&mut self, f: impl FnOnce(&mut Self) -> PResult<T>) -> PResult<T> {
        if self.depth >= MAX_DEPTH {
            return Err(Diag::new(
                "L9001",
                self.span(),
                format!("nesting deeper than {MAX_DEPTH} levels is not supported"),
                "Split the expression into smaller pieces with `let`.",
            ));
        }
        self.depth += 1;
        let r = f(self);
        self.depth -= 1;
        r
    }
    /// The recorded depth of a node, or 1 for a node this parser did
    /// not build (see `Depths`).
    fn ed(&self, e: ExprId) -> u32 {
        self.depths.exprs.get(e.0 as usize).copied().unwrap_or(1)
    }
    fn td(&self, t: TyId) -> u32 {
        self.depths.tys.get(t.0 as usize).copied().unwrap_or(1)
    }
    fn pd(&self, p: PatId) -> u32 {
        self.depths.pats.get(p.0 as usize).copied().unwrap_or(1)
    }
    fn bd(&self, b: BlockId) -> u32 {
        self.depths.blocks.get(b.0 as usize).copied().unwrap_or(1)
    }

    /// Records the L9001 reject when a node passes `MAX_AST_DEPTH`.
    /// Deferred like other parse-but-reject forms: the parse itself
    /// stays within `MAX_DEPTH` of stack, so it can finish and report.
    fn note_depth(&mut self, d: u32, span: Span) {
        if d > MAX_AST_DEPTH {
            self.defer(Diag::new(
                "L9001",
                span,
                format!("nesting deeper than {MAX_AST_DEPTH} levels is not supported"),
                "Split the expression into smaller pieces with `let`.",
            ));
        }
    }

    /// The deepest child depth under generic arguments (0 for none).
    fn arg_depth(&self, a: &GenericArg) -> u32 {
        match a {
            GenericArg::Type(t) => self.td(*t),
            GenericArg::Const(e) => self.ed(*e),
            GenericArg::Lifetime(_) => 0,
            GenericArg::Binding { kind, .. } => match kind {
                BindingKind::EqTy(t) => self.td(*t),
                BindingKind::EqConst(e) => self.ed(*e),
                BindingKind::Constraint(bounds) => self.bounds_depth(bounds),
            },
        }
    }

    /// The deepest child depth under a bound list (0 for none).
    fn bounds_depth(&self, bounds: &[TraitBound]) -> u32 {
        bounds
            .iter()
            .map(|b| match b {
                TraitBound::Trait { trait_ref, .. } => self.path_depth(&trait_ref.path),
                TraitBound::Lifetime(_) => 0,
            })
            .max()
            .unwrap_or(0)
    }

    /// The deepest child depth under a path's generic arguments (0 for none).
    fn path_depth(&self, segs: &[PathSeg]) -> u32 {
        let mut m = 0;
        for s in segs {
            match &s.args {
                GenericArgs::None => {}
                GenericArgs::Angle(args) => {
                    for a in args {
                        m = m.max(self.arg_depth(a));
                    }
                }
                GenericArgs::Parenthesized { inputs, output } => {
                    for t in inputs {
                        m = m.max(self.td(*t));
                    }
                    if let Some(t) = output {
                        m = m.max(self.td(*t));
                    }
                }
            }
        }
        m
    }

    /// The deepest child depth of an expression node (0 for a leaf).
    fn expr_kids_depth(&self, e: &Expr) -> u32 {
        let mut m = 0u32;
        match e {
            Expr::Int(..)
            | Expr::Bool(_)
            | Expr::Str(_)
            | Expr::ByteStr(_)
            | Expr::Char(_)
            | Expr::Unit
            | Expr::SelfValue
            | Expr::Float(_)
            | Expr::Continue(_)
            | Expr::Underscore
            | Expr::MacroCall(_) => {}
            Expr::Path(segs) => m = self.path_depth(segs),
            Expr::Block(b) | Expr::UnsafeBlock(b) | Expr::ConstBlock(b) => m = self.bd(*b),
            Expr::LabeledBlock { body, .. } | Expr::AsyncBlock { body, .. } => m = self.bd(*body),
            Expr::If { cond, then, els } => {
                m = m.max(self.ed(*cond)).max(self.bd(*then));
                if let Some(x) = els {
                    m = m.max(self.ed(*x));
                }
            }
            Expr::While { cond, body, .. } => m = m.max(self.ed(*cond)).max(self.bd(*body)),
            Expr::Loop { body, .. } => m = self.bd(*body),
            Expr::For { pat, iter, body, .. } => m = m.max(self.pd(*pat)).max(self.ed(*iter)).max(self.bd(*body)),
            Expr::Match { scrut, arms } => {
                m = self.ed(*scrut);
                for a in arms {
                    m = m.max(self.pd(a.pat)).max(self.ed(a.body));
                    if let Some(g) = a.guard {
                        m = m.max(self.ed(g));
                    }
                }
            }
            Expr::Call { callee, args } => {
                m = self.ed(*callee);
                for a in args {
                    m = m.max(self.ed(*a));
                }
            }
            Expr::MethodCall { recv, generic_args, args, .. } => {
                m = self.ed(*recv);
                for a in generic_args {
                    m = m.max(self.arg_depth(a));
                }
                for a in args {
                    m = m.max(self.ed(*a));
                }
            }
            Expr::Field { base, .. } | Expr::TupleField { base, .. } => m = self.ed(*base),
            Expr::Index { base, index } => m = m.max(self.ed(*base)).max(self.ed(*index)),
            Expr::Binary { lhs, rhs, .. } | Expr::Assign { lhs, rhs } | Expr::AssignOp { lhs, rhs, .. } => {
                m = m.max(self.ed(*lhs)).max(self.ed(*rhs))
            }
            Expr::Unary { expr, .. } | Expr::Ref { expr, .. } | Expr::Deref(expr) | Expr::Try(expr) | Expr::Await(expr) => {
                m = self.ed(*expr)
            }
            Expr::Cast { expr, ty } => m = m.max(self.ed(*expr)).max(self.td(*ty)),
            Expr::StructLit { path, fields, update } => {
                m = self.path_depth(path);
                for (_, _, x) in fields {
                    m = m.max(self.ed(*x));
                }
                if let Some(x) = update {
                    m = m.max(self.ed(*x));
                }
            }
            Expr::Range { lo, hi, .. } => {
                if let Some(x) = lo {
                    m = m.max(self.ed(*x));
                }
                if let Some(x) = hi {
                    m = m.max(self.ed(*x));
                }
            }
            Expr::Break { value, .. } | Expr::Return(value) => {
                if let Some(x) = value {
                    m = self.ed(*x);
                }
            }
            Expr::Macro { args, .. } | Expr::Tuple(args) | Expr::Array(args) => {
                for a in args {
                    m = m.max(self.ed(*a));
                }
            }
            Expr::ArrayRepeat { value, len } => m = m.max(self.ed(*value)).max(self.ed(*len)),
            Expr::Closure { params, ret, body, .. } => {
                for p in params {
                    m = m.max(self.pd(p.pat));
                    if let Some(t) = p.ty {
                        m = m.max(self.td(t));
                    }
                }
                if let Some(t) = ret {
                    m = m.max(self.td(*t));
                }
                m = m.max(self.ed(*body));
            }
            Expr::Let { pat, scrut } => m = m.max(self.pd(*pat)).max(self.ed(*scrut)),
            Expr::QPath { self_ty, trait_path, segs } => {
                m = m.max(self.td(*self_ty)).max(self.path_depth(trait_path)).max(self.path_depth(segs))
            }
            Expr::OffsetOf { ty, .. } => m = self.td(*ty),
        }
        m
    }

    /// The deepest child depth of a type node (0 for a leaf).
    fn ty_kids_depth(&self, t: &TyExpr) -> u32 {
        let mut m = 0u32;
        match t {
            TyExpr::Unit | TyExpr::Never | TyExpr::Infer | TyExpr::MacroCall(_) => {}
            TyExpr::Path(segs) => m = self.path_depth(segs),
            TyExpr::Ref { inner, .. } | TyExpr::Slice(inner) | TyExpr::Ptr { inner, .. } | TyExpr::Paren(inner) => {
                m = self.td(*inner)
            }
            TyExpr::Tuple(ts) => {
                for x in ts {
                    m = m.max(self.td(*x));
                }
            }
            TyExpr::Array { inner, len } => m = m.max(self.td(*inner)).max(self.ed(*len)),
            TyExpr::FnPtr { inputs, ret, .. } => {
                for p in inputs {
                    m = m.max(self.td(p.ty));
                }
                if let Some(r) = ret {
                    m = m.max(self.td(*r));
                }
            }
            TyExpr::Dyn { bounds, .. } | TyExpr::ImplTrait { bounds, .. } => m = self.bounds_depth(bounds),
            TyExpr::QPath { self_ty, trait_path, segs } => {
                m = m.max(self.td(*self_ty)).max(self.path_depth(trait_path)).max(self.path_depth(segs))
            }
        }
        m
    }

    /// The deepest child depth of a pattern node (0 for a leaf).
    fn pat_kids_depth(&self, p: &Pat) -> u32 {
        let mut m = 0u32;
        match p {
            Pat::Wild | Pat::Binding { .. } | Pat::Rest | Pat::MacroCall(_) => {}
            Pat::Lit(e) => m = self.ed(*e),
            Pat::Path(segs) => m = self.path_depth(segs),
            Pat::TupleStruct { path, elems } => {
                m = self.path_depth(path);
                for x in elems {
                    m = m.max(self.pd(*x));
                }
            }
            Pat::Struct { path, fields, .. } => {
                m = self.path_depth(path);
                for (_, x) in fields {
                    m = m.max(self.pd(*x));
                }
            }
            Pat::Or(ps) | Pat::Tuple(ps) => {
                for x in ps {
                    m = m.max(self.pd(*x));
                }
            }
            Pat::Range { lo, hi, .. } => {
                if let Some(x) = lo {
                    m = m.max(self.ed(*x));
                }
                if let Some(x) = hi {
                    m = m.max(self.ed(*x));
                }
            }
            Pat::Slice { prefix, middle, suffix } => {
                for x in prefix.iter().chain(suffix) {
                    m = m.max(self.pd(*x));
                }
                if let Some(x) = middle {
                    m = m.max(self.pd(*x));
                }
            }
            Pat::Ref { inner, .. } | Pat::At { inner, .. } | Pat::Paren(inner) => m = self.pd(*inner),
            Pat::QPath { self_ty, trait_path, segs } => {
                m = m.max(self.td(*self_ty)).max(self.path_depth(trait_path)).max(self.path_depth(segs))
            }
        }
        m
    }

    /// The deepest child depth of a block (0 for an empty block).
    fn block_kids_depth(&self, b: &Block) -> u32 {
        let mut m = 0u32;
        for s in &b.stmts {
            match s {
                Stmt::Let { pat, ty, init, els, .. } => {
                    m = m.max(self.pd(*pat));
                    if let Some(t) = ty {
                        m = m.max(self.td(*t));
                    }
                    if let Some(x) = init {
                        m = m.max(self.ed(*x));
                    }
                    if let Some(x) = els {
                        m = m.max(self.bd(*x));
                    }
                }
                Stmt::Expr { expr, .. } => m = m.max(self.ed(*expr)),
                // An item statement's own nodes were guarded as they
                // were pushed; walks that enter the item start fresh
                // from it, so it adds no depth here.
                Stmt::Item(_) | Stmt::Macro { .. } => {}
            }
        }
        if let Some(x) = b.tail {
            m = m.max(self.ed(x));
        }
        m
    }

    fn push_expr(&mut self, e: Expr, span: Span) -> ExprId {
        let d = self.expr_kids_depth(&e).saturating_add(1);
        self.note_depth(d, span);
        self.ast.exprs.push(e);
        self.ast.expr_spans.push(span);
        self.depths.exprs.resize(self.ast.exprs.len() - 1, 1);
        self.depths.exprs.push(d);
        ExprId(self.ast.exprs.len() as u32 - 1)
    }
    fn push_pat(&mut self, p: Pat, span: Span) -> PatId {
        let d = self.pat_kids_depth(&p).saturating_add(1);
        self.note_depth(d, span);
        self.ast.pats.push(p);
        self.ast.pat_spans.push(span);
        self.depths.pats.resize(self.ast.pats.len() - 1, 1);
        self.depths.pats.push(d);
        PatId(self.ast.pats.len() as u32 - 1)
    }
    fn push_ty(&mut self, t: TyExpr, span: Span) -> TyId {
        let d = self.ty_kids_depth(&t).saturating_add(1);
        self.note_depth(d, span);
        self.ast.tys.push(t);
        self.ast.ty_spans.push(span);
        self.depths.tys.resize(self.ast.tys.len() - 1, 1);
        self.depths.tys.push(d);
        TyId(self.ast.tys.len() as u32 - 1)
    }
    fn push_block(&mut self, b: Block) -> BlockId {
        let d = self.block_kids_depth(&b).saturating_add(1);
        self.note_depth(d, b.span);
        self.ast.blocks.push(b);
        self.depths.blocks.resize(self.ast.blocks.len() - 1, 1);
        self.depths.blocks.push(d);
        BlockId(self.ast.blocks.len() as u32 - 1)
    }

    // ---------- Items ----------

    /// Parses outer attributes (`#[..]`, `///` docs) in front of an item.
    /// Returns the derive list, whether `#[test]` was present, and the recorded
    /// attributes. Lint attributes and known tool attributes (`rustfmt::`,
    /// `clippy::`) are accepted and ignored, as before. A known Rust attribute
    /// lust does not handle yet (cfg, repr, path, inline, and kin) rejects with
    /// L0522; a name lust does not know at all rejects with L0402. An inner
    /// attribute (`#![..]`, `//!` docs) here is a syntax error, as in rustc:
    /// inner attributes are permitted only at the very start of a file, a
    /// module, impl, trait, or match body, or a permitted block, and those
    /// sites call `inner_attributes` before anything else in the body.
    fn attributes(&mut self) -> PResult<ParsedAttrs> {
        self.attributes_at(true, false, false, "", 0)
    }

    /// Attributes on a part of an item (a field, parameter, variant, arm, or
    /// statement). `derive` and `test` are not valid there (rustc rejects
    /// them), so they get the unsupported-attribute error, not a free pass.
    /// `what` and `flags` name the part for the target check
    /// (`attrs::check_target`).
    fn part_attributes(&mut self, what: &'static str, flags: u8) -> PResult<ParsedAttrs> {
        self.attributes_at(false, false, false, what, flags)
    }

    /// Attributes on an enum variant: part attributes plus `#[default]`
    /// and `#[non_exhaustive]`, which rustc accepts only there (collect
    /// checks that the enum derives `Default` and that the `#[default]`
    /// variant is a unit variant).
    fn variant_attributes(&mut self) -> PResult<ParsedAttrs> {
        self.attributes_at(false, false, true, "enum variants", attrs::T_VARIANT)
    }

    /// Parses a run of inner attributes (`#![..]`, `//!` docs) at a site
    /// that permits them. Stops at the first outer attribute, which belongs
    /// to the next item or statement in the body.
    fn inner_attributes(&mut self) -> PResult<ParsedAttrs> {
        self.attributes_at(true, true, false, "", 0)
    }

    /// True when the next tokens start an inner attribute (`#!`).
    fn at_inner_attr(&self) -> bool {
        self.peek() == Tok::Pound && self.peek_at(1) == Tok::Bang
    }

    fn attributes_at(&mut self, item_level: bool, inner_only: bool, variant: bool, what: &str, flags: u8) -> PResult<ParsedAttrs> {
        let mut out = ParsedAttrs::default();
        while self.peek() == Tok::Pound {
            if inner_only && !self.at_inner_attr() {
                break;
            }
            if !inner_only && self.at_inner_attr() && self.peek_at(2) == Tok::LBracket {
                return Err(syntax(self.span(), "an inner attribute is not permitted in this context"));
            }
            let start = self.bump().span;
            let inner = self.eat(Tok::Bang);
            self.expect(Tok::LBracket, "`[`")?;
            // Find the matching `]` first, so nested brackets inside the
            // attribute cannot confuse the per-attribute handling below.
            let body_start = self.pos;
            let mut depth = 1usize;
            let mut body_end = None;
            for j in body_start..self.toks.len() {
                match self.toks[j].tok {
                    Tok::LBracket => depth += 1,
                    Tok::RBracket => {
                        depth -= 1;
                        if depth == 0 {
                            body_end = Some(j);
                            break;
                        }
                    }
                    Tok::Eof => break,
                    _ => {}
                }
            }
            let Some(body_end) = body_end else {
                return Err(syntax(start, "unterminated attribute"));
            };
            let body: Vec<Token> = self.toks[body_start..body_end].to_vec();
            self.pos = body_end + 1;
            // The attribute path: name segments joined by `::` at the start.
            let mut path: Vec<PathSeg> = Vec::new();
            let mut bi = 0usize;
            while let Some(t) = body.get(bi) {
                match t.tok {
                    Tok::Ident(s) => {
                        path.push(PathSeg::plain(s));
                        bi += 1;
                        if body.get(bi).map(|t| t.tok) == Some(Tok::PathSep) {
                            bi += 1;
                        } else {
                            break;
                        }
                    }
                    _ => break,
                }
            }
            // rustc's attribute grammar holds in enabled code too:
            // `#[derive(Debug) x]` is a syntax error, not a derive.
            if !self.cfg_syntax {
                self.cfg_attr_grammar(start, body_start, body_end)?;
            }
            if self.cfg_syntax && path.is_empty() {
                // A path this loop does not read (`::a`, `self::a`,
                // `unsafe(..)`): the grammar check below judges it.
                self.cfg_attr_grammar(start, body_start, body_end)?;
                continue;
            }
            // Rust 2024 unsafe attributes (`#[unsafe(no_mangle)]`): lust has
            // no unsafe code, so none of them is supported yet.
            if path.is_empty() && body.first().map(|t| t.tok) == Some(Tok::Unsafe) && body.get(1).map(|t| t.tok) == Some(Tok::LParen) {
                let inner = match body.get(2).map(|t| t.tok) {
                    Some(Tok::Ident(s)) => self.interner.get(s).to_string(),
                    _ => "..".to_string(),
                };
                return Err(not_yet(C_ATTR, start, &format!("the `#[unsafe({inner})]` attribute")));
            }
            let Some(first) = path.first().map(|s| s.name) else {
                return Err(syntax(start, "expected an attribute name"));
            };
            let name_span = body.first().map_or(start, |t| t.span);
            let name_text = self.interner.get(first).to_string();
            let input = if body.get(bi).map(|t| t.tok) == Some(Tok::LParen) {
                // The usual form: `#[name(..)]`. The list is what is inside.
                let mut d = 0usize;
                let mut end = body.len();
                for (j, t) in body.iter().enumerate().skip(bi) {
                    match t.tok {
                        Tok::LParen => d += 1,
                        Tok::RParen => {
                            d -= 1;
                            if d == 0 {
                                end = j;
                                break;
                            }
                        }
                        _ => {}
                    }
                }
                AttrInput::List(Delim::Paren, token_trees(&body[bi + 1..end]))
            } else if bi < body.len() {
                AttrInput::List(Delim::Bracket, token_trees(&body[bi..]))
            } else {
                AttrInput::None
            };
            let attr = Attr {
                style: if inner { AttrStyle::Inner } else { AttrStyle::Outer },
                path: path.clone(),
                input,
                span: start.to(name_span),
            };
            if self.cfg_syntax {
                // Only the attribute grammar runs here (`cfg_attr_grammar`).
                // Which names exist is checked only for enabled code.
                self.cfg_attr_grammar(start, body_start, body_end)?;
                if !path.is_empty() {
                    out.attrs.push(attr);
                }
                continue;
            }
            let k = self.known;
            if path.len() == 1 {
                attrs::check_input(&name_text, &attr, self.interner)?;
                // A part of an item takes only the attributes its kind
                // permits (`what` and `flags` say which part this is).
                if !item_level {
                    attrs::check_target(std::slice::from_ref(&attr), what, flags, self.interner)?;
                }
            }
            if path.len() > 1 {
                // Tool attributes under a known tool namespace are ignored.
                if name_text == "rustfmt" || name_text == "clippy" {
                    out.attrs.push(attr);
                    continue;
                }
                return Err(Diag::new(
                    "L0402",
                    name_span,
                    format!("unsupported attribute `{name_text}`"),
                    "Lust supports #[derive(...)], #[test], and lint attributes such as #[allow(...)].",
                ));
            }
            if !item_level && (first == k.derive || first == k.test) {
                return Err(Diag::new(
                    "L0402",
                    name_span,
                    format!("unsupported attribute `{name_text}`"),
                    "Lust supports #[derive(...)] on structs and enums, #[test] on functions, and lint attributes such as #[allow(...)].",
                ));
            }
            match first {
                _ if first == k.derive && !inner => {
                    // The derive names are the identifiers inside the `(..)`.
                    if body.get(bi).map(|t| t.tok) != Some(Tok::LParen) {
                        return Err(syntax(name_span, "expected `(` after `derive`"));
                    }
                    for t in &body[bi + 1..] {
                        match t.tok {
                            Tok::Ident(s) => out.derives.push((s, t.span)),
                            Tok::Comma | Tok::PathSep => {}
                            Tok::RParen => break,
                            _ => return Err(syntax(t.span, "expected a trait name in `derive`")),
                        }
                    }
                }
                _ if first == k.test && !inner => out.is_test = true,
                // Doc comments lex to this attribute; it carries no code.
                _ if name_text == "doc" => {}
                _ if item_level && (name_text == TLS_ATTR || name_text == TLS_CONST_ATTR) => {}
                _ if name_text == "repr" => {}
                // `attrs::check_input` judged the lint list (L0531 for deny and forbid).
                // `expect` silences its lints as `allow` does; an unmet
                // expectation is only a warning in rustc.
                _ if first == k.allow || first == k.warn || first == k.deny || name_text == "forbid" || name_text == "expect" => {}
                // Advisory attributes are accepted and ignored, as
                // ARCH 1.6 gives them: `inline` and `cold` are hints,
                // `must_use` and `deprecated` are lints with no
                // warning infrastructure in v1. No output changes.
                _ if matches!(name_text.as_str(), "inline" | "cold" | "must_use" | "deprecated") => {}
                // Test harness attributes: they change only how
                // `lust test` runs a `#[test]` fn (src/testrun.rs
                // reads them from the item). In a normal build the
                // fn is removed, and on any other item rustc only
                // warns, so accepting and ignoring is exact here.
                // `attrs::check_input` judged the written form.
                _ if matches!(name_text.as_str(), "ignore" | "should_panic") => {}
                // `#[track_caller]` (check/caller.rs): the fn reports its
                // caller's location in panics and `Location::caller()`.
                _ if name_text == "track_caller" && matches!(attr.input, AttrInput::None) => {}
                _ if RESOLVE_ATTRS.contains(&name_text.as_str()) => {}
                // `#[non_exhaustive]` on a struct, enum, or variant:
                // collect records it on the Adt; the checker enforces
                // it across crate borders.
                _ if name_text == "non_exhaustive" => {}
                // `#![recursion_limit = "N"]`: the expander checked the value;
                // the checker reads the crate's from `Ast::inner_attrs`.
                _ if inner && name_text == "recursion_limit" => {}
                // `#[global_allocator]` on a static: collect checks
                // the type is a known allocator and that there is
                // only one; the lust runtime keeps its allocator
                // (allocation strategy does not change output).
                _ if name_text == "global_allocator" && !inner => {}
                // `#[default]` marks the `Default` variant of a derived enum.
                _ if variant && !inner && name_text == "default" && matches!(attr.input, AttrInput::None) => {}
                _ if KNOWN_ATTRS.contains(&name_text.as_str()) => {
                    return Err(Diag::new(
                        C_ATTR,
                        name_span,
                        format!("the `#[{name_text}]` attribute is not supported yet"),
                        "Remove the attribute, or rewrite this part with the supported subset (see README).",
                    ));
                }
                _ => {
                    return Err(Diag::new(
                        "L0402",
                        name_span,
                        format!("unsupported attribute `{name_text}`"),
                        "Lust supports #[derive(...)], #[test], and lint attributes such as #[allow(...)].",
                    ));
                }
            }
            out.attrs.push(attr);
        }
        Ok(out)
    }

    /// The attribute grammar rustc checks on every attribute, cfg-disabled
    /// code included, on the
    /// body tokens `lo..hi` (between `#[` and `]`): `unsafe(item)` or an
    /// item, where an item is a path (`::`-separated names, an optional
    /// leading `::`) followed by nothing, one delimited token group, or
    /// `= expression`. Doc comments are `doc = "..."` items. Names and
    /// values are not checked, as rustc checks those only after it
    /// strips disabled code.
    fn cfg_attr_grammar(&mut self, start: Span, lo: usize, hi: usize) -> PResult<()> {
        let malformed = || syntax(start, "malformed attribute input");
        // The matching close of the group that opens at `i`, if any.
        let close_of = |i: usize| -> Option<usize> {
            let mut d = 0usize;
            for j in i..hi {
                match self.toks[j].tok {
                    Tok::LParen | Tok::LBracket | Tok::LBrace => d += 1,
                    Tok::RParen | Tok::RBracket | Tok::RBrace => {
                        d = d.checked_sub(1)?;
                        if d == 0 {
                            return Some(j);
                        }
                    }
                    _ => {}
                }
            }
            None
        };
        let at = |i: usize| if i < hi { self.toks[i].tok } else { Tok::Eof };
        if at(lo) == Tok::Unsafe && at(lo + 1) == Tok::LParen {
            return match close_of(lo + 1) {
                Some(c) if c + 1 == hi => self.cfg_attr_grammar(start, lo + 2, c),
                _ => Err(malformed()),
            };
        }
        let mut i = lo;
        if at(i) == Tok::PathSep {
            i += 1;
        }
        loop {
            if !matches!(at(i), Tok::Ident(_) | Tok::SelfLower | Tok::SelfUpper | Tok::Super | Tok::Crate) {
                return Err(syntax(if i < hi { self.toks[i].span } else { start }, "expected an attribute name"));
            }
            i += 1;
            if at(i) != Tok::PathSep {
                break;
            }
            i += 1;
        }
        match at(i) {
            Tok::Eof => Ok(()),
            Tok::LParen | Tok::LBracket | Tok::LBrace if close_of(i) == Some(hi - 1) => Ok(()),
            // A doc comment (`doc = DocStr`), which no expression parse takes.
            Tok::Eq if i + 2 == hi && matches!(at(i + 1), Tok::DocStr(_)) => Ok(()),
            // One literal, the usual value (`doc = "..."`, `path = "a.rs"`).
            Tok::Eq if i + 2 == hi && matches!(at(i + 1), Tok::Str(..) | Tok::Int(..) | Tok::Float(..) | Tok::True | Tok::False) => {
                Ok(())
            }
            Tok::Eq if i + 1 < hi => {
                let saved = self.pos;
                // A trial parse: an unsupported-form reject it defers is
                // not this attribute's verdict.
                let deferred = self.deferred.take();
                self.pos = i + 1;
                let parsed = self.expr();
                let end = self.pos;
                self.pos = saved;
                self.deferred = deferred;
                match parsed {
                    Ok(_) if end == hi => Ok(()),
                    Ok(_) => Err(syntax(self.toks[end.min(hi)].span, "expected `]` after the attribute value")),
                    // A valid form lust cannot build: the value cannot be
                    // judged past it, so it counts as clean.
                    Err(d) if d.code != "L0001" => Ok(()),
                    Err(d) => Err(d),
                }
            }
            _ => Err(malformed()),
        }
    }

    /// `derive` and `test` placement, as in rustc: `#[derive(..)]` applies
    /// only to a struct or enum, and `#[test]` only to a free function.
    /// Anywhere else the attribute was parsed and would be silently
    /// dropped, which is a false accept.
    fn check_derive_test(&self, parsed: &ParsedAttrs, is_adt: bool, is_fn: bool) -> PResult<()> {
        // Attribute placement is not grammar: rustc checks it after
        // cfg stripping, so disabled code does not take this error.
        if self.cfg_syntax {
            return Ok(());
        }
        // Presence of the attribute is what counts: `#[derive()]` on a
        // function is an error in rustc even with an empty list.
        let derive_attr = parsed.attrs.iter().find(|a| a.path.len() == 1 && a.path[0].name == self.known.derive);
        if !is_adt && let Some(attr) = derive_attr {
            let span = attr.span;
            return Err(Diag::new(
                "L0402",
                span,
                "`derive` may only be applied to structs and enums",
                "Move the `#[derive(..)]` attribute to a struct or enum definition.",
            ));
        }
        if !is_fn && parsed.is_test {
            let span =
                parsed.attrs.iter().find(|a| a.path.len() == 1 && a.path[0].name == self.known.test).map_or(Span::default(), |a| a.span);
            return Err(Diag::new(
                "L0402",
                span,
                "the `test` attribute may only be used on a free function",
                "Move the `#[test]` attribute to a free function.",
            ));
        }
        Ok(())
    }

    /// Attribute targets on a trait or impl item: rustc takes `inline`
    /// on fns (and, with a warning, on consts), never on types, and
    /// `repr` and `non_exhaustive` on none of them. The next token
    /// tells the item kind.
    fn check_assoc_targets(&self, parsed: &ParsedAttrs, in_trait_impl: bool) -> PResult<()> {
        let is_type = self.peek() == Tok::Type || (self.peek() != Tok::Fn && self.peek_at(1) == Tok::Type);
        let is_fn = !is_type && (self.peek() == Tok::Fn || self.peek_at(1) == Tok::Fn || self.peek_at(2) == Tok::Fn);
        let trait_impl = if in_trait_impl && !self.lint_allowed(&parsed.attrs, "useless_deprecated") { attrs::T_TRAIT_IMPL } else { 0 };
        attrs::check_target(
            &parsed.attrs,
            if is_type { "associated types" } else { "associated items" },
            if is_type { trait_impl } else if is_fn { attrs::T_FN | trait_impl } else { attrs::T_FN },
            self.interner,
        )
    }

    /// True when `#[allow(name)]` is on these attributes or on an
    /// enclosing `mod`, `impl`, or `trait` (`scope_allows`).
    fn lint_allowed(&self, attrs: &[Attr], name: &str) -> bool {
        attrs.iter().chain(&self.scope_allows).any(|a| crate::check::allow_attr(a, self.interner, name))
    }

    /// True when the tokens from here are only item qualifiers (`const`,
    /// `async`, `unsafe`, `extern "abi"`) and then `}` or the end.
    fn quals_then_end(&self) -> bool {
        let mut k = 0;
        loop {
            match self.peek_at(k) {
                Tok::Const | Tok::Async | Tok::Unsafe | Tok::Extern | Tok::Str(..) => k += 1,
                Tok::RBrace | Tok::Eof => return k > 0,
                _ => return false,
            }
        }
    }

    fn item(&mut self) -> PResult<Option<Item>> {
        let outer = std::mem::replace(&mut self.in_body, false);
        let item = self.item_here();
        self.in_body = outer;
        item
    }

    /// `item` with `in_body` cleared.
    fn item_here(&mut self) -> PResult<Option<Item>> {
        let start = self.span();
        let parsed = self.attributes()?;
        let derives = parsed.derives.clone();
        // An outer `#[allow(..)]` on a `mod`, `impl`, or `trait` item scopes
        // over the functions inside it (see `scope_allows`).
        let scope_mark = self.scope_allows.len();
        self.scope_allows.extend(parsed.attrs.iter().filter(|a| is_allow(a, self.known)).cloned());
        let vis_start = self.span();
        let vis = self.vis()?;
        // Only a written visibility has a span of its own.
        let vis_span = if vis == Vis::Private { vis_start } else { vis_start.to(self.prev_span()) };
        // A `const` item (`const NAME: Ty = ...;`), told apart from a
        // `const fn` qualifier by the name and colon after it.
        if self.peek() == Tok::Const && matches!(self.peek_at(1), Tok::Ident(_) | Tok::Underscore) && self.peek_at(2) == Tok::Colon {
            let kind = ItemKind::Const(self.const_def()?);
            self.check_derive_test(&parsed, false, false)?;
            attrs::check_target(&parsed.attrs, "constants", 0, self.interner)?;
            self.scope_allows.truncate(scope_mark);
            return Ok(Some(Item { vis, attrs: parsed.attrs, kind, span: start.to(self.prev_span()) }));
        }
        // Function and impl qualifiers, in any written order: `const`,
        // `async`, `unsafe`, and `extern "abi"`. A lone `const` with no `fn`
        // after it is a const item, handled in the match below.
        let mut qual = FnQual::default();
        loop {
            match self.peek() {
                Tok::Const if !qual.is_const => {
                    self.bump();
                    qual.is_const = true;
                }
                Tok::Async if !qual.is_async => {
                    self.bump();
                    qual.is_async = true;
                }
                Tok::Unsafe if !qual.is_unsafe => {
                    self.bump();
                    qual.is_unsafe = true;
                }
                Tok::Extern if qual.abi.is_none() => {
                    self.bump();
                    if let Tok::Str(i, _) = self.peek() {
                        self.bump();
                        qual.abi = Some(i + self.str_base);
                    } else {
                        // `extern { .. }`, `extern crate`, or `extern fn`: put the
                        // marker in with no ABI string, told apart by what follows.
                        qual.abi = Some(u32::MAX);
                        break;
                    }
                }
                _ => break,
            }
        }
        let has_qual = qual.is_const || qual.is_async || qual.is_unsafe || qual.abi.is_some();
        let kind = match self.peek() {
            Tok::Fn if has_qual && !(qual.is_const && !qual.is_async && !qual.is_unsafe && qual.abi.is_none()) && !self.cfg_syntax => {
                return Err(if qual.is_async {
                    async_error(start)
                } else if qual.is_unsafe {
                    unsafe_error(start)
                } else {
                    not_yet(C_EXTERN, start, "extern functions")
                });
            }
            Tok::Fn => {
                let mut def = self.fn_def()?;
                def.is_test = parsed.is_test;
                def.vis = vis.clone();
                // `fn_def` seeded `attrs` with the enclosing scopes' allows.
                let mut attrs = parsed.attrs.clone();
                attrs.extend(def.attrs);
                def.attrs = attrs;
                def.qual = qual;
                ItemKind::Fn(def)
            }
            Tok::Struct if !has_qual => ItemKind::Struct(self.struct_def(derives)?),
            Tok::Enum if !has_qual => ItemKind::Enum(self.enum_def(derives)?),
            Tok::Impl if vis != Vis::Private && !self.cfg_syntax => return Err(vis_not_permitted(vis_span)),
            Tok::Impl if qual.is_unsafe && !qual.is_const && !qual.is_async && qual.abi.is_none() => ItemKind::Impl(self.impl_def(true)?),
            Tok::Impl if !has_qual => ItemKind::Impl(self.impl_def(false)?),
            Tok::Use if !has_qual => ItemKind::Use(self.use_def()?),
            // A visibility at the end of the file is no item (rustc:
            // "visibility `pub` is not followed by an item").
            Tok::Eof if vis != Vis::Private && !has_qual => return Err(syntax(vis_span, "visibility is not followed by an item")),
            Tok::Eof if derives.is_empty() && parsed.attrs.is_empty() && !has_qual => {
                self.scope_allows.truncate(scope_mark);
                return Ok(None);
            }
            Tok::Eof if !has_qual => return Err(syntax(start, "expected an item after attributes")),
            Tok::Trait if !qual.is_const && !qual.is_async && qual.abi.is_none() => {
                let mut def = self.trait_def()?;
                def.is_unsafe = qual.is_unsafe;
                ItemKind::Trait(def)
            }
            Tok::Mod if !has_qual => ItemKind::Mod(self.mod_def()?),
            Tok::Static if !has_qual => ItemKind::Static(self.static_def(false)?),
            Tok::Type if !has_qual => ItemKind::Type(self.type_alias_def()?),
            // `extern { .. }` and `extern crate ..;`: the qualifier loop ate `extern`.
            Tok::LBrace if qual.abi.is_some() && self.cfg_syntax => ItemKind::Mod(self.extern_block_cfg(start)?),
            Tok::LBrace if qual.abi.is_some() => return Err(not_yet(C_EXTERN, start, "extern blocks")),
            Tok::Crate if qual.abi.is_some() => ItemKind::ExternCrate(self.extern_crate_def()?),
            // Qualifiers with nothing after them are a grammar error.
            Tok::Eof | Tok::RBrace if has_qual => return Err(syntax(start, "expected an item after qualifiers")),
            // In cfg-removed code `const` with no item after it (`const C =
            // 1;`, a bare `const`) is a grammar error, as in rustc.
            _ if qual.is_const && self.cfg_syntax => return Err(syntax(start, "expected an item after `const`")),
            _ if qual.is_const => return Err(not_yet(C_CONST, start, "const and static items")),
            _ if qual.is_async => return Err(async_error(start)),
            _ if qual.is_unsafe => return Err(unsafe_error(start)),
            Tok::Ident(_) if self.cfg_syntax && self.at_ident("union") && matches!(self.peek_at(1), Tok::Ident(_)) => {
                self.bump(); // `union`
                let (name, name_span) = self.ident()?;
                let generics = self.generics(true)?;
                let where_clause = self.where_clause()?;
                let fields = self.fields()?;
                ItemKind::Struct(StructDef {
                    name,
                    name_span,
                    generics,
                    fields: VariantFields::Struct(fields),
                    where_clause,
                    derives: derives.clone(),
                })
            }
            Tok::Ident(_) if self.at_ident("union") && matches!(self.peek_at(1), Tok::Ident(_)) => {
                return Err(not_yet(C_TY, start, "unions"));
            }
            Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super if self.cfg_syntax && self.at_path_macro_call() => {
                self.skip_macro_invocation()?;
                self.eat(Tok::Semi);
                self.scope_allows.truncate(scope_mark);
                return Ok(None);
            }
            Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super if self.at_path_macro_call() => {
                return Err(macro_error(start));
            }
            Tok::Reserved(_) => return Err(self.reserved_error(start)),
            t => return Err(syntax(start, format!("expected an item, found {}", tok_name(t)))),
        };
        self.check_derive_test(&parsed, matches!(kind, ItemKind::Struct(_) | ItemKind::Enum(_)), matches!(kind, ItemKind::Fn(_)))?;
        let trait_impl = matches!(&kind, ItemKind::Impl(d) if d.trait_ref.is_some());
        attrs::check_target(
            &parsed.attrs,
            if trait_impl { "trait impl blocks" } else { item_kind_plural(&kind) },
            match &kind {
                ItemKind::Impl(_) if trait_impl && !self.lint_allowed(&parsed.attrs, "useless_deprecated") => attrs::T_TRAIT_IMPL,
                ItemKind::Fn(_) => attrs::T_FN,
                ItemKind::Struct(_) | ItemKind::Enum(_) => attrs::T_ADT,
                ItemKind::Union(_) => attrs::T_UNION,
                ItemKind::Static(_) => attrs::T_STATIC,
                _ => 0,
            },
            self.interner,
        )?;
        self.scope_allows.truncate(scope_mark);
        Ok(Some(Item { vis, attrs: parsed.attrs, kind, span: start.to(self.prev_span()) }))
    }

    /// Parses a `use` declaration into a tree. A malformed tree is a
    /// syntax error, as in rustc: an earlier fallback skipped to the `;`
    /// and recorded an empty group, which accepted every bad `use` form.
    fn use_def(&mut self) -> PResult<UseDef> {
        let start = self.expect(Tok::Use, "`use`")?;
        let tree = self.use_tree()?;
        self.expect(Tok::Semi, "`;`")?;
        Ok(UseDef { tree, span: start.to(self.prev_span()) })
    }

    /// One use tree: a prefix path, then a name, a `*`, or a `{..}` group.
    fn use_tree(&mut self) -> PResult<UseTree> {
        let start = self.span();
        let leading_colon = self.eat(Tok::PathSep);
        if self.eat(Tok::LBrace) {
            return Ok(UseTree {
                leading_colon,
                prefix: Vec::new(),
                kind: UseKind::Group(self.use_group()?),
                span: start.to(self.prev_span()),
            });
        }
        if self.eat(Tok::Star) {
            return Ok(UseTree { leading_colon, prefix: Vec::new(), kind: UseKind::Glob, span: start.to(self.prev_span()) });
        }
        let mut prefix = Vec::new();
        loop {
            let name = match self.peek() {
                Tok::Ident(_) | Tok::SelfUpper => self.ident()?.0,
                Tok::SelfLower => {
                    self.bump();
                    self.known.self_value
                }
                Tok::Crate => {
                    self.bump();
                    self.interner.intern("crate")
                }
                Tok::Super => {
                    self.bump();
                    self.interner.intern("super")
                }
                t => return Err(syntax(self.span(), format!("expected a name in `use`, found {}", tok_name(t)))),
            };
            prefix.push(PathSeg::plain(name));
            if !self.eat(Tok::PathSep) {
                break;
            }
            if self.eat(Tok::Star) {
                return Ok(UseTree { leading_colon, prefix, kind: UseKind::Glob, span: start.to(self.prev_span()) });
            }
            if self.eat(Tok::LBrace) {
                return Ok(UseTree { leading_colon, prefix, kind: UseKind::Group(self.use_group()?), span: start.to(self.prev_span()) });
            }
        }
        let rename = if self.eat(Tok::As) {
            Some(match self.peek() {
                Tok::Underscore => {
                    self.bump();
                    self.interner.intern("_")
                }
                _ => self.ident()?.0,
            })
        } else {
            None
        };
        Ok(UseTree { leading_colon, prefix, kind: UseKind::Simple { rename }, span: start.to(self.prev_span()) })
    }

    /// An `extern { ... }` block in a cfg syntax check: foreign fns,
    /// statics, and types are grammar-checked and then dropped, so the
    /// dummy `ModDef` carries no items. Enabled code still rejects
    /// extern blocks as unsupported.
    fn extern_block_cfg(&mut self, start: Span) -> PResult<ModDef> {
        self.expect(Tok::LBrace, "`{`")?;
        let _inner = self.inner_attributes()?;
        while self.peek() != Tok::RBrace {
            if self.peek() == Tok::Eof {
                return Err(syntax(self.span(), "expected `}`, found end of file"));
            }
            let _parsed = self.attributes()?;
            let _vis = self.vis()?;
            self.eat(Tok::Unsafe);
            match self.peek() {
                Tok::Fn => {
                    self.cfg_foreign = true;
                    let def = self.fn_def_inner(true);
                    self.cfg_foreign = false;
                    let _def = def?;
                }
                Tok::Static => {
                    let _def = self.static_def(true)?;
                }
                Tok::Type => {
                    self.bump();
                    let _name = self.ident()?;
                    let _generics = self.generics(true)?;
                    self.expect(Tok::Semi, "`;`")?;
                }
                Tok::Ident(_) | Tok::SelfUpper if self.at_path_macro_call() => {
                    self.skip_macro_invocation()?;
                    self.eat(Tok::Semi);
                }
                t => return Err(syntax(self.span(), format!("expected a foreign item, found {}", tok_name(t)))),
            }
        }
        self.bump();
        Ok(ModDef { name: Sym(0), name_span: start, inner_attrs: Vec::new(), body: Some(Vec::new()), span: start.to(self.prev_span()) })
    }

    /// A `mod` item: `mod name;` (a file module; the resolver finds the
    /// file) or `mod name { ... }` (inline items parsed in place).
    fn mod_def(&mut self) -> PResult<ModDef> {
        let start = self.expect(Tok::Mod, "`mod`")?;
        let (name, name_span) = self.ident()?;
        if self.eat(Tok::Semi) {
            return Ok(ModDef { name, name_span, inner_attrs: Vec::new(), body: None, span: start.to(self.prev_span()) });
        }
        self.expect(Tok::LBrace, "`{` or `;`")?;
        // Inner attributes are permitted only here, before the first item.
        let inner = self.inner_attributes()?;
        attrs::check_target(&inner.attrs, "modules", 0, self.interner)?;
        let scope_mark = self.scope_allows.len();
        self.scope_allows.extend(inner.attrs.iter().filter(|a| is_allow(a, self.known)).cloned());
        let mut items = Vec::new();
        while self.peek() != Tok::RBrace {
            if self.peek() == Tok::Eof {
                return Err(syntax(self.span(), "expected `}`, found end of file"));
            }
            let before = self.pos;
            if let Some(item) = self.nest(|p| p.item())? {
                items.push(item);
            }
            if self.pos == before {
                return Err(syntax(self.span(), format!("expected an item, found {}", tok_name(self.peek()))));
            }
        }
        self.bump();
        self.scope_allows.truncate(scope_mark);
        Ok(ModDef { name, name_span, inner_attrs: inner.attrs, body: Some(items), span: start.to(self.prev_span()) })
    }

    /// A `const` item: `const NAME: Ty = value;` (`_` for an unnamed const).
    fn const_def(&mut self) -> PResult<ConstDef> {
        let start = self.expect(Tok::Const, "`const`")?;
        let (name, name_span) = if self.peek() == Tok::Underscore {
            (None, self.bump().span)
        } else {
            let (n, s) = self.ident()?;
            (Some(n), s)
        };
        self.expect(Tok::Colon, "`:`")?;
        let ty = self.ty()?;
        let (value, init_fn) = self.const_value(name.unwrap_or(Sym(0)), name_span)?;
        // A cfg-disabled node is only grammar-checked: rustc strips it
        // before the missing-body validation, so it stands there.
        if value.is_none() && !self.cfg_syntax {
            return Err(syntax(name_span, "free constant item without body"));
        }
        self.expect(Tok::Semi, "`;`")?;
        Ok(ConstDef { name, name_span, ty, value, span: start.to(self.prev_span()), init_fn })
    }

    /// The `= value` of a const, static, or associated const, if
    /// written, with the value as the body of a fn of its own: a block
    /// whose tail is the value, over the value's expr and pat ranges
    /// (`ConstDef::init_fn`).
    fn const_value(&mut self, name: Sym, name_span: Span) -> PResult<(Option<ExprId>, Option<Box<FnDef>>)> {
        if !self.eat(Tok::Eq) {
            return Ok((None, None));
        }
        let (e0, p0) = (self.ast.exprs.len() as u32, self.ast.pats.len() as u32);
        let outer = std::mem::replace(&mut self.in_body, true);
        let value = self.expr();
        self.in_body = outer;
        let value = value?;
        let def = self.value_body(name, name_span, value, e0, p0);
        Ok((Some(value), Some(Box::new(def))))
    }

    /// A fn with no parameters over the expr and pat ids from `e0` and
    /// `p0` on, whose body is a block with `value` as its tail: the
    /// check-only body of a const value (`ConstDef::init_fn`,
    /// `AnonConst::def`).
    fn value_body(&mut self, name: Sym, name_span: Span, value: ExprId, e0: u32, p0: u32) -> FnDef {
        let exprs = (e0, self.ast.exprs.len() as u32);
        let pats = (p0, self.ast.pats.len() as u32);
        let span = self.ast.expr_span(value);
        let body = self.push_block(Block { inner_attrs: Vec::new(), stmts: Vec::new(), tail: Some(value), tail_attrs: Vec::new(), span });
        FnDef {
            name,
            name_span,
            is_test: false,
            vis: Vis::Private,
            attrs: self.scope_allows.clone(),
            qual: FnQual::default(),
            generics: Generics::default(),
            self_param: None,
            params: Vec::new(),
            variadic: false,
            ret: None,
            where_clause: WhereClause::default(),
            body: Some(body),
            exprs,
            pats,
        }
    }

    /// Parses an anonymous const's expression with `parse`. Outside fn
    /// bodies, one that is no literal or one-segment path also becomes
    /// a body of its own (`Ast::anon_consts`).
    fn anon_const(&mut self, parse: impl FnOnce(&mut Self) -> PResult<ExprId>) -> PResult<ExprId> {
        let (e0, p0) = (self.ast.exprs.len() as u32, self.ast.pats.len() as u32);
        let outer = std::mem::replace(&mut self.in_body, true);
        let value = parse(self);
        self.in_body = outer;
        let value = value?;
        if !outer && !self.ast.is_plain_const(value) && !self.cfg_syntax {
            let span = self.ast.expr_span(value);
            let def = self.value_body(Sym(0), span, value, e0, p0);
            self.ast.anon_consts.push(AnonConst { value, def, module: None });
        }
        Ok(value)
    }

    /// A `static` item: `static [mut] NAME: Ty = value;`. A foreign
    /// static (the cfg syntax check's extern blocks) has no value.
    fn static_def(&mut self, foreign: bool) -> PResult<StaticDef> {
        let start = self.expect(Tok::Static, "`static`")?;
        let mutable = self.eat(Tok::Mut);
        let (name, name_span) = self.ident()?;
        self.expect(Tok::Colon, "`:`")?;
        let ty = self.ty()?;
        let (value, init_fn) = self.const_value(name, name_span)?;
        if value.is_none() && !foreign && !self.cfg_syntax {
            return Err(syntax(name_span, "free static item without body"));
        }
        self.expect(Tok::Semi, "`;`")?;
        Ok(StaticDef { name, name_span, mutable, ty, value, span: start.to(self.prev_span()), init_fn })
    }

    /// A `type` alias: `type Name = Target;`. Generic aliases reject with
    /// the generics code, like generic structs today.
    fn type_alias_def(&mut self) -> PResult<TypeAliasDef> {
        let start = self.expect(Tok::Type, "`type`")?;
        let (name, name_span) = self.ident()?;
        let generics = self.generics(true)?;
        // For an alias the where clause follows the target type.
        self.expect(Tok::Eq, "`=`")?;
        let ty = self.ty()?;
        let where_clause = self.where_clause()?;
        self.expect(Tok::Semi, "`;`")?;
        Ok(TypeAliasDef { name, name_span, generics, where_clause, ty, span: start.to(self.prev_span()) })
    }

    /// An `extern crate` item, after the qualifier loop ate `extern`:
    /// `crate name;` or `crate name as rename;` (`crate self as name;`
    /// for the crate itself).
    fn extern_crate_def(&mut self) -> PResult<ExternCrateDef> {
        let start = self.expect(Tok::Crate, "`crate`")?;
        let (name, name_span) = if self.peek() == Tok::SelfLower {
            let s = self.bump().span;
            (self.known.self_value, s)
        } else {
            self.ident()?
        };
        let rename = if self.eat(Tok::As) {
            Some(if self.peek() == Tok::Underscore {
                self.bump();
                self.interner.intern("_")
            } else {
                self.ident()?.0
            })
        } else {
            None
        };
        self.expect(Tok::Semi, "`;`")?;
        Ok(ExternCrateDef { name, name_span, rename, span: start.to(self.prev_span()) })
    }

    /// The children of a use group, after its `{`.
    fn use_group(&mut self) -> PResult<Vec<UseTree>> {
        let mut out = Vec::new();
        while self.peek() != Tok::RBrace {
            out.push(self.nest(|p| p.use_tree())?);
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(out)
    }

    /// One written lifetime ('a, 'static, '_) at the current token.
    fn lifetime_here(&mut self) -> PResult<Lifetime> {
        match self.peek() {
            Tok::Lifetime(name) => {
                let span = self.bump().span;
                self.check_lifetime_name(name, span, false);
                Ok(Lifetime { name, span })
            }
            t => Err(syntax(self.span(), format!("expected a lifetime, found {}", tok_name(t)))),
        }
    }

    /// Records rustc's error for a lifetime or label (`label`) named by a
    /// keyword (`'fn`; see `lexer::keyword_lifetime_error`). The parse goes
    /// on, as in rustc, so the error is deferred: fragment probes, which
    /// ignore deferred errors, read such names the way rustc's parser does.
    /// Added for fx-lex-small (W-CORELANG owns the parser).
    fn check_lifetime_name(&mut self, name: Sym, span: Span, label: bool) {
        let text = self.interner.get(name);
        if let Some(d) = crate::lexer::keyword_lifetime_error(text, crate::lexer::lifetime_is_raw(text, span), label, span) {
            self.defer(d);
        }
    }

    /// Generic parameters as written: `<..>`, or empty when absent.
    /// Additive parser work for W-CORELANG (the AST owner) on behalf
    /// of W-TRAITS-CORE: the shapes are the frozen AST v2 ones.
    /// Lifetime parameters keep the old L0203 reject where
    /// `allow_lifetimes` is false (type aliases and associated types);
    /// fns, structs, enums, impls, and traits record them (W-BORROW).
    fn generics(&mut self, allow_lifetimes: bool) -> PResult<Generics> {
        let start = self.span();
        if !self.eat(Tok::Lt) {
            return Ok(Generics { params: Vec::new(), span: start });
        }
        let mut params = Vec::new();
        loop {
            if self.eat(Tok::Gt) {
                break;
            }
            let pattrs = self.part_attributes("type parameters", 0)?;
            match self.peek() {
                Tok::Lifetime(_) => {
                    if !allow_lifetimes {
                        return Err(lifetime_error(self.span()));
                    }
                    let lt = self.lifetime_here()?;
                    let mut bounds = Vec::new();
                    if self.eat(Tok::Colon) {
                        loop {
                            bounds.push(self.lifetime_here()?);
                            if !self.eat(Tok::Plus) {
                                break;
                            }
                            if !matches!(self.peek(), Tok::Lifetime(_)) {
                                break;
                            }
                        }
                    }
                    params.push(GenericParam::Lifetime { lt, bounds, attrs: pattrs.attrs });
                }
                Tok::Const => {
                    self.bump();
                    let (name, span) = self.ident()?;
                    self.expect(Tok::Colon, "`:`")?;
                    let ty = self.ty()?;
                    let default = if self.eat(Tok::Eq) { Some(self.const_arg_expr()?) } else { None };
                    params.push(GenericParam::Const { name, span, ty, default, attrs: pattrs.attrs });
                }
                Tok::Ident(_) => {
                    let (name, span) = self.ident()?;
                    let bounds = if self.eat(Tok::Colon) { self.bounds()? } else { Vec::new() };
                    let default = if self.eat(Tok::Eq) { Some(self.ty()?) } else { None };
                    params.push(GenericParam::Type { name, span, bounds, default, attrs: pattrs.attrs });
                }
                t => return Err(syntax(self.span(), format!("expected a generic parameter, found {}", tok_name(t)))),
            }
            if !self.eat(Tok::Comma) {
                self.expect(Tok::Gt, "`>`")?;
                break;
            }
        }
        Ok(Generics { params, span: start.to(self.prev_span()) })
    }

    /// A `for<'a, ..>` binder in a bound, or empty when absent.
    fn opt_binder(&mut self) -> PResult<Vec<Lifetime>> {
        if self.peek() != Tok::For {
            return Ok(Vec::new());
        }
        self.bump();
        self.expect(Tok::Lt, "`<`")?;
        let mut out = Vec::new();
        loop {
            if self.eat(Tok::Gt) {
                break;
            }
            out.push(self.lifetime_here()?);
            if !self.eat(Tok::Comma) {
                self.expect(Tok::Gt, "`>`")?;
                break;
            }
        }
        Ok(out)
    }

    /// A trait path as written in a bound or impl header, with
    /// parenthesized sugar (`Fn(A) -> B`) attached to its last
    /// segment when present.
    fn trait_path(&mut self) -> PResult<Vec<PathSeg>> {
        let mut path = self.path(true)?;
        if self.peek() == Tok::LParen {
            self.bump();
            let mut inputs = Vec::new();
            while self.peek() != Tok::RParen {
                inputs.push(self.ty()?);
                if !self.eat(Tok::Comma) {
                    break;
                }
            }
            self.expect(Tok::RParen, "`)`")?;
            let output = if self.eat(Tok::Arrow) { Some(self.ty()?) } else { None };
            if let Some(last) = path.last_mut() {
                last.args = GenericArgs::Parenthesized { inputs, output };
            }
        }
        Ok(path)
    }

    /// One bound: a trait bound (optionally `for<..>`-bound and
    /// `?`-relaxed) or a lifetime bound.
    fn trait_bound(&mut self) -> PResult<TraitBound> {
        let binder = self.opt_binder()?;
        let maybe = self.eat(Tok::Question);
        if matches!(self.peek(), Tok::Lifetime(_)) && binder.is_empty() && !maybe {
            return Ok(TraitBound::Lifetime(self.lifetime_here()?));
        }
        // The legacy `~const` and `async` bound modifiers are not
        // in the subset; plain paths and `?Trait` are.
        let path = self.trait_path()?;
        // W-BORROW3: `for<'a> Fn(&'a T) -> &'a U` reads as `Fn(&T) -> &U`.
        if !binder.is_empty()
            && let Some(GenericArgs::Parenthesized { inputs, output }) = path.last().map(|s| s.args.clone())
        {
            self.canon_binder(&binder, &inputs, output)?;
        }
        Ok(TraitBound::Trait { binder, trait_ref: TraitRefExpr { path }, maybe })
    }

    /// A `+`-separated bound list, at least one bound. A trailing
    /// `+` before the list's terminator ends the list.
    fn bounds(&mut self) -> PResult<Vec<TraitBound>> {
        let mut out = Vec::new();
        loop {
            out.push(self.trait_bound()?);
            if !self.eat(Tok::Plus) {
                break;
            }
            if matches!(self.peek(), Tok::Comma | Tok::Gt | Tok::LBrace | Tok::Semi | Tok::RParen | Tok::Eq) {
                break;
            }
        }
        Ok(out)
    }

    /// An `impl Trait`'s bound list: `bounds`, where one entry may be a
    /// `use<..>` precise-capturing list (rustc rejects a second one, and
    /// one anywhere but an `impl Trait`, which `trait_bound` cannot read).
    fn impl_bounds(&mut self) -> PResult<(Vec<TraitBound>, Option<UseCaps>)> {
        let (mut out, mut captures) = (Vec::new(), None);
        loop {
            if self.peek() == Tok::Use {
                let c = self.use_caps()?;
                if captures.is_some() {
                    return Err(syntax(c.span, "duplicate `use<...>` precise capturing syntax"));
                }
                captures = Some(c);
            } else {
                out.push(self.trait_bound()?);
            }
            if !self.eat(Tok::Plus) {
                break;
            }
            if matches!(self.peek(), Tok::Comma | Tok::Gt | Tok::LBrace | Tok::Semi | Tok::RParen | Tok::Eq) {
                break;
            }
        }
        if out.is_empty() {
            return Err(syntax(self.prev_span(), "at least one trait must be specified"));
        }
        Ok((out, captures))
    }

    /// `use<'a, T, ..>`: lifetimes (`'_` included) and type or const
    /// param names (`Self` too), comma separated. `'static` is not a param.
    fn use_caps(&mut self) -> PResult<UseCaps> {
        let start = self.expect(Tok::Use, "`use`")?;
        self.expect(Tok::Lt, "`<`")?;
        let mut args = Vec::new();
        while self.peek() != Tok::Gt {
            match self.peek() {
                Tok::Lifetime(_) => {
                    let lt = self.lifetime_here()?;
                    if self.interner.get(lt.name) == "static" {
                        return Err(syntax(lt.span, "expected lifetime parameter in `use<...>` precise captures list, found `'static`"));
                    }
                    args.push(UseArg::Lifetime(lt));
                }
                _ => {
                    let (name, span) = self.ident()?;
                    args.push(UseArg::Param(name, span));
                }
            }
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::Gt, "`>`")?;
        Ok(UseCaps { args, span: start.to(self.prev_span()) })
    }

    /// A `where` clause as written, or empty when absent.
    fn where_clause(&mut self) -> PResult<WhereClause> {
        let start = self.span();
        if !self.eat(Tok::Where) {
            return Ok(WhereClause { preds: Vec::new(), span: start });
        }
        let mut preds = Vec::new();
        loop {
            if matches!(self.peek(), Tok::LBrace | Tok::Semi) {
                break;
            }
            if matches!(self.peek(), Tok::Lifetime(_)) {
                let lt = self.lifetime_here()?;
                self.expect(Tok::Colon, "`:`")?;
                let mut bounds = Vec::new();
                loop {
                    bounds.push(self.lifetime_here()?);
                    if !self.eat(Tok::Plus) {
                        break;
                    }
                    if !matches!(self.peek(), Tok::Lifetime(_)) {
                        break;
                    }
                }
                preds.push(WherePred::Lifetime { lt, bounds });
            } else {
                let binder = self.opt_binder()?;
                let ty = self.ty()?;
                self.expect(Tok::Colon, "`:`")?;
                let bounds = self.bounds()?;
                preds.push(WherePred::Type { binder, ty, bounds });
            }
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        Ok(WhereClause { preds, span: start.to(self.prev_span()) })
    }

    fn fn_def(&mut self) -> PResult<FnDef> {
        self.fn_def_inner(false)
    }

    /// A fn definition. With `sig_only`, a trailing `;` instead of a
    /// body is a bodyless declaration (a trait method signature).
    fn fn_def_inner(&mut self, sig_only: bool) -> PResult<FnDef> {
        self.expect(Tok::Fn, "`fn`")?;
        let (name, name_span) = self.ident()?;
        let generics = self.generics(true)?;
        self.expect(Tok::LParen, "`(`")?;
        let mut self_param = None;
        let mut params = Vec::new();
        // `self`, `mut self`, `&self`, `&mut self`, the same with a
        // written lifetime, and typed receivers (`self: Rc<Self>`).
        let s = self.span();
        let typed_self = (self.peek() == Tok::SelfLower && self.peek_at(1) == Tok::Colon)
            || (self.peek() == Tok::Mut && self.peek_at(1) == Tok::SelfLower && self.peek_at(2) == Tok::Colon);
        if typed_self {
            let mutable = self.eat(Tok::Mut);
            self.bump(); // `self`
            self.bump(); // `:`
            let ty = self.ty()?;
            self_param = Some(SelfParam {
                kind: SelfKind::Typed,
                mutable,
                lifetime: None,
                ty: Some(ty),
                attrs: Vec::new(),
                span: s.to(self.prev_span()),
            });
            if !self.eat(Tok::Comma) && self.peek() != Tok::RParen {
                return Err(syntax(self.span(), "expected `,` or `)`"));
            }
        }
        let self_form = if typed_self {
            None
        } else {
            match (self.peek(), self.peek_at(1), self.peek_at(2), self.peek_at(3)) {
                (Tok::SelfLower, _, _, _) => Some((SelfKind::Value, false, 1, None)),
                (Tok::Mut, Tok::SelfLower, _, _) => Some((SelfKind::Value, true, 2, None)),
                (Tok::Amp, Tok::SelfLower, _, _) => Some((SelfKind::Ref, false, 2, None)),
                (Tok::Amp, Tok::Mut, Tok::SelfLower, _) => Some((SelfKind::RefMut, false, 3, None)),
                (Tok::Amp, Tok::Lifetime(lt), Tok::SelfLower, _) => {
                    Some((SelfKind::Ref, false, 3, Some(Lifetime { name: lt, span: self.toks[self.pos + 1].span })))
                }
                (Tok::Amp, Tok::Lifetime(lt), Tok::Mut, Tok::SelfLower) => {
                    Some((SelfKind::RefMut, false, 4, Some(Lifetime { name: lt, span: self.toks[self.pos + 1].span })))
                }
                _ => None,
            }
        };
        if let Some((kind, mutable, n, lifetime)) = self_form {
            if let Some(lt) = lifetime {
                self.check_lifetime_name(lt.name, lt.span, false);
            }
            for _ in 0..n {
                self.bump();
            }
            self_param = Some(SelfParam { kind, mutable, lifetime, ty: None, attrs: Vec::new(), span: s.to(self.prev_span()) });
            if !self.eat(Tok::Comma) && self.peek() != Tok::RParen {
                return Err(syntax(self.span(), "expected `,` or `)`"));
            }
        }
        // Parameter patterns belong to the fn's own expr and pat
        // ranges, like its body: the checker indexes its tables
        // by them.
        let (e0, p0) = (self.ast.exprs.len() as u32, self.ast.pats.len() as u32);
        while self.peek() != Tok::RParen {
            let pattrs = self.part_attributes("function parameters", attrs::T_PARAM)?;
            let start = self.span();
            if self.cfg_syntax && self.cfg_foreign && (self.peek() == Tok::DotDot || self.peek() == Tok::Ellipsis) {
                self.bump();
                if self.peek() == Tok::Dot {
                    self.bump();
                }
                break;
            }
            if self.peek() == Tok::DotDot {
                return Err(self.reject(C_CORE, "variadic parameters"));
            }
            // The plain `name: Ty` and `mut name: Ty` forms keep
            // the exact name span: hygiene reads the name token's
            // context as the binding's context (ARCH 6.3).
            let plain = (matches!(self.peek(), Tok::Ident(_) | Tok::Reserved(_)) && self.peek_at(1) == Tok::Colon)
                || (self.peek() == Tok::Mut && matches!(self.peek_at(1), Tok::Ident(_)) && self.peek_at(2) == Tok::Colon);
            if plain {
                let mutable = self.eat(Tok::Mut);
                let (pname, pspan) = match self.peek() {
                    Tok::Ident(_) => self.ident()?,
                    Tok::Reserved(_) => return Err(self.reserved_error(self.span())),
                    _ => unreachable!(),
                };
                self.expect(Tok::Colon, "`:`")?;
                let ty = self.ty()?;
                // A type from another context (a macro's `$ty` fragment)
                // must not move the binding's context to the call site:
                // the span stays the name's then.
                let end = self.prev_span();
                let span = if end.ctxt == pspan.ctxt { pspan.to(end) } else { pspan };
                params.push(Param { name: pname, mutable, pat: None, ty, attrs: pattrs.attrs, span });
            } else {
                let pat = self.pattern_no_top_alt("function parameters require top-level or-patterns in parentheses")?;
                self.expect(Tok::Colon, "`:`")?;
                let ty = self.ty()?;
                let span = start.to(self.prev_span());
                params.push(Param { name: Sym(0), mutable: false, pat: Some(pat), ty, attrs: pattrs.attrs, span });
            }
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RParen, "`)`")?;
        let ret = if self.eat(Tok::Arrow) { Some(self.ret_ty()?) } else { None };
        let where_clause = self.where_clause()?;
        // A fn body block permits inner attributes at its start.
        self.block_inner_ok = true;
        let body = if sig_only && self.eat(Tok::Semi) {
            self.block_inner_ok = false;
            None
        } else {
            let outer = std::mem::replace(&mut self.in_body, true);
            let body = self.block();
            self.in_body = outer;
            Some(body?)
        };
        // Patterns are not allowed in functions without bodies
        // (rustc E0642): a trait signature takes plain names and
        // `_` only.
        if body.is_none() && !self.cfg_syntax {
            for param in &params {
                if let Some(pat) = param.pat
                    && !matches!(self.ast.pat(pat), Pat::Wild)
                {
                    return Err(syntax(param.span, "patterns are not allowed in functions without bodies"));
                }
            }
            // `mut x` is rustc's deny-by-default lint
            // `patterns_in_fns_without_body`, lifted by an `#[allow]` on
            // the fn or an enclosing scope.
            let mut_span = params.iter().find(|p| p.mutable).map(|p| p.span).or(self_param.as_ref().filter(|s| s.mutable).map(|s| s.span));
            if let Some(span) = mut_span
                && !self.lint_allowed(&[], "patterns_in_fns_without_body")
                && !self.lint_allowed(&[], "future_incompatible")
            {
                return Err(Diag::new(
                    "L0524",
                    span,
                    "patterns aren't allowed in functions without bodies",
                    "Remove the `mut`: a signature without a body takes plain names (rustc `patterns_in_fns_without_body`).",
                ));
            }
        }
        let exprs = (e0, self.ast.exprs.len() as u32);
        let pats = (p0, self.ast.pats.len() as u32);
        Ok(FnDef {
            name,
            name_span,
            is_test: false,
            vis: Vis::Private,
            // Seeded with the enclosing scopes' allows; the caller prepends
            // this function's own outer attributes.
            attrs: self.scope_allows.clone(),
            qual: FnQual::default(),
            generics,
            self_param,
            params,
            variadic: false,
            ret,
            where_clause,
            body,
            exprs,
            pats,
        })
    }

    fn fields(&mut self) -> PResult<Vec<FieldDef>> {
        self.expect(Tok::LBrace, "`{`")?;
        let mut fields = Vec::new();
        while self.peek() != Tok::RBrace {
            let fattrs = self.part_attributes("struct fields", attrs::T_FIELD)?;
            let vis = self.vis()?;
            let (name, span) = self.ident()?;
            self.expect(Tok::Colon, "`:`")?;
            let ty = self.ty()?;
            fields.push(FieldDef { name, vis, attrs: fattrs.attrs, ty, span });
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(fields)
    }

    /// Tuple variant fields after the `(`: types with optional attributes.
    /// `FieldDef::name` is unused for these (see `StructDef::fields`).
    fn tuple_fields(&mut self) -> PResult<Vec<FieldDef>> {
        let mut fields = Vec::new();
        while self.peek() != Tok::RParen {
            let fattrs = self.part_attributes("struct fields", attrs::T_FIELD)?;
            let _vis = self.vis_ctx(true)?;
            let span = self.span();
            let ty = self.ty()?;
            fields.push(FieldDef { name: Sym(0), vis: _vis, attrs: fattrs.attrs, ty, span });
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RParen, "`)`")?;
        Ok(fields)
    }

    fn struct_def(&mut self, derives: Vec<(Sym, Span)>) -> PResult<StructDef> {
        self.expect(Tok::Struct, "`struct`")?;
        let (name, name_span) = self.ident()?;
        let generics = self.generics(true)?;
        // The where clause sits before the fields (named struct),
        // before the `;` (unit struct), or after the fields and
        // before the `;` (tuple struct), as in rustc's grammar.
        let mut where_clause = self.where_clause()?;
        let fields = match self.peek() {
            Tok::Semi => {
                self.bump();
                VariantFields::Unit
            }
            Tok::LParen => {
                self.bump();
                let fs = self.tuple_fields()?;
                let tail = self.where_clause()?;
                if !tail.preds.is_empty() {
                    if !where_clause.preds.is_empty() {
                        return Err(syntax(tail.span, "duplicate `where` clauses on an item"));
                    }
                    where_clause = tail;
                }
                self.expect(Tok::Semi, "`;`")?;
                VariantFields::Tuple(fs)
            }
            _ => VariantFields::Struct(self.fields()?),
        };
        Ok(StructDef { name, name_span, generics, fields, where_clause, derives })
    }

    fn enum_def(&mut self, derives: Vec<(Sym, Span)>) -> PResult<EnumDef> {
        self.expect(Tok::Enum, "`enum`")?;
        let (name, name_span) = self.ident()?;
        let generics = self.generics(true)?;
        let where_clause = self.where_clause()?;
        self.expect(Tok::LBrace, "`{`")?;
        let mut variants = Vec::new();
        while self.peek() != Tok::RBrace {
            let vattrs = self.variant_attributes()?;
            let (vname, span) = self.ident()?;
            let fields = match self.peek() {
                Tok::LParen => {
                    self.bump();
                    VariantFields::Tuple(self.tuple_fields()?)
                }
                Tok::LBrace => VariantFields::Struct(self.fields()?),
                _ => VariantFields::Unit,
            };
            let discriminant = if self.eat(Tok::Eq) { Some(self.anon_const(|p| p.expr())?) } else { None };
            variants.push(VariantDef { name: vname, attrs: vattrs.attrs, fields, discriminant, span });
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(EnumDef { name, name_span, generics, variants, where_clause, derives })
    }

    /// One associated type in a trait or an impl:
    /// `type Name<..>: Bounds = Default;` (parts optional by context;
    /// collect checks which parts each context requires).
    fn assoc_type(&mut self) -> PResult<AssocTypeDef> {
        let start = self.expect(Tok::Type, "`type`")?;
        let (name, name_span) = self.ident()?;
        let generics = self.generics(true)?;
        let bounds = if self.eat(Tok::Colon) { self.bounds()? } else { Vec::new() };
        let where_clause = self.where_clause()?;
        let default = if self.eat(Tok::Eq) { Some(self.ty()?) } else { None };
        self.expect(Tok::Semi, "`;`")?;
        Ok(AssocTypeDef {
            name,
            name_span,
            vis: Vis::Private,
            attrs: Vec::new(),
            generics,
            bounds,
            where_clause,
            default,
            span: start.to(self.prev_span()),
        })
    }

    /// One associated const in a trait or an impl:
    /// `const NAME: Ty = value;` (the value is optional in a trait).
    fn assoc_const(&mut self) -> PResult<AssocConstDef> {
        // Scalar associated consts in inherent impls are supported
        // (collect evaluates them); trait definitions still defer
        // their own L0614, and trait impls defer in `impl_def`.
        let start = self.expect(Tok::Const, "`const`")?;
        let (name, name_span) = self.ident()?;
        self.expect(Tok::Colon, "`:`")?;
        let ty = self.ty()?;
        let (default, init_fn) = self.const_value(name, name_span)?;
        self.expect(Tok::Semi, "`;`")?;
        Ok(AssocConstDef { name, name_span, vis: Vis::Private, attrs: Vec::new(), ty, default, span: start.to(self.prev_span()), init_fn })
    }

    /// A trait definition: supertrait bounds, a where clause, and
    /// method signatures (with optional default bodies), associated
    /// types, and associated consts.
    fn trait_def(&mut self) -> PResult<TraitDef> {
        let start = self.expect(Tok::Trait, "`trait`")?;
        let (name, name_span) = self.ident()?;
        let generics = self.generics(true)?;
        let bounds = if self.eat(Tok::Colon) { self.bounds()? } else { Vec::new() };
        let where_clause = self.where_clause()?;
        self.expect(Tok::LBrace, "`{`")?;
        // Inner attributes are permitted only here, before the first item.
        let inner = self.inner_attributes()?;
        let scope_mark = self.scope_allows.len();
        self.scope_allows.extend(inner.attrs.iter().filter(|a| is_allow(a, self.known)).cloned());
        let mut fns = Vec::new();
        let mut consts = Vec::new();
        let mut types = Vec::new();
        while self.peek() != Tok::RBrace {
            let parsed = self.attributes()?;
            // A trait item is neither an ADT nor a free function.
            self.check_derive_test(&parsed, false, false)?;
            self.check_assoc_targets(&parsed, false)?;
            // Trait items are as visible as their trait.
            let vis_start = self.span();
            let vis = self.vis()?;
            if vis != Vis::Private && !self.cfg_syntax {
                return Err(vis_not_permitted(vis_start.to(self.prev_span())));
            }
            // The item's own `#[allow]`s scope over its signature checks.
            let item_mark = self.scope_allows.len();
            self.scope_allows.extend(parsed.attrs.iter().filter(|a| is_allow(a, self.known)).cloned());
            match self.peek() {
                Tok::Fn => {
                    let mut def = self.fn_def_inner(true)?;
                    def.vis = vis;
                    let mut attrs = parsed.attrs;
                    attrs.extend(def.attrs);
                    def.attrs = attrs;
                    fns.push(def);
                }
                Tok::Type => types.push(self.assoc_type()?),
                Tok::Const if matches!(self.peek_at(1), Tok::Ident(_) | Tok::Underscore) => consts.push(self.assoc_const()?),
                Tok::Const | Tok::Unsafe | Tok::Async | Tok::Extern if self.cfg_syntax => {
                    while matches!(self.peek(), Tok::Const | Tok::Unsafe | Tok::Async) {
                        self.bump();
                    }
                    if self.eat(Tok::Extern) && matches!(self.peek(), Tok::Str(..)) {
                        self.bump();
                    }
                    let mut def = self.fn_def_inner(true)?;
                    def.vis = vis;
                    let mut attrs = parsed.attrs;
                    attrs.extend(def.attrs);
                    def.attrs = attrs;
                    fns.push(def);
                }
                // Const fns in traits are unstable in Rust
                // (E0379) and unsupported here.
                // Qualifiers with no item after them are a grammar error.
                Tok::Const | Tok::Unsafe | Tok::Async | Tok::Extern if self.quals_then_end() => {
                    return Err(syntax(self.span(), "expected an item after qualifiers"));
                }
                Tok::Const if self.peek_at(1) == Tok::Fn => return Err(self.reject(C_CONST, "const functions in traits")),
                Tok::Const => return Err(self.reject(C_CONST, "const functions")),
                Tok::Unsafe => return Err(unsafe_error(self.span())),
                Tok::Async => return Err(async_error(self.span())),
                Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super | Tok::SelfLower if self.cfg_syntax && self.at_path_macro_call() => {
                    self.skip_macro_invocation()?;
                    self.eat(Tok::Semi);
                }
                Tok::Ident(_) | Tok::SelfUpper if self.at_path_macro_call() => return Err(macro_error(self.span())),
                t => return Err(syntax(self.span(), format!("expected a trait item, found {}", tok_name(t)))),
            }
            self.scope_allows.truncate(item_mark);
        }
        self.expect(Tok::RBrace, "`}`")?;
        self.scope_allows.truncate(scope_mark);
        Ok(TraitDef {
            inner_attrs: inner.attrs,
            name,
            name_span,
            is_unsafe: false,
            is_auto: false,
            generics,
            bounds,
            where_clause,
            fns,
            consts,
            types,
            span: start.to(self.prev_span()),
        })
    }

    /// An inherent or trait impl. The header before the `{` is
    /// either a Self type or `TraitRef for SelfType`: a path is
    /// parsed once, and a following `for` makes it the trait ref.
    fn impl_def(&mut self, is_unsafe: bool) -> PResult<ImplDef> {
        let start = self.expect(Tok::Impl, "`impl`")?;
        let generics = self.generics(true)?;
        let is_negative = self.eat(Tok::Bang);
        // A trait path may also start with `crate`, `super`, `self`, or
        // `::` (`impl crate::a::Trait for T`): `path` reads the anchor as
        // a first segment and the resolver rewrites it, as in a bound.
        // An inherent impl's Self type may start the same way.
        let path_start = matches!(self.peek(), Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super | Tok::SelfLower | Tok::PathSep);
        let (trait_ref, self_ty) = if path_start {
            let header_start = self.span();
            let path = self.trait_path()?;
            if self.eat(Tok::For) {
                let self_ty = self.ty()?;
                (Some(TraitRefExpr { path }), self_ty)
            } else if is_negative {
                return Err(syntax(header_start, "expected `for` after the trait in a negative impl"));
            } else {
                let span = header_start.to(self.prev_span());
                (None, self.push_ty(TyExpr::Path(path), span))
            }
        } else {
            let self_ty = self.ty()?;
            if self.peek() == Tok::For {
                return Err(syntax(self.span(), "expected a trait path before `for` in an impl"));
            }
            (None, self_ty)
        };
        if trait_ref.is_some() || is_negative {}
        let where_clause = self.where_clause()?;
        self.expect(Tok::LBrace, "`{`")?;
        // Inner attributes are permitted only here, before the first item.
        let inner = self.inner_attributes()?;
        let scope_mark = self.scope_allows.len();
        self.scope_allows.extend(inner.attrs.iter().filter(|a| is_allow(a, self.known)).cloned());
        let mut fns = Vec::new();
        let mut consts = Vec::new();
        let mut types = Vec::new();
        while self.peek() != Tok::RBrace {
            let parsed = self.attributes()?;
            // An impl item is neither an ADT nor a free function.
            self.check_derive_test(&parsed, false, false)?;
            self.check_assoc_targets(&parsed, trait_ref.is_some())?;
            // Trait impl items take the trait's visibility.
            let vis_start = self.span();
            let vis = self.vis()?;
            if trait_ref.is_some() && vis != Vis::Private && !self.cfg_syntax {
                return Err(vis_not_permitted(vis_start.to(self.prev_span())));
            }
            match self.peek() {
                Tok::Fn => {
                    let mut def = self.fn_def()?;
                    def.vis = vis;
                    let mut attrs = parsed.attrs;
                    attrs.extend(def.attrs);
                    def.attrs = attrs;
                    fns.push(def);
                }
                Tok::Type if trait_ref.is_some() || self.cfg_syntax => types.push(self.assoc_type()?),
                Tok::Type => return Err(self.reject(C_ASSOC, "associated types in inherent impls")),
                Tok::Const if matches!(self.peek_at(1), Tok::Ident(_) | Tok::Underscore) => {
                    let mut def = self.assoc_const()?;
                    def.vis = vis;
                    consts.push(def);
                }
                Tok::Const if self.peek_at(1) == Tok::Fn => {
                    self.bump();
                    let mut def = self.fn_def()?;
                    def.vis = vis;
                    let mut attrs = parsed.attrs;
                    attrs.extend(def.attrs);
                    def.attrs = attrs;
                    def.qual.is_const = true;
                    fns.push(def);
                }
                Tok::Unsafe | Tok::Async | Tok::Extern if self.cfg_syntax => {
                    while matches!(self.peek(), Tok::Unsafe | Tok::Async | Tok::Const) {
                        self.bump();
                    }
                    if self.eat(Tok::Extern) && matches!(self.peek(), Tok::Str(..)) {
                        self.bump();
                    }
                    let mut def = self.fn_def()?;
                    def.vis = vis;
                    let mut attrs = parsed.attrs;
                    attrs.extend(def.attrs);
                    def.attrs = attrs;
                    fns.push(def);
                }
                // Qualifiers with no item after them are a grammar error.
                Tok::Const | Tok::Unsafe | Tok::Async | Tok::Extern if self.quals_then_end() => {
                    return Err(syntax(self.span(), "expected an item after qualifiers"));
                }
                Tok::Const => return Err(self.reject(C_CONST, "const functions")),
                Tok::Unsafe => return Err(unsafe_error(self.span())),
                Tok::Async => return Err(async_error(self.span())),
                Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super | Tok::SelfLower if self.cfg_syntax && self.at_path_macro_call() => {
                    self.skip_macro_invocation()?;
                    self.eat(Tok::Semi);
                }
                Tok::Ident(_) | Tok::SelfUpper if self.at_path_macro_call() => return Err(macro_error(self.span())),
                t => return Err(syntax(self.span(), format!("expected an impl item, found {}", tok_name(t)))),
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        self.scope_allows.truncate(scope_mark);
        Ok(ImplDef {
            inner_attrs: inner.attrs,
            generics,
            is_unsafe,
            is_negative,
            in_body: false,
            trait_ref,
            self_ty,
            where_clause,
            fns,
            consts,
            types,
            span: start,
        })
    }

    // ---------- Types ----------

    fn ty(&mut self) -> PResult<TyId> {
        self.nest(|p| p.ty_inner())
    }

    /// The type after `->` in a fn, fn pointer, or closure: the one
    /// place where a written `!` is stable (rustc gates it in `Fn() -> !`
    /// sugar too).
    fn ret_ty(&mut self) -> PResult<TyId> {
        let start = self.span();
        if self.peek() == Tok::Bang {
            self.bump();
            return Ok(self.push_ty(TyExpr::Never, start.to(self.prev_span())));
        }
        self.ty()
    }

    fn ty_inner(&mut self) -> PResult<TyId> {
        let start = self.span();
        match self.peek() {
            Tok::Amp | Tok::AndAnd => {
                let double = self.bump().tok == Tok::AndAnd;
                // Written lifetimes are recorded; regions are erased
                // in this milestone, and collect decides which
                // written forms the subset accepts.
                let lifetime = if matches!(self.peek(), Tok::Lifetime(_)) {
                    let lt = self.lifetime_here()?;
                    Some(lt)
                } else {
                    None
                };
                let mutable = self.eat(Tok::Mut);
                let bare_bounds = matches!(self.peek(), Tok::Dyn | Tok::Impl);
                let inner = self.ty()?;
                let span = start.to(self.prev_span());
                // rustc E0178: after `&`, a `dyn` or `impl` type takes one
                // bound; `&dyn A + Send` must be written `&(dyn A + Send)`.
                if bare_bounds {
                    let n = match self.ast.ty(inner) {
                        TyExpr::Dyn { bounds, lifetime, .. } => bounds.len() + usize::from(lifetime.is_some()),
                        TyExpr::ImplTrait { bounds, captures } => bounds.len() + usize::from(captures.is_some()),
                        _ => 1,
                    };
                    if n > 1 {
                        return Err(syntax(span, "ambiguous `+` in a type: write `&(dyn A + B)`".to_string()));
                    }
                }
                let mut t = self.push_ty(TyExpr::Ref { lifetime, mutable, inner }, span);
                if double {
                    t = self.push_ty(TyExpr::Ref { lifetime: None, mutable: false, inner: t }, span);
                }
                Ok(t)
            }
            Tok::LParen => {
                self.bump();
                if self.eat(Tok::RParen) {
                    return Ok(self.push_ty(TyExpr::Unit, start.to(self.prev_span())));
                }
                let mut elems = vec![self.ty()?];
                let mut tuple = false;
                while self.eat(Tok::Comma) {
                    tuple = true;
                    if self.peek() == Tok::RParen {
                        break;
                    }
                    elems.push(self.ty()?);
                }
                self.expect(Tok::RParen, "`)`")?;
                if tuple {
                    Ok(self.push_ty(TyExpr::Tuple(elems), start.to(self.prev_span())))
                } else {
                    self.paren_tys.push(elems[0].0);
                    Ok(elems[0])
                }
            }
            Tok::LBracket => {
                self.bump();
                let inner = self.ty()?;
                if self.eat(Tok::Semi) {
                    let len = self.anon_const(|p| p.expr())?;
                    self.expect(Tok::RBracket, "`]`")?;
                    Ok(self.push_ty(TyExpr::Array { inner, len }, start.to(self.prev_span())))
                } else {
                    self.expect(Tok::RBracket, "`]`")?;
                    Ok(self.push_ty(TyExpr::Slice(inner), start.to(self.prev_span())))
                }
            }
            Tok::Impl => {
                self.bump();
                let (bounds, captures) = self.impl_bounds()?;
                Ok(self.push_ty(TyExpr::ImplTrait { bounds, captures }, start.to(self.prev_span())))
            }
            Tok::Dyn => {
                self.bump();
                let binder = self.opt_binder()?;
                let mut bounds = self.bounds()?;
                // W-BORROW3: `dyn for<'a> Fn(&'a T)` as `dyn Fn(&T)`.
                if let Some(TraitBound::Trait { trait_ref, .. }) = bounds.first()
                    && let Some(GenericArgs::Parenthesized { inputs, output }) = trait_ref.path.last().map(|s| s.args.clone())
                {
                    self.canon_binder(&binder, &inputs, output)?;
                }
                // A trailing lifetime bound is the dyn lifetime.
                let lifetime = match bounds.last() {
                    Some(TraitBound::Lifetime(lt)) if bounds.len() > 1 => {
                        let lt = *lt;
                        bounds.pop();
                        Some(lt)
                    }
                    _ => None,
                };
                Ok(self.push_ty(TyExpr::Dyn { binder, bounds, lifetime }, start.to(self.prev_span())))
            }
            Tok::Fn => {
                // A plain function pointer type: `fn(A, B) -> R`, with
                // optionally named inputs. `unsafe fn`, `extern fn`, and
                // variadic forms stay rejected below (they reach here
                // only as the bare `fn` token).
                self.bump();
                self.expect(Tok::LParen, "`(` after `fn`")?;
                let mut inputs = Vec::new();
                let mut variadic = false;
                while self.peek() != Tok::RParen {
                    if (self.peek() == Tok::DotDot && self.peek_at(1) == Tok::Dot) || (self.cfg_syntax && self.peek() == Tok::Ellipsis) {
                        variadic = true;
                        if self.cfg_syntax {
                            self.bump();
                            if self.peek() == Tok::Dot {
                                self.bump();
                            }
                        }
                        break;
                    }
                    let pstart = self.span();
                    let name = if matches!(self.peek(), Tok::Ident(_)) && self.peek_at(1) == Tok::Colon {
                        let Tok::Ident(n) = self.bump().tok else { unreachable!() };
                        self.bump();
                        Some(n)
                    } else {
                        None
                    };
                    let ty = self.ty()?;
                    inputs.push(crate::ast::FtyParam { name, ty, attrs: Vec::new(), span: pstart.to(self.prev_span()) });
                    if !self.eat(Tok::Comma) {
                        break;
                    }
                }
                self.expect(Tok::RParen, "`)`")?;
                if variadic && !self.cfg_syntax {
                    return Err(not_yet(C_TY, start, "variadic function pointer types"));
                }
                let ret = if self.eat(Tok::Arrow) { Some(self.ret_ty()?) } else { None };
                Ok(self.push_ty(
                    TyExpr::FnPtr { binder: Vec::new(), qual: FnQual::default(), inputs, variadic: false, ret },
                    start.to(self.prev_span()),
                ))
            }
            Tok::Star => {
                self.bump();
                let mutable = if self.eat(Tok::Mut) {
                    true
                } else if self.eat(Tok::Const) {
                    false
                } else {
                    return Err(syntax(self.span(), "expected `const` or `mut` after `*` in a raw pointer type"));
                };
                let inner = self.ty()?;
                Ok(self.push_ty(TyExpr::Ptr { mutable, inner }, start.to(self.prev_span())))
            }
            Tok::Bang => {
                // A written `!` is stable only as a whole return type
                // (`ret_ty`); rustc gates every other position (E0658,
                // `never_type`). Cfg-disabled code is not gated.
                self.bump();
                if !self.cfg_syntax {
                    return Err(Diag::new(
                        "L0603",
                        start,
                        "the `!` type is unstable outside a function return type",
                        "Use an empty enum (`enum Never {}`) or `std::convert::Infallible`.",
                    ));
                }
                Ok(self.push_ty(TyExpr::Never, start.to(self.prev_span())))
            }
            Tok::Underscore => {
                self.bump();
                Ok(self.push_ty(TyExpr::Infer, start.to(self.prev_span())))
            }
            Tok::Unsafe if self.cfg_syntax => {
                self.bump();
                self.ty()
            }
            Tok::Unsafe => Err(unsafe_error(start)),
            Tok::Extern if self.cfg_syntax => {
                self.bump();
                if matches!(self.peek(), Tok::Str(..)) {
                    self.bump();
                }
                self.ty()
            }
            Tok::Extern => Err(not_yet(C_TY, start, "extern function types")),
            Tok::Lt | Tok::Shl => {
                let (self_ty, trait_path, segs) = self.qpath_parts()?;
                Ok(self.push_ty(TyExpr::QPath { self_ty, trait_path, segs }, start.to(self.prev_span())))
            }
            Tok::For if self.cfg_syntax => {
                let _binder = self.opt_binder()?;
                self.ty()
            }
            // W-BORROW3: `for<'a> fn(&'a T) -> &'a U`, read as the elided
            // form when it means the same (`canon_binder`).
            Tok::For if self.peek_at(1) == Tok::Lt && self.peek_at(2) != Tok::Gt => {
                let binder = self.opt_binder()?;
                if self.peek() != Tok::Fn {
                    return Err(not_yet(C_TRAIT, start, "higher-ranked (`for<..>`) types other than fn pointers"));
                }
                let t = self.ty()?;
                let TyExpr::FnPtr { inputs, ret, .. } = &self.ast.tys[t.0 as usize] else {
                    return Err(not_yet(C_TRAIT, start, "higher-ranked (`for<..>`) types other than fn pointers"));
                };
                let (inputs, ret): (Vec<TyId>, Option<TyId>) = (inputs.iter().map(|p| p.ty).collect(), *ret);
                self.canon_binder(&binder, &inputs, ret)?;
                if let TyExpr::FnPtr { binder: b, .. } = &mut self.ast.tys[t.0 as usize] {
                    *b = binder;
                }
                Ok(t)
            }
            Tok::For => Err(not_yet(C_TRAIT, start, "higher-ranked (`for<..>`) types and bounds")),
            Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super | Tok::SelfLower if self.cfg_syntax && self.at_path_macro_call() => {
                let (span, _) = self.skip_macro_invocation()?;
                Ok(self.push_ty(TyExpr::Unit, span))
            }
            Tok::Ident(_) | Tok::SelfUpper if self.at_path_macro_call() => Err(macro_error(start)),
            _ => {
                let path = self.path(true)?;
                Ok(self.push_ty(TyExpr::Path(path), start.to(self.prev_span())))
            }
        }
    }

    /// The parts of a qualified path, current token at `<`:
    /// `<SelfTy as Trait>::Segs`, or `<SelfTy>::Segs` with an empty
    /// trait path. Shared by type and expression position.
    fn qpath_parts(&mut self) -> PResult<(TyId, Vec<PathSeg>, Vec<PathSeg>)> {
        self.expect(Tok::Lt, "`<`")?;
        let self_ty = self.ty()?;
        let trait_path = if self.eat(Tok::As) { self.trait_path()? } else { Vec::new() };
        self.expect(Tok::Gt, "`>`")?;
        self.expect(Tok::PathSep, "`::`")?;
        let segs = self.path(true)?;
        Ok((self_ty, trait_path, segs))
    }

    /// A const generic argument expression: a literal, a path to a
    /// const item or parameter, a negated literal, or a braced
    /// block. Anything that would need an operator must be braced,
    /// as in Rust, so `>` is never eaten as a comparison here.
    fn const_arg_expr(&mut self) -> PResult<ExprId> {
        self.anon_const(|p| p.const_arg_form())
    }

    /// `const_arg_expr` without the anonymous const entry.
    fn const_arg_form(&mut self) -> PResult<ExprId> {
        match self.peek() {
            Tok::Minus => self.prefix(false),
            Tok::LBrace => self.block_like_expr(false),
            Tok::Int(..) | Tok::Str(..) | Tok::Char(..) | Tok::True | Tok::False | Tok::Ident(_) | Tok::SelfUpper => {
                self.primary(false, false)
            }
            // A token that starts no expression is a grammar error, also
            // in cfg-removed code (`<const N: u8 = ;>`).
            Tok::Semi | Tok::Comma | Tok::Gt | Tok::Eq | Tok::RParen | Tok::RBracket | Tok::RBrace | Tok::Eof => {
                Err(syntax(self.span(), format!("expected a const argument, found {}", tok_name(self.peek()))))
            }
            _ => Err(self.reject(C_CONST, "const generic arguments in this form")),
        }
    }

    /// Angle generic arguments, starting at the `<` and eating through
    /// the matching `>`: types, lifetimes (still rejected, L0203),
    /// consts, and associated bindings (`Item = u8`, `Item: Clone`).
    fn generic_args(&mut self) -> PResult<Vec<GenericArg>> {
        self.expect(Tok::Lt, "`<`")?;
        let mut args = Vec::new();
        while self.peek() != Tok::Gt {
            match self.peek() {
                Tok::Lifetime(_) => args.push(GenericArg::Lifetime(self.lifetime_here()?)),
                Tok::Ident(name) if self.peek_at(1) == Tok::Eq => {
                    let span = self.span();
                    self.bump();
                    self.bump();
                    let kind = match self.peek() {
                        Tok::Int(..) | Tok::Str(..) | Tok::Char(..) | Tok::True | Tok::False | Tok::Minus | Tok::LBrace => {
                            BindingKind::EqConst(self.const_arg_expr()?)
                        }
                        _ => BindingKind::EqTy(self.ty()?),
                    };
                    args.push(GenericArg::Binding { name, span, kind });
                }
                Tok::Ident(name) if self.peek_at(1) == Tok::Colon => {
                    let span = self.span();
                    self.bump();
                    self.bump();
                    let bounds = self.bounds()?;
                    args.push(GenericArg::Binding { name, span, kind: BindingKind::Constraint(bounds) });
                }
                Tok::Int(..) | Tok::Str(..) | Tok::Char(..) | Tok::True | Tok::False | Tok::Minus | Tok::LBrace => {
                    args.push(GenericArg::Const(self.const_arg_expr()?));
                }
                _ => args.push(GenericArg::Type(self.ty()?)),
            }
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::Gt, "`>`")?;
        Ok(args)
    }

    /// Parses `a::b::<T>::c`. In type position (`in_type`), generics need no `::`.
    /// Module anchors parse as plain first segments named `crate`,
    /// `self`, or `super` (the resolver reads them, as in use trees); a
    /// leading `::` becomes a first segment named `::`, which the
    /// resolver also reads and removes. Without the resolver these
    /// paths reach collect/check, which reject them as before.
    fn path(&mut self, in_type: bool) -> PResult<Vec<PathSeg>> {
        let mut segs = Vec::new();
        if self.eat(Tok::PathSep) {
            segs.push(PathSeg::plain(self.interner.intern("::")));
        }
        loop {
            let name = match self.peek() {
                Tok::Crate => {
                    self.bump();
                    self.interner.intern("crate")
                }
                Tok::Super => {
                    self.bump();
                    self.interner.intern("super")
                }
                Tok::SelfLower => {
                    self.bump();
                    self.known.self_value
                }
                _ => self.ident()?.0,
            };
            let turbofish = self.peek() == Tok::PathSep && matches!(self.peek_at(1), Tok::Lt | Tok::Shl);
            let args = if (in_type && self.at_lt()) || turbofish {
                if turbofish {
                    self.bump();
                }
                GenericArgs::Angle(self.generic_args()?)
            } else {
                GenericArgs::None
            };
            segs.push(PathSeg { name, args });
            if self.peek() == Tok::PathSep
                && matches!(self.peek_at(1), Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super | Tok::SelfLower)
            {
                self.bump();
            } else {
                break;
            }
        }
        Ok(segs)
    }

    // ---------- Blocks and statements ----------

    fn block(&mut self) -> PResult<BlockId> {
        self.nest(|p| p.block_inner())
    }

    /// True when the statement ahead (past attributes and visibility) opens
    /// with an item keyword. `use` keeps its dedicated path below, and a
    /// `const {` block is an expression, not an item.
    fn at_body_item(&self) -> bool {
        let mut j = self.pos;
        loop {
            if self.toks.get(j).map(|t| t.tok) != Some(Tok::Pound) {
                break;
            }
            j += 1;
            if self.toks.get(j).map(|t| t.tok) == Some(Tok::Bang) {
                j += 1;
            }
            if self.toks.get(j).map(|t| t.tok) != Some(Tok::LBracket) {
                return false;
            }
            let mut depth = 0usize;
            while let Some(t) = self.toks.get(j) {
                match t.tok {
                    Tok::LBracket => depth += 1,
                    Tok::RBracket => {
                        depth -= 1;
                        j += 1;
                        if depth == 0 {
                            break;
                        }
                        continue;
                    }
                    Tok::Eof => return false,
                    _ => {}
                }
                j += 1;
            }
        }
        if self.toks.get(j).map(|t| t.tok) == Some(Tok::Pub) {
            j += 1;
            if self.toks.get(j).map(|t| t.tok) == Some(Tok::LParen) {
                let mut depth = 0usize;
                while let Some(t) = self.toks.get(j) {
                    match t.tok {
                        Tok::LParen => depth += 1,
                        Tok::RParen => {
                            depth -= 1;
                            j += 1;
                            if depth == 0 {
                                break;
                            }
                            continue;
                        }
                        Tok::Eof => return false,
                        _ => {}
                    }
                    j += 1;
                }
            }
        }
        match self.toks.get(j).map(|t| t.tok) {
            Some(Tok::Fn | Tok::Struct | Tok::Enum | Tok::Impl | Tok::Mod | Tok::Trait | Tok::Static | Tok::Type | Tok::Extern) => true,
            Some(Tok::Const) => self.toks.get(j + 1).map(|t| t.tok) != Some(Tok::LBrace),
            // `union` is a contextual keyword: an item only when a name follows.
            Some(Tok::Ident(s)) => self.interner.get(s) == "union" && matches!(self.toks.get(j + 1).map(|t| t.tok), Some(Tok::Ident(_))),
            _ => false,
        }
    }

    /// True at an `unsafe` or `async` item qualifier in a cfg syntax
    /// check: qualifiers (and an `extern "abi"`) followed by an item
    /// keyword. An `unsafe { .. }` or `async { .. }` block is not an
    /// item and stays an expression.
    fn at_cfg_qualified_item(&self) -> bool {
        if !matches!(self.peek(), Tok::Unsafe | Tok::Async) {
            return false;
        }
        let mut j = self.pos;
        let mut saw_extern = false;
        loop {
            match self.toks.get(j).map(|t| t.tok) {
                Some(Tok::Unsafe | Tok::Async | Tok::Const) => j += 1,
                Some(Tok::Extern) => {
                    saw_extern = true;
                    j += 1;
                    if matches!(self.toks.get(j).map(|t| t.tok), Some(Tok::Str(..))) {
                        j += 1;
                    }
                }
                _ => break,
            }
        }
        match self.toks.get(j).map(|t| t.tok) {
            Some(Tok::Fn | Tok::Impl | Tok::Trait | Tok::Mod | Tok::Struct | Tok::Enum | Tok::Crate) => true,
            // Only an extern block opens with `{`; a plain unsafe or
            // async block is an expression.
            Some(Tok::LBrace) => saw_extern,
            _ => false,
        }
    }

    fn block_inner(&mut self) -> PResult<BlockId> {
        let start = self.expect(Tok::LBrace, "`{`")?;
        // Inner attributes at a block's start are permitted only in the
        // contexts that set `block_inner_ok` (a fn body, a loop body, a
        // statement or tail block, a call/array/tuple element block), and
        // only before the first statement. Everywhere else rustc rejects
        // them, so lust does too.
        let inner_attrs = if std::mem::take(&mut self.block_inner_ok) {
            self.inner_attributes()?.attrs
        } else if self.at_inner_attr() {
            return Err(syntax(self.span(), "an inner attribute is not permitted in this context"));
        } else {
            Vec::new()
        };
        let mut stmts = Vec::new();
        let mut tail = None;
        let mut tail_attrs = Vec::new();
        while self.peek() != Tok::RBrace {
            if self.peek() == Tok::Eof {
                return Err(syntax(self.span(), "expected `}`, found end of file"));
            }
            if self.at_inner_attr() {
                return Err(syntax(self.span(), "an inner attribute is not permitted in this context"));
            }
            if self.eat(Tok::Semi) {
                continue;
            }
            // An item inside a function body parses with the item parser
            // (which reads its own attributes); the resolver and checker
            // bind it for the rest of the block.
            if self.at_body_item() {
                match self.item()? {
                    Some(item) => {
                        let idx = self.ast.stmt_items.len() as u32;
                        self.ast.stmt_items.push(item);
                        stmts.push(Stmt::Item(idx));
                    }
                    None => return Err(syntax(self.span(), "expected an item")),
                }
                continue;
            }
            // Statement attributes: parsed here so a `#[cfg]` on a statement
            // gets the attribute code; lint attributes are kept on the
            // statement (`let`, expression, or the block's tail).
            let mut stmt_attrs = self.part_attributes("statements", 0)?;
            // A function-local `use` is an item statement; the resolver
            // binds it for the rest of the block (docs/ARCH.md 1.3).
            if self.peek() == Tok::Use {
                let s = self.span();
                let tree_use = self.use_def()?;
                let idx = self.ast.stmt_items.len() as u32;
                self.ast.stmt_items.push(Item {
                    vis: Vis::Private,
                    attrs: stmt_attrs.attrs,
                    kind: ItemKind::Use(tree_use),
                    span: s.to(self.prev_span()),
                });
                stmts.push(Stmt::Item(idx));
                continue;
            }
            if matches!(
                self.peek(),
                Tok::Fn | Tok::Struct | Tok::Enum | Tok::Impl | Tok::Use | Tok::Mod | Tok::Trait | Tok::Static | Tok::Type | Tok::Extern
            ) || (self.peek() == Tok::Const && self.peek_at(1) != Tok::LBrace)
                || (self.cfg_syntax && self.at_cfg_qualified_item())
            {
                if self.cfg_syntax {
                    match self.item()? {
                        Some(item) => {
                            let idx = self.ast.stmt_items.len() as u32;
                            self.ast.stmt_items.push(item);
                            stmts.push(Stmt::Item(idx));
                        }
                        None => return Err(syntax(self.span(), "expected an item")),
                    }
                    continue;
                }
                return Err(self.reject(C_CORE, "items inside function bodies"));
            }
            if self.peek() == Tok::Let {
                let s = self.bump().span;
                let pat = self.pattern_no_top_alt("`let` bindings require top-level or-patterns in parentheses")?;
                let ty = if self.eat(Tok::Colon) { Some(self.ty()?) } else { None };
                let init = if self.eat(Tok::Eq) { Some(self.expr()?) } else { None };
                let els = if self.peek() == Tok::Else {
                    // Rust grammar: a let-else scrutinee may not end
                    // with a `}` and may not be a top-level lazy boolean.
                    // Both are parse errors in rustc, so they are here.
                    let bad_scrutinee = match init {
                        None => true,
                        // A parenthesized block-like scrutinee is
                        // the wrapped form rustc asks for.
                        Some(i) if self.paren_lo.contains_key(&i.0) => false,
                        Some(i) => matches!(
                            self.ast.expr(i),
                            Expr::StructLit { .. }
                                | Expr::Block(_)
                                | Expr::If { .. }
                                | Expr::While { .. }
                                | Expr::Loop { .. }
                                | Expr::For { .. }
                                | Expr::Match { .. }
                                | Expr::Binary { op: BinOp::And | BinOp::Or, .. }
                        ),
                    };
                    if bad_scrutinee {
                        return Err(syntax(
                            self.span(),
                            "this expression cannot be a `let...else` scrutinee; wrap it in parentheses",
                        ));
                    }
                    self.bump();
                    Some(self.block()?)
                } else {
                    None
                };
                self.expect(Tok::Semi, "`;`")?;
                self.stmt_track_caller(&stmt_attrs.attrs, false)?;
                stmts.push(Stmt::Let { pat, ty, init, els, attrs: stmt_attrs.attrs, span: s.to(self.prev_span()) });
                continue;
            }
            let labeled = matches!(self.peek(), Tok::Lifetime(_)) && self.peek_at(1) == Tok::Colon;
            // An inline `const { .. }` block is block-like too: as a
            // statement it needs no `;` and ends at its `}` (rustc).
            let const_block = self.peek() == Tok::Const && self.peek_at(1) == Tok::LBrace;
            // A cfg syntax check reads `m! {..}` as rustc does: a whole
            // statement, so `m! {} [1]` is two statements, not an index.
            let brace_mac = self.cfg_syntax && self.at_brace_macro_call();
            let mut block_like = labeled
                || const_block
                || brace_mac
                || matches!(self.peek(), Tok::If | Tok::Match | Tok::While | Tok::Loop | Tok::For | Tok::LBrace);
            // A statement (or block tail) block may carry inner attributes.
            self.block_inner_ok = true;
            let expr = if block_like {
                // A labeled block-like statement ends at its block too:
                // `'a: { .. } [x]` is two statements, not an index.
                let e = if labeled {
                    self.primary(false, true)?
                } else if brace_mac {
                    self.primary(false, false)?
                } else if const_block {
                    let start = self.span();
                    self.bump();
                    let b = self.block()?;
                    self.push_expr(Expr::ConstBlock(b), start.to(self.prev_span()))
                } else {
                    self.block_like_expr(true)?
                };
                // Allow method calls on a block-like expression, as rustc does.
                // The statement is then a plain expression: it needs a `;`
                // unless it is the block's tail.
                if self.peek() == Tok::Dot || self.peek() == Tok::Question {
                    block_like = false;
                    let e = self.postfix(e)?;
                    self.binary_rest(e, 0, false)?
                } else {
                    e
                }
            } else {
                self.expr()?
            };
            // An `#[allow(..)]` directly on a macro invocation is unused
            // in rustc (it does not reach the macro's arguments), while
            // the same allow on an enclosing `let`, block, or arm does.
            // Drop it here so the lint still fires inside the invocation.
            let is_macro = matches!(self.ast.expr(expr), Expr::Macro { .. } | Expr::MacroCall(_));
            if is_macro {
                stmt_attrs.attrs.retain(|a| !is_allow(a, self.known));
            }
            self.stmt_track_caller(&stmt_attrs.attrs, is_macro)?;
            // Attributes on an expression statement are stable only for
            // expression kinds with no trailing operator: rustc rejects
            // them on assignments, binary operations, casts, and ranges.
            // Disabled code is stripped before that check, so it is exempt.
            if !self.cfg_syntax && !stmt_attrs.attrs.is_empty() && self.attr_goes_to_operand(expr) {
                return Err(syntax(stmt_attrs.attrs[0].span, "attributes on expressions are not permitted in this context"));
            }
            // A tool attribute (`rustfmt::skip`) on an expression statement
            // with no `;` (a block tail or a block-like statement) is
            // rustc E0658; with a `;` it is fine.
            if !self.cfg_syntax
                && self.peek() != Tok::Semi
                && let Some(a) = stmt_attrs.attrs.iter().find(|a| a.path.len() > 1)
            {
                return Err(syntax(a.span, "attributes on expressions are not permitted in this context"));
            }
            if self.eat(Tok::Semi) {
                stmts.push(Stmt::Expr { expr, semi: true, attrs: stmt_attrs.attrs });
            } else if self.peek() == Tok::RBrace {
                tail = Some(expr);
                tail_attrs = stmt_attrs.attrs;
            } else if block_like
                || (self.cfg_syntax && matches!(self.ast.expr(expr), Expr::MacroCall(m) if m.delim == Delim::Brace))
            {
                stmts.push(Stmt::Expr { expr, semi: false, attrs: stmt_attrs.attrs });
            } else {
                return Err(syntax(self.span(), format!("expected `;` or `}}`, found {}", tok_name(self.peek()))));
            }
        }
        let end = self.expect(Tok::RBrace, "`}`")?;
        Ok(self.push_block(Block { inner_attrs, stmts, tail, tail_attrs, span: start.to(end) }))
    }

    // ---------- Patterns ----------

    fn pattern(&mut self) -> PResult<PatId> {
        self.nest(|p| p.pattern_inner())
    }

    fn pattern_inner(&mut self) -> PResult<PatId> {
        let start = self.span();
        self.eat(Tok::Pipe);
        let first = self.pattern_one()?;
        if self.peek() != Tok::Pipe {
            return Ok(first);
        }
        let mut alts = vec![first];
        while self.eat(Tok::Pipe) {
            alts.push(self.pattern_one()?);
        }
        Ok(self.push_pat(Pat::Or(alts), start.to(self.prev_span())))
    }

    /// A pattern with no top-level `|` alternation, for the
    /// positions Rust reserves it in (`let` bindings and
    /// parameters): a top-level or-pattern there needs
    /// parentheses, which parse through `pattern_one` anyway.
    fn pattern_no_top_alt(&mut self, what: &'static str) -> PResult<PatId> {
        self.nest(|p| {
            let start = p.span();
            let pat = p.pattern_one()?;
            if p.peek() == Tok::Pipe {
                return Err(syntax(start.to(p.span()), what));
            }
            Ok(pat)
        })
    }

    /// True when the token `n` ahead can start a pattern literal.
    fn at_literal_start_at(&self, n: usize) -> bool {
        matches!(
            self.peek_at(n),
            Tok::Int(..)
                | Tok::Float(_)
                | Tok::ByteStr(_)
                | Tok::ByteChar(_)
                | Tok::Minus
                | Tok::Str(..)
                | Tok::Char(..)
                | Tok::True
                | Tok::False
        )
    }

    /// True when the next token can start a pattern literal.
    fn at_literal_start(&self) -> bool {
        self.at_literal_start_at(0)
    }

    /// True when the next token can start a range pattern bound: a
    /// literal, or a path to a const (`u8::MAX`, `m::LO`, `LO`,
    /// `crate::m::HI`, `<K>::A`).
    fn at_bound_start(&self) -> bool {
        self.at_bound_start_at(0)
    }

    /// `at_bound_start` at lookahead `n`.
    fn at_bound_start_at(&self, n: usize) -> bool {
        self.at_literal_start_at(n)
            || matches!(self.peek_at(n), Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super | Tok::SelfLower | Tok::PathSep | Tok::Lt)
    }

    /// Parses one range pattern bound: a literal (possibly negated) or
    /// a path. The checker evaluates it as a const expression.
    fn pattern_bound(&mut self) -> PResult<ExprId> {
        let start = self.span();
        if self.peek() == Tok::Lt {
            let (self_ty, trait_path, segs) = self.qpath_parts()?;
            let span = start.to(self.prev_span());
            Ok(self.push_expr(Expr::QPath { self_ty, trait_path, segs }, span))
        } else if matches!(self.peek(), Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super | Tok::SelfLower | Tok::PathSep) {
            let path = self.path(false)?;
            let span = start.to(self.prev_span());
            Ok(self.push_expr(Expr::Path(path), span))
        } else {
            self.literal_expr()
        }
    }

    fn pattern_one(&mut self) -> PResult<PatId> {
        let start = self.span();
        let pat = match self.peek() {
            Tok::Underscore => {
                self.bump();
                Pat::Wild
            }
            Tok::Ref | Tok::Mut => {
                let by_ref = self.eat(Tok::Ref);
                let mutable = self.eat(Tok::Mut);
                let (name, _) = self.ident()?;
                if self.eat(Tok::At) {
                    let inner = self.nest(|p| p.pattern_one())?;
                    Pat::At { name, mutable, by_ref, inner }
                } else {
                    Pat::Binding { name, mutable, by_ref }
                }
            }
            Tok::Int(..)
            | Tok::Float(_)
            | Tok::ByteStr(_)
            | Tok::ByteChar(_)
            | Tok::Minus
            | Tok::Str(..)
            | Tok::Char(..)
            | Tok::True
            | Tok::False => {
                let lo = self.literal_expr()?;
                if self.eat(Tok::DotDotEq) {
                    let hi = self.pattern_bound()?;
                    Pat::Range { lo: Some(lo), hi: Some(hi), inclusive: true }
                } else if self.eat(Tok::DotDot) {
                    if self.at_bound_start() {
                        let hi = self.pattern_bound()?;
                        Pat::Range { lo: Some(lo), hi: Some(hi), inclusive: false }
                    } else {
                        Pat::Range { lo: Some(lo), hi: None, inclusive: false }
                    }
                } else {
                    Pat::Lit(lo)
                }
            }
            Tok::DotDot => {
                self.bump();
                if self.at_bound_start() {
                    let hi = self.pattern_bound()?;
                    Pat::Range { lo: None, hi: Some(hi), inclusive: false }
                } else {
                    Pat::Rest
                }
            }
            Tok::DotDotEq => {
                self.bump();
                let hi = self.pattern_bound()?;
                Pat::Range { lo: None, hi: Some(hi), inclusive: true }
            }
            Tok::Lt => {
                let (self_ty, trait_path, segs) = self.qpath_parts()?;
                if self.peek() == Tok::DotDotEq || self.peek() == Tok::DotDot {
                    // A qualified path as a range lower bound
                    // (`<K>::A..=100`), as for a plain path below.
                    let lo_span = start.to(self.prev_span());
                    let lo = self.push_expr(Expr::QPath { self_ty, trait_path, segs }, lo_span);
                    if self.eat(Tok::DotDotEq) {
                        let hi = self.pattern_bound()?;
                        Pat::Range { lo: Some(lo), hi: Some(hi), inclusive: true }
                    } else {
                        self.bump();
                        if self.at_bound_start() {
                            let hi = self.pattern_bound()?;
                            Pat::Range { lo: Some(lo), hi: Some(hi), inclusive: false }
                        } else {
                            Pat::Range { lo: Some(lo), hi: None, inclusive: false }
                        }
                    }
                } else {
                    Pat::QPath { self_ty, trait_path, segs }
                }
            }
            Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super | Tok::SelfLower if self.cfg_syntax && self.at_path_macro_call() => {
                self.skip_macro_invocation()?;
                Pat::Wild
            }
            Tok::Ident(_) | Tok::SelfUpper if self.at_path_macro_call() => return Err(macro_error(start)),
            // A path pattern may start with a module anchor
            // (`crate::m::E::A`, `super::S { .. }`, `::m::C`): the same
            // path forms as after an identifier, never a binding.
            Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super | Tok::SelfLower | Tok::PathSep => {
                let anchored = matches!(self.peek(), Tok::Crate | Tok::Super | Tok::SelfLower | Tok::PathSep);
                let path = self.path(false)?;
                if self.peek() == Tok::DotDotEq || self.peek() == Tok::DotDot {
                    // A path as a range lower bound (`LO..=HI`, `u8::MIN..`).
                    let lo_span = start.to(self.prev_span());
                    let lo = self.push_expr(Expr::Path(path), lo_span);
                    if self.eat(Tok::DotDotEq) {
                        let hi = self.pattern_bound()?;
                        Pat::Range { lo: Some(lo), hi: Some(hi), inclusive: true }
                    } else {
                        self.bump();
                        if self.at_bound_start() {
                            let hi = self.pattern_bound()?;
                            Pat::Range { lo: Some(lo), hi: Some(hi), inclusive: false }
                        } else {
                            Pat::Range { lo: Some(lo), hi: None, inclusive: false }
                        }
                    }
                } else if self.peek() == Tok::At {
                    if anchored || path.len() != 1 || path[0].has_args() {
                        return Err(syntax(start, "expected a binding name before `@`"));
                    }
                    self.bump();
                    let inner = self.nest(|p| p.pattern_one())?;
                    Pat::At { name: path[0].name, mutable: false, by_ref: false, inner }
                } else {
                    match self.peek() {
                        Tok::LParen => {
                            self.bump();
                            let mut elems = Vec::new();
                            while self.peek() != Tok::RParen {
                                if self.peek() == Tok::DotDot && !self.at_bound_start_at(1) {
                                    let s = self.span();
                                    self.bump();
                                    elems.push(self.push_pat(Pat::Rest, s));
                                } else {
                                    elems.push(self.pattern()?);
                                }
                                if !self.eat(Tok::Comma) {
                                    break;
                                }
                            }
                            self.expect(Tok::RParen, "`)`")?;
                            Pat::TupleStruct { path, elems }
                        }
                        Tok::LBrace => {
                            self.bump();
                            let mut fields = Vec::new();
                            let mut rest = false;
                            while self.peek() != Tok::RBrace {
                                if self.eat(Tok::DotDot) {
                                    rest = true;
                                    break;
                                }
                                let fstart = self.span();
                                if matches!(self.peek(), Tok::Int(..)) {
                                    // `S { 0: p }` is valid Rust lust does not build;
                                    // `S { 0 }` is a syntax error (no shorthand for a number).
                                    if self.peek_at(1) != Tok::Colon {
                                        return Err(syntax(self.span(), "expected identifier, found integer literal"));
                                    }
                                    return Err(self.reject(C_CORE, "tuple struct patterns with field numbers"));
                                }
                                let _fattrs = self.part_attributes("pattern fields", 0)?;
                                let by_ref = self.eat(Tok::Ref);
                                let mutable = self.eat(Tok::Mut);
                                let (fname, fspan) = self.ident()?;
                                let p = if self.eat(Tok::At) {
                                    let inner = self.nest(|p| p.pattern_one())?;
                                    self.push_pat(Pat::At { name: fname, mutable, by_ref, inner }, fstart.to(self.prev_span()))
                                } else if !by_ref && !mutable && self.eat(Tok::Colon) {
                                    self.pattern()?
                                } else {
                                    self.push_pat(Pat::Binding { name: fname, mutable, by_ref }, fstart.to(fspan))
                                };
                                fields.push((fname, p));
                                if !self.eat(Tok::Comma) {
                                    break;
                                }
                            }
                            self.expect(Tok::RBrace, "`}`")?;
                            Pat::Struct { path, fields, rest }
                        }
                        _ if anchored && path.len() == 1 => {
                            // A lone anchor (`crate`, `super`, `self`) names no pattern.
                            return Err(syntax(start, format!("expected a pattern, found `{}`", self.interner.get(path[0].name))));
                        }
                        _ if path.len() == 1 => {
                            // A lone identifier is a binding. Unit variants need a path such as `Kind::C`.
                            Pat::Binding { name: path[0].name, mutable: false, by_ref: false }
                        }
                        _ => Pat::Path(path),
                    }
                }
            }
            Tok::LParen => {
                self.bump();
                let mut elems = Vec::new();
                let mut tuple = false;
                while self.peek() != Tok::RParen {
                    if self.peek() == Tok::DotDot && !self.at_bound_start_at(1) {
                        let s = self.span();
                        self.bump();
                        elems.push(self.push_pat(Pat::Rest, s));
                    } else {
                        elems.push(self.pattern()?);
                    }
                    if !self.eat(Tok::Comma) {
                        break;
                    }
                    tuple = true;
                }
                self.expect(Tok::RParen, "`)`")?;
                if !tuple && elems.len() == 1 {
                    return Ok(elems[0]);
                }
                Pat::Tuple(elems)
            }
            Tok::LBracket => {
                self.bump();
                let mut prefix: Vec<PatId> = Vec::new();
                let mut middle: Option<PatId> = None;
                let mut suffix: Vec<PatId> = Vec::new();
                let mut seen_rest = false;
                while self.peek() != Tok::RBracket {
                    if self.peek() == Tok::DotDot && !self.at_bound_start_at(1) {
                        let s = self.span();
                        self.bump();
                        if seen_rest {
                            return Err(syntax(s, "multiple `..` in a slice pattern"));
                        }
                        seen_rest = true;
                        middle = Some(self.push_pat(Pat::Rest, s));
                    } else {
                        let parenthesized = self.peek() == Tok::LParen;
                        let e = self.pattern()?;
                        // An unparenthesized `X..` element is experimental
                        // in a slice pattern (rustc E0658): the `..` reads
                        // as the rest. `[(X..)]` and `..X` stay legal.
                        let half_open = |p: PatId| {
                            matches!(self.ast.pat(p), Pat::Range { lo: Some(_), hi: None, .. })
                                || matches!(self.ast.pat(p), Pat::At { inner, .. } if matches!(self.ast.pat(*inner), Pat::Range { lo: Some(_), hi: None, .. }))
                        };
                        if !parenthesized && half_open(e) {
                            return Err(syntax(
                                self.ast.pat_span(e),
                                "`X..` patterns in slices are experimental; write `[(X..)]` with parentheses",
                            ));
                        }
                        // `rest @ ..` binds the middle slice itself.
                        let at_rest = match self.ast.pat(e) {
                            Pat::At { name, mutable, by_ref, inner } if matches!(self.ast.pat(*inner), Pat::Rest) => {
                                Some((*name, *mutable, *by_ref))
                            }
                            _ => None,
                        };
                        if let Some((name, mutable, by_ref)) = at_rest {
                            if seen_rest {
                                return Err(syntax(start, "multiple `..` in a slice pattern"));
                            }
                            seen_rest = true;
                            let espan = self.ast.pat_span(e);
                            middle = Some(self.push_pat(Pat::Binding { name, mutable, by_ref }, espan));
                        } else if seen_rest {
                            suffix.push(e);
                        } else {
                            prefix.push(e);
                        }
                    }
                    if !self.eat(Tok::Comma) {
                        break;
                    }
                }
                self.expect(Tok::RBracket, "`]`")?;
                Pat::Slice { prefix, middle, suffix }
            }
            Tok::Amp | Tok::AndAnd => {
                let double = self.bump().tok == Tok::AndAnd;
                let mutable = self.eat(Tok::Mut);
                let parenthesized = self.peek() == Tok::LParen;
                let inner = self.nest(|p| p.pattern_one())?;
                // `&0..=9` is ambiguous in Rust: a range directly under
                // `&` needs parentheses, `&(0..=9)`.
                if !parenthesized && matches!(self.ast.pat(inner), Pat::Range { .. }) {
                    return Err(syntax(
                        self.ast.pat_span(inner),
                        "the range pattern here has ambiguous interpretation; add parentheses, such as `&(0..=9)`",
                    ));
                }
                let mut pat = Pat::Ref { mutable, inner };
                if double {
                    let s = start.to(self.prev_span());
                    let inner_id = self.push_pat(pat, s);
                    pat = Pat::Ref { mutable: false, inner: inner_id };
                }
                pat
            }
            Tok::Reserved(_) => return Err(self.reserved_error(start)),
            t => return Err(syntax(start, format!("expected a pattern, found {}", tok_name(t)))),
        };
        Ok(self.push_pat(pat, start.to(self.prev_span())))
    }

    /// The `u8` expression for a byte char literal token (`b'x'`).
    fn byte_char_expr(&self, i: u32, start: Span) -> PResult<Expr> {
        let text = self.ast.strings[(i + self.str_base) as usize].clone();
        match decode_byte_char(&text) {
            Some(v) => Ok(Expr::Int(v as u128, Some(crate::lexer::IntSuffix::U8))),
            None => Err(syntax(start, "invalid byte char literal")),
        }
    }

    /// The `&[u8; N]` expression for a byte string literal token
    /// (`b".."`, `br".."`, `br#".."#`): a reference to one blob node
    /// holding the bytes, which is its Rust type. The bytes stay one
    /// buffer, never one element node per byte, so a megabyte
    /// `include_bytes!` costs one node. C string literals share the
    /// token and stay rejected.
    fn byte_str_expr(&mut self, i: u32, start: Span) -> PResult<Expr> {
        let text = self.ast.strings[(i + self.str_base) as usize].clone();
        if text.starts_with('c') {
            if self.cfg_syntax {
                let arr = self.push_expr(Expr::Array(Vec::new()), start);
                return Ok(Expr::Ref { mutable: false, raw: false, expr: arr });
            }
            return Err(not_yet(C_LIT, start, "C string literals"));
        }
        let Some(bytes) = decode_byte_str(&text) else { return Err(syntax(start, "invalid byte string literal")) };
        let id = self.ast.blobs.len() as u32;
        self.ast.blobs.push(crate::ast::ByteBlob::new(bytes));
        let arr = self.push_expr(Expr::ByteStr(id), start);
        Ok(Expr::Ref { mutable: false, raw: false, expr: arr })
    }

    fn literal_expr(&mut self) -> PResult<ExprId> {
        let start = self.span();
        let neg = self.eat(Tok::Minus);
        let e = match self.bump().tok {
            Tok::Int(v, s, _) => Expr::Int(v, s),
            Tok::Float(i) => Expr::Float(i + self.str_base),
            Tok::ByteChar(i) if !neg => self.byte_char_expr(i, start)?,
            Tok::ByteStr(i) if !neg => self.byte_str_expr(i, start)?,
            Tok::Str(i, _) if !neg => Expr::Str(i + self.str_base),
            Tok::Char(c, _) if !neg => Expr::Char(c),
            Tok::True if !neg => Expr::Bool(true),
            Tok::False if !neg => Expr::Bool(false),
            t => return Err(syntax(start, format!("expected a literal, found {}", tok_name(t)))),
        };
        let span = start.to(self.prev_span());
        let id = self.push_expr(e, span);
        Ok(if neg { self.push_expr(Expr::Unary { op: UnOp::Neg, expr: id }, span) } else { id })
    }

    // ---------- Expressions ----------

    pub fn expr(&mut self) -> PResult<ExprId> {
        self.expr_ctx(false)
    }

    /// A closure: `move |params| -> Ret body`. Parameters are
    /// single patterns (no top-level `|` alternation, as in Rust);
    /// attributes on parameters are not parsed yet and fall out
    /// as a syntax error. The body is a full expression.
    /// The arity of a std fn that a path names when lust has no value form
    /// for it, so a value use eta-expands (`eta_closure`): `Vec::new`,
    /// `Arc::new`, `Rc::downgrade`, `Ord::cmp`, `HashMap::default`. Only
    /// the last two segments count. None for every other path. Each fn
    /// here is safe and not `#[track_caller]`, so the closure behaves as
    /// the fn item does (its panics, drops, and output are the same). Only
    /// the `mem` fns have generics of their own, so only they keep a
    /// turbofish on the item (`mem::take::<Vec<u8>>`); the closure's call
    /// writes it.
    fn eta_arity(&self, path: &[PathSeg]) -> Option<usize> {
        let [.., ty, item] = path else { return None };
        if !matches!(item.args, GenericArgs::None) && self.interner.get(ty.name) != "mem" {
            return None;
        }
        let (t, i) = (self.interner.get(ty.name), self.interner.get(item.name));
        Some(match (t, i) {
            ("Self", _) => return None,
            (_, "default") => 0,
            ("Vec" | "String" | "HashMap" | "HashSet" | "BTreeMap" | "BTreeSet" | "VecDeque" | "BinaryHeap" | "Weak", "new") => 0,
            ("Vec" | "String", "with_capacity") => 1,
            ("Arc", "new") => 1,
            ("Rc" | "Arc", "clone" | "as_ptr" | "downgrade" | "strong_count" | "weak_count" | "get_mut" | "unwrap_or_clone") => 1,
            ("Rc" | "Arc", "ptr_eq") => 2,
            // As a closure, borrowck's `upgrade` rule applies inside it: the
            // result shares `T` only, not the `&Weak` borrow
            // (`.and_then(Weak::upgrade)` into an `Arc<dyn Tr>`).
            ("Weak", "upgrade") => 1,
            ("char", "from_u32") => 1,
            ("MaybeUninit", "uninit" | "zeroed") => 0,
            // By-value predicates, so `trim_matches(char::is_whitespace)`
            // takes them as the closure patterns lust has.
            ("char", "is_whitespace" | "is_alphabetic" | "is_alphanumeric" | "is_numeric" | "is_control" | "is_lowercase" | "is_uppercase") => 1,
            ("thread", "sleep" | "spawn") => 1,
            // Builtin methods by path as values (check/ufcs.rs types the
            // call): `map_or(0, Vec::len)`, `start(f, Builder::spawn)`.
            ("Builder", "spawn") => 2,
            ("Vec" | "String" | "VecDeque", "len" | "is_empty" | "capacity") => 1,
            ("Vec", "leak") => 1,
            ("mem", "drop" | "take") => 1,
            ("mem", "swap" | "replace") => 2,
            ("Ord" | "PartialOrd", "cmp" | "partial_cmp" | "lt" | "le" | "gt" | "ge" | "max" | "min") => 2,
            ("PartialEq", "eq" | "ne") => 2,
            // A primitive's comparison and clone trait methods: their
            // marker values have no fn for a builtin's C adapter to call
            // (`sort_by(i32::cmp)`), a closure does.
            (
                "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "char" | "bool",
                "cmp" | "partial_cmp" | "eq" | "ne" | "lt" | "le" | "gt" | "ge",
            ) => 2,
            ("i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "char" | "bool", "max" | "min") => 2,
            ("i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "char" | "bool" | "String", "clone") => 1,
            ("Duration", "from_secs" | "from_millis" | "from_micros" | "from_nanos") => 1,
            _ => return None,
        })
    }

    /// `path` (a plain or qualified path expr) used as a value, for a fn
    /// `eta_arity` lists: the closure `|a0, .., an| path(a0, .., an)`,
    /// every node at the path's span.
    /// rustc gives the fn item type instead; the two differ only in type
    /// identity, so a `TypeId` of such a closure is a reject
    /// (check/any.rs, `ast::is_eta_closure`).
    fn eta_closure(&mut self, path: Expr, n: usize, span: Span) -> ExprId {
        let mut params = Vec::with_capacity(n);
        let mut args = Vec::with_capacity(n);
        for i in 0..n {
            let name = self.interner.intern(&format!("__lust_eta{i}"));
            let pat = self.push_pat(Pat::Binding { name, mutable: false, by_ref: false }, span);
            params.push(ClosureParam { pat, ty: None, attrs: Vec::new(), span });
            args.push(self.push_expr(Expr::Path(vec![PathSeg::plain(name)]), span));
        }
        let callee = self.push_expr(path, span);
        let body = self.push_expr(Expr::Call { callee, args }, span);
        self.push_expr(Expr::Closure { is_move: false, is_async: false, params, ret: None, body }, span)
    }

    fn closure_expr(&mut self, start: Span) -> PResult<ExprId> {
        let is_move = self.eat(Tok::Move);
        let mut params: Vec<ClosureParam> = Vec::new();
        if !self.eat(Tok::OrOr) {
            self.expect(Tok::Pipe, "`|`")?;
            loop {
                if self.eat(Tok::Pipe) {
                    break;
                }
                let pstart = self.span();
                // rustc takes lint and cfg attributes here (the expander
                // strips cfg).
                let attrs = self.part_attributes("function parameters", attrs::T_PARAM)?.attrs;
                let pat = self.pattern_one()?;
                let ty = if self.eat(Tok::Colon) { Some(self.ty()?) } else { None };
                let span = pstart.to(self.prev_span());
                params.push(ClosureParam { pat, ty, attrs, span });
                if self.eat(Tok::Pipe) {
                    break;
                }
                self.expect(Tok::Comma, "`,` or `|`")?;
            }
        }
        let ret = if self.eat(Tok::Arrow) { Some(self.ret_ty()?) } else { None };
        // With a written return type the body must be a block, as in Rust.
        if ret.is_some() && self.peek() != Tok::LBrace {
            return Err(syntax(self.span(), "expected `{` after the closure return type"));
        }
        let body = self.nest(|p| p.expr())?;
        let span = start.to(self.prev_span());
        Ok(self.push_expr(Expr::Closure { is_move, is_async: false, params, ret, body }, span))
    }

    /// `no_struct` is set in `if`, `while`, `match`, and `for` heads, where `{` starts the body.
    fn expr_ctx(&mut self, no_struct: bool) -> PResult<ExprId> {
        let start = self.span();
        if matches!(self.peek(), Tok::Pipe | Tok::OrOr | Tok::Move) {
            // A closure head is not a struct-less head expression
            // either: `if |x| .. { }` stays rejected, as in Rust
            // without parentheses.
            if no_struct {
                return Err(not_yet(C_CORE, start, "closures"));
            }
            // A closure body block may not carry inner attributes, and
            // this dispatch bypasses the prefix take of `block_inner_ok`.
            self.block_inner_ok = false;
            return self.closure_expr(start);
        }
        // Assignment is right-associative and lowest.
        let lhs = self.range_expr(no_struct)?;
        // `>>=` arrives as two tokens (`>` then `>=`), since `>>` is never lexed as one.
        let (op, consume) = if self.at_shr_assign() {
            (Some(BinOp::Shr), 2)
        } else {
            (
                match self.peek() {
                    Tok::Eq => None,
                    Tok::PlusEq => Some(BinOp::Add),
                    Tok::MinusEq => Some(BinOp::Sub),
                    Tok::StarEq => Some(BinOp::Mul),
                    Tok::SlashEq => Some(BinOp::Div),
                    Tok::PercentEq => Some(BinOp::Rem),
                    Tok::AmpEq => Some(BinOp::BitAnd),
                    Tok::PipeEq => Some(BinOp::BitOr),
                    Tok::CaretEq => Some(BinOp::BitXor),
                    Tok::ShlEq => Some(BinOp::Shl),
                    _ => return Ok(lhs),
                },
                1,
            )
        };
        for _ in 0..consume {
            self.bump();
        }
        let rhs = self.nest(|p| p.expr_ctx(no_struct))?;
        let span = start.to(self.prev_span());
        Ok(match op {
            None => self.push_expr(Expr::Assign { lhs, rhs }, span),
            Some(op) => self.push_expr(Expr::AssignOp { op, lhs, rhs }, span),
        })
    }

    fn range_expr(&mut self, no_struct: bool) -> PResult<ExprId> {
        let start = self.span();
        let lo = if matches!(self.peek(), Tok::DotDot | Tok::DotDotEq) { None } else { Some(self.binary(0, no_struct)?) };
        let inclusive = match self.peek() {
            Tok::DotDot => false,
            Tok::DotDotEq => true,
            _ => return Ok(lo.unwrap()),
        };
        self.bump();
        // `_` does not begin a range end (rustc's `can_begin_expr`).
        let ends = matches!(self.peek(), Tok::RParen | Tok::RBracket | Tok::RBrace | Tok::Comma | Tok::Semi | Tok::Eof | Tok::Underscore)
            || (no_struct && self.peek() == Tok::LBrace);
        let hi = if ends { None } else { Some(self.binary(0, no_struct)?) };
        if inclusive && hi.is_none() {
            return Err(syntax(self.prev_span(), "inclusive range with no end; write `a..=b`, or `a..` for an open range"));
        }
        Ok(self.push_expr(Expr::Range { lo, hi, inclusive }, start.to(self.prev_span())))
    }

    fn binop(&self) -> Option<(BinOp, u8, usize)> {
        // (operator, precedence, token count). Higher binds tighter.
        Some(match self.peek() {
            Tok::OrOr => (BinOp::Or, 1, 1),
            Tok::AndAnd => (BinOp::And, 2, 1),
            Tok::EqEq => (BinOp::Eq, 3, 1),
            Tok::Ne => (BinOp::Ne, 3, 1),
            Tok::Lt => (BinOp::Lt, 3, 1),
            Tok::Le => (BinOp::Le, 3, 1),
            // `>>=` is a compound assignment, not a shift: leave it for `expr_ctx`.
            Tok::Gt if self.at_shr_assign() => return None,
            Tok::Gt if self.at_shr() => (BinOp::Shr, 7, 2),
            Tok::Gt => (BinOp::Gt, 3, 1),
            Tok::Ge => (BinOp::Ge, 3, 1),
            Tok::Pipe => (BinOp::BitOr, 4, 1),
            Tok::Caret => (BinOp::BitXor, 5, 1),
            Tok::Amp => (BinOp::BitAnd, 6, 1),
            Tok::Shl => (BinOp::Shl, 7, 1),
            Tok::Plus => (BinOp::Add, 8, 1),
            Tok::Minus => (BinOp::Sub, 8, 1),
            Tok::Star => (BinOp::Mul, 9, 1),
            Tok::Slash => (BinOp::Div, 9, 1),
            Tok::Percent => (BinOp::Rem, 9, 1),
            _ => return None,
        })
    }

    fn binary(&mut self, min_prec: u8, no_struct: bool) -> PResult<ExprId> {
        let lhs = self.unary(no_struct)?;
        self.binary_rest(lhs, min_prec, no_struct)
    }

    fn binary_rest(&mut self, mut lhs: ExprId, min_prec: u8, no_struct: bool) -> PResult<ExprId> {
        // A long flat chain (`a + a + ...`) makes a deep tree without any recursion
        // here, so count the operators to keep later passes off the stack limit.
        let mut chain = 0u32;
        while let Some((op, prec, n)) = self.binop() {
            chain += 1;
            if chain > MAX_DEPTH {
                return Err(Diag::new(
                    "L9001",
                    self.span(),
                    format!("operator chains longer than {MAX_DEPTH} are not supported"),
                    "Split the expression into smaller pieces with `let`.",
                ));
            }
            if prec <= min_prec {
                break;
            }
            for _ in 0..n {
                self.bump();
            }
            let rhs = self.binary(prec, no_struct)?;
            let span = self.outer_span(lhs).to(self.prev_span());
            if op.is_cmp()
                && let Some((op2, prec2, _)) = self.binop()
                && prec2 == prec
                && op2.is_cmp()
            {
                return Err(syntax(self.span(), "comparison operators cannot be chained; add parentheses"));
            }
            lhs = self.push_expr(Expr::Binary { op, lhs, rhs }, span);
        }
        // `as` binds tighter than every binary operator; handled in `unary` postfix.
        Ok(lhs)
    }

    /// A prefix expression followed by any `as` casts. Prefix operators bind tighter than `as`.
    fn unary(&mut self, no_struct: bool) -> PResult<ExprId> {
        let e = self.prefix(no_struct)?;
        self.cast_rest(e)
    }

    fn prefix(&mut self, no_struct: bool) -> PResult<ExprId> {
        // Spend the caller's block-inner permission here: only a block
        // that starts this prefix expression may use it.
        let inner_ok = std::mem::take(&mut self.block_inner_ok);
        self.nest(|p| p.prefix_inner(no_struct, inner_ok))
    }

    fn prefix_inner(&mut self, no_struct: bool, inner_ok: bool) -> PResult<ExprId> {
        // Outer attributes on any expression are grammar in rustc (the
        // feature gate runs after cfg stripping), so a cfg syntax check
        // reads them and goes on to the expression.
        if self.cfg_syntax && self.peek() == Tok::Pound && self.peek_at(1) == Tok::LBracket {
            self.part_attributes("expressions", 0)?;
        }
        let start = self.span();
        let e = match self.peek() {
            Tok::Minus => {
                self.bump();
                let inner = self.prefix(no_struct)?;
                Expr::Unary { op: UnOp::Neg, expr: inner }
            }
            Tok::Bang => {
                self.bump();
                let inner = self.prefix(no_struct)?;
                Expr::Unary { op: UnOp::Not, expr: inner }
            }
            Tok::Star => {
                self.bump();
                Expr::Deref(self.prefix(no_struct)?)
            }
            Tok::Amp | Tok::AndAnd => {
                let double = self.bump().tok == Tok::AndAnd;
                if !double && self.at_ident("raw") && matches!(self.peek_at(1), Tok::Const | Tok::Mut) {
                    if self.cfg_syntax {
                        self.bump(); // `raw`
                        let mutable = if self.eat(Tok::Mut) {
                            true
                        } else {
                            self.eat(Tok::Const);
                            false
                        };
                        let inner = self.prefix(no_struct)?;
                        let span = start.to(self.prev_span());
                        return Ok(self.push_expr(Expr::Ref { mutable, raw: true, expr: inner }, span));
                    }
                    return Err(not_yet(C_CORE, start, "raw references (`&raw`)"));
                }
                let mutable = self.eat(Tok::Mut);
                let inner = self.prefix(no_struct)?;
                let span = start.to(self.prev_span());
                let mut id = self.push_expr(Expr::Ref { mutable, raw: false, expr: inner }, span);
                if double {
                    id = self.push_expr(Expr::Ref { mutable: false, raw: false, expr: id }, span);
                }
                return Ok(id);
            }
            _ => {
                let e = self.primary(no_struct, inner_ok)?;
                return self.postfix(e);
            }
        };
        Ok(self.push_expr(e, start.to(self.prev_span())))
    }

    /// Records the parenthesized expressions this parse saw in the
    /// AST (`Ast::paren_exprs`), sorted. A parse that appends to an
    /// existing AST (`parse_body`) merges with what is there.
    fn finish_parens(&mut self) {
        if !self.paren_lo.is_empty() {
            let mut ids: Vec<u32> = self.paren_lo.keys().copied().collect();
            self.ast.paren_exprs.append(&mut ids);
            self.ast.paren_exprs.sort_unstable();
            self.ast.paren_exprs.dedup();
        }
        if !self.paren_tys.is_empty() {
            self.ast.paren_tys.append(&mut self.paren_tys);
            self.ast.paren_tys.sort_unstable();
            self.ast.paren_tys.dedup();
        }
    }

    /// `e`'s span, widened to its `(` when it was written in parentheses.
    fn outer_span(&self, e: ExprId) -> Span {
        let s = self.ast.expr_span(e);
        // `Span::to`: a `(` a macro wrote around its argument covers the call.
        match self.paren_lo.get(&e.0) {
            Some(&p) if p.lo < s.lo || p.ctxt != s.ctxt => p.to(s),
            _ => s,
        }
    }

    fn cast_rest(&mut self, mut e: ExprId) -> PResult<ExprId> {
        while self.peek() == Tok::As {
            self.bump();
            let ty = self.ty()?;
            // In rustc a `<<` right after a cast type starts generic
            // arguments, it is not a shift: `a as u8 << 2` is an error. A
            // type that already ends in `>` is complete, so a shift after
            // it stays a shift.
            if self.peek() == Tok::Shl && self.toks[self.pos.saturating_sub(1)].tok != Tok::Gt {
                return Err(syntax(
                    self.span(),
                    "`<<` after a cast type is read as generic arguments, not as a shift: parenthesize the cast",
                ));
            }
            let span = self.outer_span(e).to(self.prev_span());
            e = self.push_expr(Expr::Cast { expr: e, ty }, span);
        }
        Ok(e)
    }

    fn postfix(&mut self, mut e: ExprId) -> PResult<ExprId> {
        // Like `binary_rest`, a long postfix chain makes a deep tree iteratively.
        let mut chain = 0u32;
        loop {
            // Only a real postfix link counts: the lookahead that ends
            // the chain must not make a chain of exactly MAX_DEPTH
            // links read as one too many.
            match self.peek() {
                Tok::LParen | Tok::Dot | Tok::LBracket | Tok::Question => {}
                _ => return Ok(e),
            }
            chain += 1;
            if chain > MAX_DEPTH {
                return Err(Diag::new(
                    "L9001",
                    self.span(),
                    format!("method and field chains longer than {MAX_DEPTH} are not supported"),
                    "Split the expression into smaller pieces with `let`.",
                ));
            }
            let start = self.outer_span(e);
            match self.peek() {
                Tok::LParen => {
                    let args = self.call_args()?;
                    e = self.push_expr(Expr::Call { callee: e, args }, start.to(self.prev_span()));
                }
                Tok::Dot => {
                    self.bump();
                    if let Tok::Float(i) = self.peek() {
                        // `t.0.1` lexes the `0.1` as one float token; in field
                        // position it is two tuple indexes, as in rustc.
                        let text = self.ast.strings[(i + self.str_base) as usize].clone();
                        let parts: Vec<&str> = text.split('.').collect();
                        if parts.len() == 2 && parts.iter().all(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())) {
                            self.bump();
                            // A tuple index has no leading zero: `t.01.2`
                            // names no field (rustc E0609).
                            if parts.iter().any(|s| s.len() > 1 && s.starts_with('0')) {
                                return Err(syntax(self.span(), "tuple index has a leading zero"));
                            }
                            for part in parts {
                                let index: u32 = part.parse().map_err(|_| syntax(self.span(), "invalid tuple field index"))?;
                                e = self.push_expr(Expr::TupleField { base: e, index }, start.to(self.prev_span()));
                            }
                            continue;
                        }
                        return Err(syntax(self.span(), "expected identifier, found float literal"));
                    }
                    if let Some(index) = self.tuple_index()? {
                        e = self.push_expr(Expr::TupleField { base: e, index }, start.to(self.prev_span()));
                        continue;
                    }
                    if self.peek() == Tok::Await {
                        if self.cfg_syntax {
                            self.bump();
                            continue;
                        }
                        return Err(async_error(self.span()));
                    }
                    let (name, name_span) = self.ident()?;
                    let mut generic_args = Vec::new();
                    if self.peek() == Tok::PathSep && matches!(self.peek_at(1), Tok::Lt | Tok::Shl) {
                        self.bump();
                        generic_args = self.generic_args()?;
                    }
                    if self.peek() == Tok::LParen {
                        let args = self.call_args()?;
                        e = self.push_expr(Expr::MethodCall { recv: e, name, name_span, generic_args, args }, start.to(self.prev_span()));
                    } else {
                        e = self.push_expr(Expr::Field { base: e, name }, start.to(self.prev_span()));
                    }
                }
                Tok::LBracket => {
                    self.bump();
                    let index = self.expr()?;
                    self.expect(Tok::RBracket, "`]`")?;
                    e = self.push_expr(Expr::Index { base: e, index }, start.to(self.prev_span()));
                }
                Tok::Question => {
                    self.bump();
                    e = self.push_expr(Expr::Try(e), start.to(self.prev_span()));
                }
                _ => return Ok(e),
            }
        }
    }

    /// rustc rejects `#[track_caller]` on a `let` or expression statement
    /// and only warns on a macro call statement.
    fn stmt_track_caller(&self, attrs: &[Attr], is_macro: bool) -> PResult<()> {
        match attrs.iter().find(|a| a.path.len() == 1 && self.interner.get(a.path[0].name) == "track_caller") {
            Some(a) if !is_macro && !self.cfg_syntax => Err(Diag::new(
                "L0524",
                a.span,
                "the `track_caller` attribute cannot be used on statements",
                "Remove the `#[track_caller]` attribute.",
            )),
            _ => Ok(()),
        }
    }

    /// Outer attributes on a list element or a struct literal field
    /// (`field`), where rustc takes them: lint levels (deny and forbid are
    /// L0531 in `attrs::check_input`), doc comments, `must_use`, and
    /// `cold`; tool attributes (`rustfmt::skip`) on a field only. Other
    /// attributes are rejected. cfg runs never get here: the expander
    /// strips them and checks their position.
    fn elem_attributes(&mut self, field: bool) -> PResult<Vec<Attr>> {
        if self.peek() != Tok::Pound || self.at_inner_attr() {
            return Ok(Vec::new());
        }
        let parsed = self.part_attributes("expressions", 0)?;
        if !self.cfg_syntax
            && let Some(a) = parsed.attrs.iter().find(|a| {
                if a.path.len() != 1 {
                    return !field;
                }
                !matches!(self.interner.get(a.path[0].name), "allow" | "warn" | "expect" | "deny" | "forbid" | "doc" | "must_use" | "cold")
            })
        {
            return Err(syntax(a.span, "attributes on expressions are not permitted in this context"));
        }
        Ok(parsed.attrs)
    }

    /// True when outer attributes on `e` would go to its left operand in
    /// rustc (E0658): a binary operation, cast, range, or assignment that
    /// is not in parentheses.
    fn attr_goes_to_operand(&self, e: ExprId) -> bool {
        !self.paren_lo.contains_key(&e.0)
            && matches!(
                self.ast.expr(e),
                Expr::Binary { .. } | Expr::Cast { .. } | Expr::Assign { .. } | Expr::AssignOp { .. } | Expr::Range { .. }
            )
    }

    /// One call argument, array element, or tuple element after the
    /// first, with its outer attributes (`elem_attributes`), read and
    /// dropped. A block element may carry inner attributes.
    fn list_elem(&mut self) -> PResult<ExprId> {
        let attrs = self.elem_attributes(false)?;
        self.block_inner_ok = true;
        let e = self.expr()?;
        self.check_elem_attrs(&attrs, e)?;
        Ok(e)
    }

    /// The E0658 check for attributes `attrs` on list element `e`.
    fn check_elem_attrs(&self, attrs: &[Attr], e: ExprId) -> PResult<()> {
        match attrs.first() {
            Some(a) if !self.cfg_syntax && self.attr_goes_to_operand(e) => {
                Err(syntax(a.span, "attributes on expressions are not permitted in this context"))
            }
            _ => Ok(()),
        }
    }

    fn call_args(&mut self) -> PResult<Vec<ExprId>> {
        self.expect(Tok::LParen, "`(`")?;
        let mut args = Vec::new();
        while self.peek() != Tok::RParen {
            // A call argument block may carry inner attributes.
            args.push(self.list_elem()?);
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RParen, "`)`")?;
        Ok(args)
    }

    /// A block-like expression. `inner_ok` says whether a plain or
    /// labeled block here may carry inner attributes (see `block_inner`).
    /// Loop bodies always may; `if`/`else` bodies and match arm bodies
    /// never may, whatever the caller passes.
    fn block_like_expr(&mut self, inner_ok: bool) -> PResult<ExprId> {
        self.block_like_labeled(None, inner_ok)
    }

    fn block_like_labeled(&mut self, label: Option<Label>, inner_ok: bool) -> PResult<ExprId> {
        // The caller's flag is spent: only the arms below re-arm it.
        self.block_inner_ok = false;
        let start = self.span();
        let e = match self.peek() {
            Tok::LBrace => match label {
                Some(label) => {
                    self.block_inner_ok = inner_ok;
                    Expr::LabeledBlock { label, body: self.block()? }
                }
                None => {
                    self.block_inner_ok = inner_ok;
                    Expr::Block(self.block()?)
                }
            },
            Tok::If => return self.if_expr(),
            Tok::While => {
                self.bump();
                let cond = self.condition()?;
                self.block_inner_ok = true;
                let body = self.block()?;
                Expr::While { label, cond, body }
            }
            Tok::Loop => {
                self.bump();
                self.block_inner_ok = true;
                Expr::Loop { label, body: self.block()? }
            }
            Tok::For => {
                self.bump();
                let pat = self.pattern()?;
                self.expect(Tok::In, "`in`")?;
                let iter = self.expr_ctx(true)?;
                self.block_inner_ok = true;
                let body = self.block()?;
                Expr::For { label, pat, iter, body }
            }
            Tok::Match => {
                self.bump();
                let scrut = self.expr_ctx(true)?;
                self.expect(Tok::LBrace, "`{`")?;
                // Inner attributes are permitted only here, before the
                // first arm. An inner `#[allow(..)]` scopes over every
                // arm, so it is cloned onto each arm's attributes.
                let inner = self.inner_attributes()?;
                let inner_allows: Vec<Attr> = inner.attrs.iter().filter(|a| is_allow(a, self.known)).cloned().collect();
                let mut arms = Vec::new();
                while self.peek() != Tok::RBrace {
                    let mut aattrs = self.part_attributes("match arms", 0)?;
                    aattrs.attrs.splice(0..0, inner_allows.iter().cloned());
                    let pat = self.pattern()?;
                    let guard = if self.eat(Tok::If) { Some(self.expr()?) } else { None };
                    self.expect(Tok::FatArrow, "`=>`")?;
                    // A block-like body (block, labeled block, `if`,
                    // `match`, a loop, `const { .. }`) ends the arm at its
                    // `}` and needs no `,`, as in rustc; a `.` or `?`
                    // after it continues one expression that does.
                    let labeled = matches!(self.peek(), Tok::Lifetime(_)) && self.peek_at(1) == Tok::Colon;
                    let const_block = self.peek() == Tok::Const && self.peek_at(1) == Tok::LBrace;
                    let mut block_body =
                        labeled || const_block || matches!(self.peek(), Tok::LBrace | Tok::If | Tok::Match | Tok::While | Tok::Loop | Tok::For);
                    let body = if !block_body {
                        self.expr()?
                    } else {
                        let e = if const_block {
                            let start = self.span();
                            self.bump();
                            let b = self.block()?;
                            self.push_expr(Expr::ConstBlock(b), start.to(self.prev_span()))
                        } else {
                            self.primary(false, false)?
                        };
                        if matches!(self.peek(), Tok::Dot | Tok::Question) {
                            block_body = false;
                            let e = self.postfix(e)?;
                            self.binary_rest(e, 0, false)?
                        } else {
                            e
                        }
                    };
                    arms.push(Arm { attrs: aattrs.attrs, pat, guard, body });
                    if !self.eat(Tok::Comma) && !block_body && self.peek() != Tok::RBrace {
                        return Err(syntax(self.span(), "expected `,` after match arm"));
                    }
                }
                self.expect(Tok::RBrace, "`}`")?;
                Expr::Match { scrut, arms }
            }
            _ if label.is_some() => return Err(syntax(start, "expected a loop or a block after the label")),
            _ => unreachable!(),
        };
        Ok(self.push_expr(e, start.to(self.prev_span())))
    }

    /// An `if` or `while` condition, where let chains may appear.
    fn condition(&mut self) -> PResult<ExprId> {
        let old = self.let_ok;
        self.let_ok = true;
        let r = self.expr_ctx(true);
        self.let_ok = old;
        r
    }

    fn if_expr(&mut self) -> PResult<ExprId> {
        let start = self.expect(Tok::If, "`if`")?;
        let cond = self.condition()?;
        let then = self.block()?;
        let els = if self.eat(Tok::Else) {
            if self.peek() == Tok::If {
                Some(self.nest(|p| p.if_expr())?)
            } else {
                let s = self.span();
                let b = self.block()?;
                Some(self.push_expr(Expr::Block(b), s.to(self.prev_span())))
            }
        } else {
            None
        };
        Ok(self.push_expr(Expr::If { cond, then, els }, start.to(self.prev_span())))
    }

    fn primary(&mut self, no_struct: bool, inner_ok: bool) -> PResult<ExprId> {
        let start = self.span();
        let e = match self.peek() {
            Tok::Int(v, s, _) => {
                self.bump();
                Expr::Int(v, s)
            }
            Tok::Float(i) => {
                self.bump();
                Expr::Float(i + self.str_base)
            }
            Tok::ByteChar(i) => {
                self.bump();
                self.byte_char_expr(i, start)?
            }
            Tok::ByteStr(i) => {
                self.bump();
                self.byte_str_expr(i, start)?
            }
            Tok::Str(i, _) => {
                self.bump();
                Expr::Str(i + self.str_base)
            }
            Tok::Char(c, _) => {
                self.bump();
                Expr::Char(c)
            }
            Tok::True => {
                self.bump();
                Expr::Bool(true)
            }
            Tok::False => {
                self.bump();
                Expr::Bool(false)
            }
            // `crate::m!(..)` in a cfg-disabled item: an opaque call, as
            // for a path that starts at an identifier.
            Tok::Crate | Tok::Super | Tok::SelfLower if self.cfg_syntax && self.at_path_macro_call() => {
                return self.cfg_macro_expr();
            }
            Tok::Crate | Tok::Super | Tok::PathSep => {
                let path = self.path(false)?;
                if self.peek() == Tok::LBrace && !no_struct {
                    return self.struct_lit(path, start);
                }
                Expr::Path(path)
            }
            Tok::SelfLower if self.peek_at(1) == Tok::PathSep => {
                let path = self.path(false)?;
                if self.peek() == Tok::LBrace && !no_struct {
                    return self.struct_lit(path, start);
                }
                Expr::Path(path)
            }
            Tok::SelfLower => {
                self.bump();
                Expr::SelfValue
            }
            Tok::LParen => {
                self.bump();
                // The first token inside: its context tells a macro-written body
                // from source (see the paren span below).
                let first_inner = self.span();
                if self.eat(Tok::RParen) {
                    Expr::Unit
                } else {
                    // A `let` in parentheses is never a let chain, even in a
                    // condition: rustc rejects `(let ...)` as a syntax error.
                    if self.peek() == Tok::Let {
                        return Err(syntax(start, "expected an expression, found `let`: parenthesized let chains are not allowed"));
                    }
                    let old_let = self.let_ok;
                    self.let_ok = false;
                    // Attributes on the first element: a tuple takes them,
                    // a parenthesized expression does not (rustc E0658).
                    let first_attrs = match self.elem_attributes(false) {
                        Ok(a) => a,
                        Err(d) => {
                            self.let_ok = old_let;
                            return Err(d);
                        }
                    };
                    let first = self.expr();
                    let mut elems = match first {
                        Ok(e) => vec![e],
                        Err(d) => {
                            self.let_ok = old_let;
                            return Err(d);
                        }
                    };
                    let mut tuple = false;
                    while self.eat(Tok::Comma) {
                        tuple = true;
                        if self.peek() == Tok::RParen {
                            break;
                        }
                        // A tuple element block may carry inner attrs. The
                        // first element is not armed: until a comma is seen
                        // it may still be a parenthesized expression, where
                        // rustc rejects inner attrs.
                        match self.list_elem() {
                            Ok(e) => elems.push(e),
                            Err(d) => {
                                self.let_ok = old_let;
                                return Err(d);
                            }
                        }
                    }
                    let end = self.expect(Tok::RParen, "`)`");
                    self.let_ok = old_let;
                    end?;
                    if let Some(a) = first_attrs.first()
                        && !tuple
                        && !self.cfg_syntax
                    {
                        return Err(syntax(a.span, "attributes on expressions are not permitted in this context"));
                    }
                    self.check_elem_attrs(&first_attrs, elems[0])?;
                    if tuple {
                        Expr::Tuple(elems)
                    } else {
                        self.paren_lo.insert(elems[0].0, start);
                        // rustc's HIR lowering gives a parenthesized expression the
                        // parens' span when it contains the inner one: a panic in
                        // `(t + t)` reports at the `(`.
                        let inner = self.ast.expr_span(elems[0]);
                        let close = self.prev_span();
                        let last_inner = self.toks[self.pos.saturating_sub(2)].span;
                        let one_ctxt = [inner.ctxt, close.ctxt, first_inner.ctxt, last_inner.ctxt].iter().all(|&c| c == start.ctxt);
                        if one_ctxt && start.file == inner.file {
                            self.ast.expr_spans[elems[0].0 as usize] = Span { lo: start.lo, hi: close.hi, ..inner };
                        }
                        return Ok(elems[0]);
                    }
                }
            }
            Tok::LBracket => {
                self.bump();
                if self.eat(Tok::RBracket) {
                    Expr::Array(Vec::new())
                } else {
                    // An array element (or repeat value) block may carry
                    // inner attributes; the repeat length may not. An
                    // element takes outer attributes, a repeat value does
                    // not (rustc E0658).
                    let first_attrs = self.elem_attributes(false)?;
                    self.block_inner_ok = true;
                    let first = self.expr()?;
                    if self.eat(Tok::Semi) {
                        if let Some(a) = first_attrs.first()
                            && !self.cfg_syntax
                        {
                            return Err(syntax(a.span, "attributes on expressions are not permitted in this context"));
                        }
                        let len = self.expr()?;
                        self.expect(Tok::RBracket, "`]`")?;
                        Expr::ArrayRepeat { value: first, len }
                    } else {
                        self.check_elem_attrs(&first_attrs, first)?;
                        let mut elems = vec![first];
                        while self.eat(Tok::Comma) {
                            if self.peek() == Tok::RBracket {
                                break;
                            }
                            elems.push(self.list_elem()?);
                        }
                        self.expect(Tok::RBracket, "`]`")?;
                        Expr::Array(elems)
                    }
                }
            }
            Tok::If | Tok::Match | Tok::While | Tok::Loop | Tok::For | Tok::LBrace => return self.block_like_expr(inner_ok),
            Tok::Break => {
                self.bump();
                let label = self.break_label();
                let val = if label.is_some() || self.can_start_expr() {
                    if self.can_start_expr() { Some(self.expr()?) } else { None }
                } else {
                    None
                };
                Expr::Break { label, value: val }
            }
            Tok::Continue => {
                self.bump();
                let label = self.break_label();
                Expr::Continue(label)
            }
            Tok::Return => {
                self.bump();
                let val = if self.can_start_expr() { Some(self.expr()?) } else { None };
                Expr::Return(val)
            }
            Tok::Lifetime(name) => {
                let span = self.span();
                self.bump();
                self.check_lifetime_name(name, span, true);
                self.expect(Tok::Colon, "`:` after a label")?;
                let label = Label { name, span };
                return self.block_like_labeled(Some(label), inner_ok);
            }
            // A closure as an operand (`&|n| n * 2`, `&mut || ..`): its
            // body is a full expression, as in rustc, so nothing follows
            // it at this level.
            Tok::Pipe | Tok::OrOr | Tok::Move => {
                if no_struct {
                    return Err(not_yet(C_CORE, start, "closures"));
                }
                self.block_inner_ok = false;
                return self.closure_expr(start);
            }
            Tok::Unsafe if self.cfg_syntax => {
                self.bump();
                Expr::Block(self.block()?)
            }
            Tok::Unsafe => return Err(unsafe_error(start)),
            Tok::Async if self.cfg_syntax => {
                self.bump();
                if self.peek() == Tok::LBrace {
                    Expr::Block(self.block()?)
                } else if self.peek() == Tok::Move && self.peek_at(1) == Tok::LBrace {
                    self.bump();
                    Expr::Block(self.block()?)
                } else {
                    return self.closure_expr(start);
                }
            }
            Tok::Async => return Err(async_error(start)),
            Tok::Const => {
                self.bump();
                if self.peek() == Tok::LBrace {
                    Expr::ConstBlock(self.block()?)
                } else {
                    // No expression starts `const` without a block: a
                    // grammar error, also in cfg-removed code (rustc).
                    return Err(syntax(self.span(), format!("expected `{{` after `const`, found {}", tok_name(self.peek()))));
                }
            }
            Tok::Let if self.let_ok => {
                self.bump();
                let pat = self.pattern()?;
                self.expect(Tok::Eq, "`=`")?;
                // The scrutinee stops before a chain `&&` (and before `||`):
                // only operators that bind tighter than `&&` are consumed.
                let scrut = self.binary(3, true)?;
                Expr::Let { pat, scrut }
            }
            Tok::Let if self.cfg_syntax => return Err(syntax(start, "expected an expression, found `let`")),
            Tok::Let => return Err(not_yet(C_CORE, start, "let chains outside conditions")),
            Tok::Lt => {
                let (self_ty, trait_path, segs) = self.qpath_parts()?;
                // `<Vec<u16>>::new` as a value eta-expands as `Vec::<u16>::new`
                // does (`eta_arity`); the closure calls the qualified path.
                if trait_path.is_empty()
                    && self.peek() != Tok::LParen
                    && let [item] = segs.as_slice()
                    && let TyExpr::Path(ty_segs) = self.ast.ty(self_ty)
                    && let Some(ty_seg) = ty_segs.last()
                    && let Some(n) = self.eta_arity(&[ty_seg.clone(), item.clone()])
                {
                    let span = start.to(self.prev_span());
                    return Ok(self.eta_closure(Expr::QPath { self_ty, trait_path, segs }, n, span));
                }
                Expr::QPath { self_ty, trait_path, segs }
            }
            Tok::Underscore => {
                self.bump();
                Expr::Underscore
            }
            Tok::Ident(_) | Tok::SelfUpper => {
                if self.peek_at(1) == Tok::Bang {
                    return self.macro_call();
                }
                if self.cfg_syntax && self.at_path_macro_call() {
                    return self.cfg_macro_expr();
                }
                if self.at_offset_of_path() {
                    for _ in 0..6 {
                        self.bump();
                    }
                    return self.offset_of_body(start);
                }
                if self.at_path_macro_call() {
                    if self.cfg_syntax {
                        return self.cfg_macro_expr();
                    }
                    return Err(macro_error(start));
                }
                let path = self.path(false)?;
                if self.peek() == Tok::LBrace && !no_struct {
                    return self.struct_lit(path, start);
                }
                if self.peek() != Tok::LParen
                    && let Some(n) = self.eta_arity(&path)
                {
                    let span = start.to(self.prev_span());
                    return Ok(self.eta_closure(Expr::Path(path), n, span));
                }
                Expr::Path(path)
            }
            Tok::Reserved(s) if self.cfg_syntax && self.interner.get(s) == "try" && self.peek_at(1) == Tok::LBrace => {
                self.bump();
                Expr::Block(self.block()?)
            }
            Tok::Reserved(_) => return Err(self.reserved_error(start)),
            t => return Err(syntax(start, format!("expected an expression, found {}", tok_name(t)))),
        };
        Ok(self.push_expr(e, start.to(self.prev_span())))
    }

    /// An optional label after `break` or `continue` (no colon follows it there).
    fn break_label(&mut self) -> Option<Label> {
        match self.peek() {
            Tok::Lifetime(name) => {
                let span = self.span();
                self.bump();
                self.check_lifetime_name(name, span, true);
                Some(Label { name, span })
            }
            _ => None,
        }
    }

    fn can_start_expr(&self) -> bool {
        !matches!(self.peek(), Tok::Semi | Tok::RBrace | Tok::RParen | Tok::Comma | Tok::RBracket | Tok::Eof)
    }

    fn struct_lit(&mut self, path: Vec<PathSeg>, start: Span) -> PResult<ExprId> {
        self.expect(Tok::LBrace, "`{`")?;
        let mut fields = Vec::new();
        let mut update = None;
        while self.peek() != Tok::RBrace {
            if self.peek() == Tok::DotDot {
                let dd = self.bump().span;
                if self.peek() == Tok::RBrace {
                    // A bare `..` rest: only an assignment target may
                    // use it (`S { x: place, .. } = value`). It reads
                    // as an open range in the update slot, and the
                    // checker rejects it in a struct literal value.
                    update = Some(self.push_expr(Expr::Range { lo: None, hi: None, inclusive: false }, dd));
                } else {
                    update = Some(self.expr()?);
                }
                break;
            }
            // A field takes lint attributes and doc comments, read and dropped.
            self.elem_attributes(true)?;
            // A tuple struct literal names fields by index: `T { 0: 5, ..a }`.
            // Tuple field names are the index text (collect).
            let index = matches!(self.peek(), Tok::Int(..));
            let (name, span) = if index {
                let span = self.span();
                let index = self.tuple_index()?.unwrap_or_default();
                (self.interner.intern(&index.to_string()), span)
            } else {
                self.ident()?
            };
            let value = if self.eat(Tok::Colon) {
                self.expr()?
            } else if index {
                // An index needs its value: `T { 0 }` is not shorthand.
                return Err(syntax(span, "expected `:` after a tuple field index"));
            } else {
                let seg = PathSeg::plain(name);
                self.push_expr(Expr::Path(vec![seg]), span)
            };
            fields.push((name, span, value));
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(self.push_expr(Expr::StructLit { path, fields, update }, start.to(self.prev_span())))
    }

    /// One step of an `offset_of!` field path: a field name, or an
    /// unsuffixed integer for a tuple field.
    fn offset_field(&mut self) -> PResult<crate::ast::OffsetField> {
        if let Some(index) = self.tuple_index()? {
            return Ok(crate::ast::OffsetField::Index(index));
        }
        let (name, _) = self.ident()?;
        Ok(crate::ast::OffsetField::Name(name))
    }

    /// A tuple field index at the current integer token (`t.0`, `T { 0: x }`),
    /// or None at any other token. rustc names the field by the written text,
    /// so only plain decimal is an index: `t.01`, `t.0x1`, and `t.1_` name no
    /// field (E0609), and a suffix is an error. A `Tok::Int` with no text
    /// index is exactly plain decimal (see `lexer::Tok`).
    fn tuple_index(&mut self) -> PResult<Option<u32>> {
        let Tok::Int(v, suffix, text) = self.peek() else { return Ok(None) };
        if suffix.is_some() {
            return Err(syntax(self.span(), "suffixes on a tuple index are invalid"));
        }
        if text.is_some() || v > u32::MAX as u128 {
            return Err(syntax(self.span(), "invalid tuple index: write it in plain decimal, with no leading zero or `_`"));
        }
        self.bump();
        Ok(Some(v as u32))
    }

    /// The body of an `offset_of!` call, after the `!`: `(Type, field)`,
    /// with a nested `a.b` field path allowed.
    fn offset_of_body(&mut self, start: Span) -> PResult<ExprId> {
        self.expect(Tok::LParen, "`(`")?;
        let ty = self.ty()?;
        self.expect(Tok::Comma, "`,`")?;
        let mut fields = vec![self.offset_field()?];
        while self.eat(Tok::Dot) {
            fields.push(self.offset_field()?);
        }
        self.eat(Tok::Comma);
        self.expect(Tok::RParen, "`)`")?;
        Ok(self.push_expr(Expr::OffsetOf { ty, fields }, start.to(self.prev_span())))
    }

    /// True at a `std::mem::offset_of!` or `core::mem::offset_of!` path call.
    fn at_offset_of_path(&self) -> bool {
        let name_at = |j: usize| match self.toks.get(j).map(|t| t.tok) {
            Some(Tok::Ident(s)) => Some(self.interner.get(s)),
            _ => None,
        };
        matches!(name_at(self.pos), Some("std" | "core"))
            && matches!(self.toks.get(self.pos + 1).map(|t| t.tok), Some(Tok::PathSep))
            && name_at(self.pos + 2) == Some("mem")
            && matches!(self.toks.get(self.pos + 3).map(|t| t.tok), Some(Tok::PathSep))
            && name_at(self.pos + 4) == Some("offset_of")
            && matches!(self.toks.get(self.pos + 5).map(|t| t.tok), Some(Tok::Bang))
    }

    /// Consumes one macro invocation (`path ! group`, or a
    /// `macro_rules! name group` definition) at the current token
    /// without looking inside its group. A cfg syntax check uses this
    /// in every position, as rustc parses an invocation in disabled
    /// code as one opaque node and never expands it.
    fn skip_macro_invocation(&mut self) -> PResult<(Span, Delim)> {
        let start = self.span();
        self.eat(Tok::PathSep);
        let mut last_text = String::new();
        loop {
            match self.peek() {
                Tok::Ident(s) => {
                    last_text = self.interner.get(s).to_string();
                    self.bump();
                }
                Tok::SelfUpper | Tok::SelfLower | Tok::Crate | Tok::Super => {
                    self.bump();
                }
                t => return Err(syntax(self.span(), format!("expected a macro name, found {}", tok_name(t)))),
            }
            if !self.eat(Tok::PathSep) {
                break;
            }
        }
        self.expect(Tok::Bang, "`!` after a macro name")?;
        // A definition names the macro before its group.
        if last_text == "macro_rules" && matches!(self.peek(), Tok::Ident(_)) {
            self.bump();
        }
        let close_of = |t: Tok| match t {
            Tok::LParen => Some(Tok::RParen),
            Tok::LBracket => Some(Tok::RBracket),
            Tok::LBrace => Some(Tok::RBrace),
            _ => None,
        };
        let delim = match self.peek() {
            Tok::LParen => Delim::Paren,
            Tok::LBracket => Delim::Bracket,
            Tok::LBrace => Delim::Brace,
            _ => return Err(syntax(self.span(), "expected `(` or `[` or `{` after a macro name")),
        };
        let first_close = close_of(self.peek()).unwrap();
        let mut stack = vec![first_close];
        self.bump();
        while let Some(&want) = stack.last() {
            match self.peek() {
                Tok::Eof => return Err(syntax(start, "unterminated macro invocation")),
                t if t == want => {
                    stack.pop();
                    self.bump();
                }
                t => {
                    if let Some(c) = close_of(t) {
                        stack.push(c);
                    }
                    self.bump();
                }
            }
        }
        Ok((start.to(self.prev_span()), delim))
    }

    /// One cfg-syntax macro invocation as an expression: an opaque
    /// `MacroCall` node with no token trees (they are not parsed).
    fn cfg_macro_expr(&mut self) -> PResult<ExprId> {
        let (span, delim) = self.skip_macro_invocation()?;
        Ok(self.push_expr(Expr::MacroCall(MacroCall { path: Vec::new(), delim, tokens: Vec::new(), span }), span))
    }

    fn macro_call(&mut self) -> PResult<ExprId> {
        let start = self.span();
        if self.cfg_syntax {
            return self.cfg_macro_expr();
        }
        let (name, _) = self.ident()?;
        self.bump(); // `!`
        let k = self.known;
        let table = [
            (k.println, MacroKind::Println),
            (k.print, MacroKind::Print),
            (k.eprintln, MacroKind::Eprintln),
            (k.eprint, MacroKind::Eprint),
            (k.format, MacroKind::Format),
            (k.panic, MacroKind::Panic),
            (k.vec, MacroKind::Vec),
            (k.assert, MacroKind::Assert),
            (k.assert_eq, MacroKind::AssertEq),
            (k.assert_ne, MacroKind::AssertNe),
            (k.todo, MacroKind::Todo),
            (k.unreachable, MacroKind::Unreachable),
            (k.format_args, MacroKind::FormatArgs),
        ];
        if self.interner.get(name) == "offset_of" {
            return self.offset_of_body(start);
        }
        let Some(&(_, kind)) = table.iter().find(|(s, _)| *s == name) else {
            return Err(macro_error(start));
        };
        let close = match self.bump().tok {
            Tok::LParen => Tok::RParen,
            Tok::LBracket => Tok::RBracket,
            Tok::LBrace => Tok::RBrace,
            _ => return Err(syntax(start, "expected `(` after macro name")),
        };
        let mut args = Vec::new();
        let mut fmt = Vec::new();
        let mut repeat = false;
        // Leading non-format arguments.
        let fixed = match kind {
            MacroKind::Assert => 1,
            MacroKind::AssertEq | MacroKind::AssertNe => 2,
            _ => 0,
        };
        if kind == MacroKind::Vec {
            // Elements, or from_elem's value and length: each takes outer
            // attributes, as call arguments do.
            while self.peek() != close {
                args.push(self.list_elem()?);
                if self.eat(Tok::Semi) {
                    args.push(self.list_elem()?);
                    repeat = true;
                    break;
                }
                if !self.eat(Tok::Comma) {
                    break;
                }
            }
        } else {
            let first_at = self.pos;
            let mut first_end = self.pos;
            for _ in 0..fixed {
                args.push(self.expr()?);
                if args.len() == 1 {
                    first_end = self.pos;
                }
                if !self.eat(Tok::Comma) {
                    break;
                }
            }
            // `assert!(cond)` with no message: rustc's text names the
            // condition (the expander adds it when it runs on the file).
            if kind == MacroKind::Assert && self.peek() == close {
                let strings = &self.ast.strings[self.str_base as usize..];
                let flat = self.toks[first_at..first_end]
                    .iter()
                    .map(|t| (crate::expand::tok_text(&t.tok, strings, self.interner), t.tok, t.span))
                    .collect();
                // A text lust cannot print as rustc does is the marker that
                // lowering rejects in runtime code (`ASSERT_TEXT_UNKNOWN`).
                fmt = vec![FmtPiece::Lit(match crate::expand::assert_msg::cond_text(flat) {
                    Some(cond) => format!("assertion failed: {cond}"),
                    None => crate::expand::builtin::ASSERT_TEXT_UNKNOWN.to_string(),
                })];
            }
            if args.len() < fixed {
                return Err(syntax(self.span(), "too few arguments for this macro"));
            }
            // `print!`, `eprint!`, and `format!` need a format string; `println!` and kin do not.
            let needs_str = matches!(kind, MacroKind::Print | MacroKind::Eprint | MacroKind::Format | MacroKind::FormatArgs);
            if needs_str && !matches!(self.peek(), Tok::Str(..)) {
                return Err(syntax(self.span(), "expected a format string literal"));
            }
            if let Tok::Str(si, lit_text) = self.peek() {
                let lit_span = self.bump().span;
                let mut extra = Vec::new();
                // `name = expr` arguments: (name, index in `extra`).
                let mut named: Vec<(Sym, usize)> = Vec::new();
                while self.eat(Tok::Comma) {
                    if self.peek() == close {
                        break;
                    }
                    if let Tok::Ident(name) = self.peek()
                        && self.peek_at(1) == Tok::Eq
                    {
                        let name_span = self.bump().span;
                        self.bump();
                        if named.iter().any(|(n, _)| *n == name) {
                            return Err(syntax(name_span, format!("duplicate argument named `{}`", self.interner.get(name))));
                        }
                        named.push((name, extra.len()));
                    } else if !named.is_empty() {
                        return Err(syntax(self.span(), "positional arguments cannot follow named arguments"));
                    }
                    extra.push(self.expr()?);
                }
                let s = self.ast.strings[(si + self.str_base) as usize].clone();
                // std's `panic_2021!` has its own arm for exactly `"{}"` and
                // one argument: `panic_display(&arg)` formats `*arg`, never an
                // inlined literal, so `panic!("{}", "a")` has a `String`
                // payload where `format_args!` would give a `&'static str`.
                // `assert!`'s message takes the same arm. `*&lit` keeps the
                // literal out of the inlining (lower.rs `inline_literal`).
                // The arm matches the literal token `"{}"` only: a `concat!`
                // result (its span is the whole call, not 4 bytes) or a
                // `$f:literal` fragment (another span context than the macro
                // name) does not take it. A `$($t:tt)*` forward is left out
                // too (also another context), as before.
                if matches!(kind, MacroKind::Panic | MacroKind::Assert)
                    && lit_text.is_none()
                    && lit_span.hi - lit_span.lo == 4
                    && lit_span.ctxt == start.ctxt
                    && s == "{}"
                    && named.is_empty()
                    && let [arg] = extra[..]
                    && matches!(self.ast.expr(self.peel_refs(arg)), Expr::Str(_) | Expr::Int(..))
                {
                    let sp = self.ast.expr_span(arg);
                    let r = self.push_expr(Expr::Ref { mutable: false, raw: false, expr: arg }, sp);
                    extra[0] = self.push_expr(Expr::Deref(r), sp);
                }
                let base = args.len();
                // A format string a macro produced (concat! and kin) may
                // not capture variables, as in rustc.
                fmt = self.format_string(&s, lit_span, base, &mut extra, &named, !crate::diag::is_no_capture(lit_span.ctxt))?;
                // An empty format string is still a message (`panic!("")`
                // prints an empty one, not "explicit panic").
                if fmt.is_empty() {
                    fmt.push(FmtPiece::Lit(String::new()));
                }
                args.extend(extra);
            } else if self.peek() != close {
                return Err(syntax(self.span(), "expected a format string literal"));
            }
        }
        self.expect(close, "closing delimiter")?;
        Ok(self.push_expr(Expr::Macro { kind, args, fmt, repeat }, start.to(self.prev_span())))
    }

    /// `e` without its `&` borrows (not `&raw`).
    fn peel_refs(&self, mut e: ExprId) -> ExprId {
        while let Expr::Ref { raw: false, expr, .. } = self.ast.expr(e) {
            e = *expr;
        }
        e
    }

    /// Splits a format string into pieces. `{name}` captures become extra path arguments.
    /// With `allow_capture` false (a macro-produced format string), a named
    /// capture is an error, as in rustc.
    fn format_string(
        &mut self,
        s: &str,
        span: Span,
        base: usize,
        extra: &mut Vec<ExprId>,
        named: &[(Sym, usize)],
        allow_capture: bool,
    ) -> PResult<Vec<FmtPiece>> {
        let mut pieces = Vec::new();
        let mut lit = String::new();
        let mut next = 0usize;
        let mut chars = s.chars().peekable();
        let explicit = extra.len();
        let mut used = vec![false; explicit];
        // Captured names, each one argument however often it is named.
        let mut captured: Vec<(Sym, usize)> = Vec::new();
        while let Some(c) = chars.next() {
            if c == '{' && chars.peek() == Some(&'{') {
                chars.next();
                lit.push('{');
            } else if c == '}' && chars.peek() == Some(&'}') {
                chars.next();
                lit.push('}');
            } else if c == '{' {
                let mut spec = String::new();
                loop {
                    match chars.next() {
                        Some('}') => break,
                        Some(ch) => spec.push(ch),
                        None => return Err(syntax(span, "unterminated `{` in format string")),
                    }
                }
                let (name, fmt) = spec.split_once(':').unwrap_or((spec.as_str(), ""));
                let (mut fspec, width_arg, precision_arg) = match parse_fmt_spec(fmt) {
                    Ok(s) => s,
                    Err(true) => return Err(not_yet(C_LIT, span, &format!("format spec `{{:{fmt}}}`"))),
                    Err(false) => return Err(syntax(span, format!("invalid format specification `{{:{fmt}}}`"))),
                };
                let debug = fspec.kind == FmtKind::Debug;
                // The argument a name refers to: a named argument, else a
                // captured variable (once per name).
                let mut by_name = |this: &mut Self, name: &str, extra: &mut Vec<ExprId>, used: &mut Vec<bool>| -> PResult<usize> {
                    let sym = this.interner.intern(name);
                    if let Some(&(_, i)) = named.iter().chain(captured.iter()).find(|(n, _)| *n == sym) {
                        return Ok(i);
                    }
                    if !allow_capture {
                        return Err(syntax(
                            span,
                            format!("there is no argument named `{name}`: a format string expanded from a macro cannot capture variables"),
                        ));
                    }
                    let e = this.push_expr(Expr::Path(vec![PathSeg::plain(sym)]), span);
                    extra.push(e);
                    used.push(true);
                    captured.push((sym, extra.len() - 1));
                    Ok(extra.len() - 1)
                };
                // `.*` takes the next positional argument before the value.
                // A positional reference (`{}`, `{0}`, `.*`, `1$`) names an
                // explicit argument only: a captured variable appended
                // below is never one (rustc: "N positional arguments in
                // format string, but there are M arguments").
                let mut counts = [None, None];
                let mut positional = Vec::new();
                for (slot, count) in [width_arg, precision_arg].into_iter().enumerate() {
                    counts[slot] = match count {
                        None => None,
                        Some(FmtCount::Index(n)) => {
                            positional.push(n);
                            Some(n)
                        }
                        Some(FmtCount::Next) => {
                            next += 1;
                            positional.push(next - 1);
                            Some(next - 1)
                        }
                        Some(FmtCount::Name(n)) => Some(by_name(self, &n, extra, &mut used)?),
                    };
                }
                let index = if name.is_empty() {
                    next += 1;
                    positional.push(next - 1);
                    next - 1
                } else if let Ok(n) = name.parse::<usize>() {
                    positional.push(n);
                    n
                } else {
                    by_name(self, name, extra, &mut used)?
                };
                if positional.iter().any(|&i| i >= explicit) {
                    return Err(syntax(span, "format string refers to a missing argument"));
                }
                for i in counts.iter().flatten().chain([&index]) {
                    if *i >= extra.len() {
                        return Err(syntax(span, "format string refers to a missing argument"));
                    }
                    used[*i] = true;
                }
                fspec.width_arg = counts[0].map(|i| (base + i) as u32);
                fspec.precision_arg = counts[1].map(|i| (base + i) as u32);
                if !lit.is_empty() {
                    pieces.push(FmtPiece::Lit(std::mem::take(&mut lit)));
                }
                pieces.push(FmtPiece::Arg { index: base + index, debug, spec: fspec });
            } else if c == '}' {
                return Err(syntax(span, "unmatched `}` in format string"));
            } else {
                lit.push(c);
            }
        }
        if used.iter().any(|u| !u) {
            return Err(syntax(span, "format argument never used"));
        }
        if !lit.is_empty() {
            pieces.push(FmtPiece::Lit(lit));
        }
        Ok(pieces)
    }
}

fn macro_error(span: Span) -> Diag {
    Diag::new(
        "L0401",
        span,
        "this macro call has no expanded form yet",
        "User macros and most built-in macros expand before parsing. This form (such as format_args!) has no expanded form in the subset yet.",
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::FileId;

    /// Parses `src` as a whole file.
    fn parse_src(src: &str) -> PResult<Ast> {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let lexed = crate::lexer::lex(src, FileId(0), 0, &interner)?;
        parse(&lexed, &interner, &known)
    }

    /// A parenthesized `chain`-term sum whose first term is the
    /// previous level, `levels` times: AST depth about levels * chain,
    /// while each per-shape cap (nesting, operator chain) stays met.
    fn combo(levels: usize, chain: usize) -> String {
        let mut e = "1i64".to_string();
        for _ in 0..levels {
            let mut s = String::from("(");
            s.push_str(&e);
            for _ in 1..chain {
                s.push_str(" + 1i64");
            }
            s.push(')');
            e = s;
        }
        format!("fn main() {{ let _x = {e}; }}")
    }

    /// The total AST depth guard: combinations of the per-shape caps
    /// that stay under `MAX_AST_DEPTH` parse; past it the error is
    /// L9001, never a stack overflow in a later pass. Chains of
    /// exactly the per-shape cap (2000 terms, 2000 method links)
    /// parse; one link more rejects.
    #[test]
    fn ast_depth_guard_and_chain_caps() {
        assert!(parse_src(&combo(7, 2000)).is_ok(), "depth about 14000 parses");
        let err = parse_src(&combo(9, 2000)).err().expect("depth about 18000 rejects");
        assert_eq!(err.code, "L9001");
        let sum = format!("fn main() {{ let _x = {}; }}", vec!["1i64"; 2000].join(" + "));
        assert!(parse_src(&sum).is_ok(), "a 2000-term chain parses");
        let m2000 = format!("fn main() {{ let _x = 5i64{}; }}", ".abs()".repeat(2000));
        assert!(parse_src(&m2000).is_ok(), "a 2000-link method chain parses");
        let m2001 = format!("fn main() {{ let _x = 5i64{}; }}", ".abs()".repeat(2001));
        assert_eq!(parse_src(&m2001).err().expect("2001 links reject").code, "L9001");
    }

    /// Right-recursive shapes (else-if chains, assignments, closures,
    /// `&` and `@` patterns) count against `MAX_DEPTH` too: past it
    /// the error is L9001, not a parser stack overflow (fx-parsehang).
    #[test]
    fn right_recursion_depth_cap() {
        let n = 100_000;
        let cases = [
            format!("fn f(a: bool) {{ if a {{}}{} }}", " else if a {}".repeat(n)),
            format!("fn f() {{ let mut a = 0; a{} = 0; }}", " = a".repeat(n)),
            format!("fn f() {{ let _ = {}0; }}", "|| ".repeat(n)),
            format!("fn f(y: i32) {{ let {}x = y; }}", "&".repeat(n)),
            format!("fn f(y: i32) {{ let {}x = y; }}", "a @ ".repeat(n)),
        ];
        for src in &cases {
            assert_eq!(parse_src(src).err().expect("deep shape rejects").code, "L9001", "{}", &src[..40]);
        }
    }
}
