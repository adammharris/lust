// Macro expansion (docs/ARCH.md section 6): `macro_rules!` matching and
// transcription over token trees, builtin macros, and the single-file
// macro scope rules (textual order, `#[macro_export]`, `#[macro_use]`,
// `use` imports) that run until the 6.1 outline worklist lands with
// W-RESOLVE. Expansion runs here on the lexed token stream of one file
// (or one driver chunk), before scan and parse, so items and functions a
// macro generates are scanned and parsed like written code.
//
// The frozen worklist interface is `compile_macro` plus `expand_call`:
// expand one `MacroCall` against one compiled definition to token trees.
// `lookup_macro` is the one place macro names resolve; it swaps to the
// frozen `Binding` query fns (S7) without touching callers.
pub mod assert_msg;
pub mod builtin;
pub mod lazy;
pub mod match_;
pub mod recognize;
pub mod transcribe;

use crate::ast::{MacroCall, MacroRulesDef};
use crate::def::DefId;
use crate::diag::{CtxtId, Diag, HygieneMark, Span, mark_no_capture, register_expansion, register_hygiene};
use crate::intern::{FxMap, Interner, Known, Sym};
use crate::lexer::{Delim, Lexed, Tok, Token, TokenTree, build_trees};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

// Diagnostic codes (docs/errors/REGISTRY.md, macro range).
pub const C_CAP: &str = "L0801"; // expansion caps
pub const C_UNKNOWN: &str = "L0802"; // unknown macro
pub const C_INCLUDE: &str = "L0803"; // include file not found
pub const C_AMBIG: &str = "L0805"; // local ambiguity
pub const C_CALL: &str = "L0806"; // invalid macro call or builtin input
pub const C_DEF: &str = "L0807"; // invalid macro definition
pub const C_UNSUPPORTED: &str = "L0809"; // known macro form lust does not support yet
const C_SYNTAX: &str = "L0001"; // syntax error (a malformed `recursion_limit`)
const C_ATTR: &str = "L0522"; // known attribute lust does not support yet

/// One expansion error, in the house shape (code, span, message, fix).
pub fn err(code: &'static str, span: Span, message: impl Into<String>, fix: impl Into<String>) -> Diag {
    Diag::new(code, span, message, fix)
}

/// A macro fragment kind, as written after `$name:` in a matcher.
/// `expr` and `expr_2021` are distinct kinds: the 2024 expression
/// grammar adds the `_` expression and const blocks, which an
/// `expr_2021` fragment must not match (ARCH 6.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FragKind {
    Expr,
    Expr2021,
    Ident,
    Ty,
    Pat,
    PatParam,
    Path,
    Stmt,
    Block,
    Item,
    Meta,
    Vis,
    Literal,
    Lifetime,
    Tt,
}

impl FragKind {
    /// The kind a matcher name stands for, or None for an unknown name.
    pub fn from_name(name: &str) -> Option<FragKind> {
        Some(match name {
            "expr" => FragKind::Expr,
            "expr_2021" => FragKind::Expr2021,
            "ident" => FragKind::Ident,
            "ty" => FragKind::Ty,
            "pat" => FragKind::Pat,
            "pat_param" => FragKind::PatParam,
            "path" => FragKind::Path,
            "stmt" => FragKind::Stmt,
            "block" => FragKind::Block,
            "item" => FragKind::Item,
            "meta" => FragKind::Meta,
            "vis" => FragKind::Vis,
            "literal" => FragKind::Literal,
            "lifetime" => FragKind::Lifetime,
            "tt" => FragKind::Tt,
            _ => return None,
        })
    }
    /// The matcher spelling of this kind, for diagnostics.
    pub fn name(self) -> &'static str {
        match self {
            FragKind::Expr => "expr",
            FragKind::Expr2021 => "expr_2021",
            FragKind::Ident => "ident",
            FragKind::Ty => "ty",
            FragKind::Pat => "pat",
            FragKind::PatParam => "pat_param",
            FragKind::Path => "path",
            FragKind::Stmt => "stmt",
            FragKind::Block => "block",
            FragKind::Item => "item",
            FragKind::Meta => "meta",
            FragKind::Vis => "vis",
            FragKind::Literal => "literal",
            FragKind::Lifetime => "lifetime",
            FragKind::Tt => "tt",
        }
    }
    /// Transparent kinds stay visible token by token to an inner matcher
    /// (ARCH 6.2); every other kind is one opaque unit when forwarded.
    pub fn transparent(self) -> bool {
        matches!(self, FragKind::Ident | FragKind::Lifetime | FragKind::Tt)
    }
}

/// One token tree in the expander. Like `lexer::TokenTree`, plus matched
/// fragments, which keep their kind and identity when forwarded into
/// another macro call (ARCH 6.2).
#[derive(Clone, Debug)]
pub enum Tt {
    Tok(Token),
    Delim(Delim, Vec<Tt>, Span),
    /// A matched fragment: its kind and the trees it was matched from.
    Frag(FragKind, Vec<Tt>, Span),
}

impl Tt {
    /// This tree's span (a group's opening delimiter span).
    pub fn span(&self) -> Span {
        match self {
            Tt::Tok(t) => t.span,
            Tt::Delim(_, _, span) | Tt::Frag(_, _, span) => *span,
        }
    }
    /// True when this tree is the single token `tok`.
    pub fn is_tok(&self, tok: Tok) -> bool {
        matches!(self, Tt::Tok(t) if t.tok == tok)
    }
}

/// Builds expander trees from lexer token trees.
pub fn tt_from_tree(tree: &TokenTree) -> Tt {
    match tree {
        TokenTree::Token(t) => Tt::Tok(*t),
        TokenTree::Delim(d, inner, span) => Tt::Delim(*d, inner.iter().map(tt_from_tree).collect(), *span),
    }
}

/// Turns expander trees back into lexer token trees. A fragment becomes
/// its inner trees (a statement also its `;`, see `match_::stmt_semi`):
/// the lexer form has no fragment case.
pub fn trees_from_tts(trees: &[Tt], out: &mut Vec<TokenTree>) {
    for tree in trees {
        match tree {
            Tt::Tok(t) => {
                let mut flat = Vec::new();
                push_split_token(&mut flat, t);
                out.extend(flat.into_iter().map(TokenTree::Token));
            }
            Tt::Delim(d, inner, span) => {
                let mut converted = Vec::new();
                trees_from_tts(inner, &mut converted);
                out.push(TokenTree::Delim(*d, converted, *span));
            }
            Tt::Frag(kind, inner, _) => {
                trees_from_tts(inner, out);
                if *kind == FragKind::Stmt
                    && let Some(semi) = match_::stmt_semi(inner)
                {
                    out.push(TokenTree::Token(semi));
                }
            }
        }
    }
}

/// Pushes one token into a flat token list, splitting a fused
/// `>>` or `>>=` back into the two halves the parser reads (it
/// joins them itself where a shift belongs). Every path from
/// token trees back to the parser goes through here.
pub fn push_split_token(out: &mut Vec<Token>, t: &Token) {
    match t.tok {
        Tok::Shr => {
            let mid = t.span.lo + 1;
            out.push(Token { tok: Tok::Gt, span: Span { hi: mid.min(t.span.hi), ..t.span } });
            out.push(Token { tok: Tok::Gt, span: Span { lo: mid.min(t.span.hi), ..t.span } });
        }
        Tok::ShrEq => {
            let mid = t.span.lo + 1;
            out.push(Token { tok: Tok::Gt, span: Span { hi: mid.min(t.span.hi), ..t.span } });
            out.push(Token { tok: Tok::Ge, span: Span { lo: mid.min(t.span.hi), ..t.span } });
        }
        _ => out.push(*t),
    }
}

/// Counts flat tokens in trees, groups included, for the 6.1 caps.
pub fn count_tokens(trees: &[Tt]) -> usize {
    trees
        .iter()
        .map(|t| match t {
            Tt::Tok(_) => 1,
            Tt::Delim(_, inner, _) => 2 + count_tokens(inner),
            Tt::Frag(_, inner, _) => count_tokens(inner),
        })
        .sum()
}

/// What one metavariable binds to. `Seq` nests once per repetition level
/// the variable was matched under; `Empty` is a variable inside an
/// optional group or repetition iteration that did not run.
#[derive(Clone, Debug)]
pub enum Bind {
    Leaf(Vec<Tt>),
    Seq(Vec<Bind>),
    Empty,
}

/// All metavariable bindings from one matched arm.
pub type BindMap = FxMap<Sym, Bind>;

/// Hashes one token for cache keys and matcher probes: what the token is,
/// what it names, and its hygiene context, but not its position, so code
/// that only moved still hits the expansion cache (ARCH 6.5).
pub fn hash_token(h: &mut impl Hasher, tok: &Token, strings: &[String]) {
    std::mem::discriminant(&tok.tok).hash(h);
    tok.span.ctxt.0.hash(h);
    match tok.tok {
        Tok::Ident(s) | Tok::Reserved(s) | Tok::Lifetime(s) => s.0.hash(h),
        Tok::Int(v, suffix, _) => {
            v.hash(h);
            suffix.map(|s| s as u8).hash(h);
        }
        Tok::Char(c, _) => c.hash(h),
        _ => {}
    }
    // Strings, including a literal's written text, which matching and
    // `stringify!` read: `0x1` and `1` are different inputs.
    for i in tok.tok.string_indices() {
        strings.get(i as usize).hash(h);
    }
}

/// Hashes token trees with `hash_token`.
pub fn hash_tts(trees: &[Tt], strings: &[String]) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    fn go(h: &mut impl Hasher, trees: &[Tt], strings: &[String]) {
        trees.len().hash(h);
        for tree in trees {
            match tree {
                Tt::Tok(t) => hash_token(h, t, strings),
                Tt::Delim(d, inner, _) => {
                    (*d as u8).hash(h);
                    go(h, inner, strings);
                }
                Tt::Frag(kind, inner, _) => {
                    0xffu8.hash(h);
                    (*kind as u8).hash(h);
                    go(h, inner, strings);
                }
            }
        }
    }
    go(&mut h, trees, strings);
    h.finish()
}

/// Hashes the spans of token trees against `base`: each token's file
/// and its byte range minus `base`, in tree order. With the first
/// token's start as base this is the trees' spacing shape, unchanged
/// when the code only moves; with base 0 it is the absolute layout.
/// Expansion reads spans (`line!`, `stringify!` spacing), so cache
/// keys and definition fingerprints must include what they read.
pub fn span_hash_tts(trees: &[Tt], base: u32) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    fn go(h: &mut impl Hasher, trees: &[Tt], base: u32) {
        for tree in trees {
            let span = tree.span();
            span.file.0.hash(h);
            span.lo.wrapping_sub(base).hash(h);
            span.hi.wrapping_sub(base).hash(h);
            if let Tt::Delim(_, inner, _) | Tt::Frag(_, inner, _) = tree {
                go(h, inner, base);
            }
        }
    }
    go(&mut h, trees, base);
    h.finish()
}

/// True when a token can be one segment of a macro path.
fn is_seg_tok(tok: Tok) -> bool {
    matches!(tok, Tok::Ident(_) | Tok::SelfUpper | Tok::SelfLower | Tok::Crate | Tok::Super)
}

/// The token at `trees[i]` when it is a plain token.
pub fn tok_at(trees: &[Tt], i: usize) -> Option<Token> {
    match trees.get(i) {
        Some(Tt::Tok(t)) => Some(*t),
        _ => None,
    }
}

/// The name a path-segment token stands for, as a string.
pub fn seg_text(tok: Tok, interner: &Interner) -> Option<String> {
    Some(match tok {
        Tok::Ident(s) => interner.get(s).to_string(),
        Tok::SelfUpper => "Self".to_string(),
        Tok::SelfLower => "self".to_string(),
        Tok::Crate => "crate".to_string(),
        Tok::Super => "super".to_string(),
        _ => return None,
    })
}

/// The symbol a metavariable name token stands for. Macro authors may
/// name a metavariable with a keyword (`$trait:ident` occurs in the
/// wild), so keywords count, as they do in rustc's matcher.
pub fn meta_sym(tok: Tok, interner: &Interner) -> Option<Sym> {
    match tok {
        Tok::Ident(s) => Some(s),
        Tok::As
        | Tok::Break
        | Tok::Const
        | Tok::Continue
        | Tok::Else
        | Tok::Enum
        | Tok::Fn
        | Tok::For
        | Tok::If
        | Tok::Impl
        | Tok::In
        | Tok::Let
        | Tok::Loop
        | Tok::Match
        | Tok::Mod
        | Tok::Mut
        | Tok::Pub
        | Tok::Ref
        | Tok::Return
        | Tok::SelfLower
        | Tok::SelfUpper
        | Tok::Static
        | Tok::Struct
        | Tok::Trait
        | Tok::Type
        | Tok::Unsafe
        | Tok::Use
        | Tok::Where
        | Tok::While
        | Tok::Async
        | Tok::Dyn
        | Tok::Move
        | Tok::Crate
        | Tok::Super
        | Tok::Extern
        | Tok::Await => Some(interner.intern(&tok_text(&tok, &[], interner))),
        _ => None,
    }
}

/// The symbol a path-segment token stands for.
pub fn seg_sym(tok: Tok, interner: &Interner) -> Option<Sym> {
    match tok {
        Tok::Ident(s) => Some(s),
        _ => seg_text(tok, interner).map(|text| interner.intern(&text)),
    }
}

/// The source text of one token, for `stringify!` and for reading literal
/// arguments to builtin macros.
pub fn tok_text(tok: &Tok, strings: &[String], interner: &Interner) -> String {
    use Tok::*;
    match tok {
        Ident(s) | Reserved(s) => return interner.get(*s).to_string(),
        Lifetime(s) => return format!("'{}", interner.get(*s)),
        // Literals print as written (see `lexer::lit_text`).
        Int(..) | Float(_) | Str(..) | DocStr(_) | ByteStr(_) | ByteChar(_) | Char(..) => {
            return crate::lexer::lit_text(tok, strings).unwrap_or_default().into_owned();
        }
        As => "as",
        Break => "break",
        Const => "const",
        Continue => "continue",
        Else => "else",
        Enum => "enum",
        False => "false",
        Fn => "fn",
        For => "for",
        If => "if",
        Impl => "impl",
        In => "in",
        Let => "let",
        Loop => "loop",
        Match => "match",
        Mod => "mod",
        Mut => "mut",
        Pub => "pub",
        Ref => "ref",
        Return => "return",
        SelfLower => "self",
        SelfUpper => "Self",
        Static => "static",
        Struct => "struct",
        Trait => "trait",
        True => "true",
        Type => "type",
        Unsafe => "unsafe",
        Use => "use",
        Where => "where",
        While => "while",
        Async => "async",
        Dyn => "dyn",
        Move => "move",
        Crate => "crate",
        Super => "super",
        Extern => "extern",
        Await => "await",
        LParen => "(",
        RParen => ")",
        LBrace => "{",
        RBrace => "}",
        LBracket => "[",
        RBracket => "]",
        Comma => ",",
        Semi => ";",
        Colon => ":",
        PathSep => "::",
        Dot => ".",
        DotDot => "..",
        DotDotEq => "..=",
        Ellipsis => "...",
        Arrow => "->",
        FatArrow => "=>",
        Eq => "=",
        EqEq => "==",
        Ne => "!=",
        Lt => "<",
        Le => "<=",
        Gt => ">",
        Ge => ">=",
        Plus => "+",
        Minus => "-",
        Star => "*",
        Slash => "/",
        Percent => "%",
        PlusEq => "+=",
        MinusEq => "-=",
        StarEq => "*=",
        SlashEq => "/=",
        PercentEq => "%=",
        AmpEq => "&=",
        PipeEq => "|=",
        CaretEq => "^=",
        ShlEq => "<<=",
        Amp => "&",
        AndAnd => "&&",
        Pipe => "|",
        OrOr => "||",
        Caret => "^",
        Bang => "!",
        Pound => "#",
        Question => "?",
        Underscore => "_",
        Shl => "<<",
        Shr => ">>",
        ShrEq => ">>=",
        Dollar => "$",
        At => "@",
        Eof => "",
    }
    .to_string()
}

/// True when two plain tokens match as token-tree literals in a matcher:
/// the same token, and a literal with the same written text, as rustc
/// compares them (`0x1` is not `1`, `'\x61'` is not `'a'`, and a doc
/// comment's `/// a` is `#[doc = r" a"]`). Span and context do not take part.
pub fn tok_matches(pattern: &Tok, input: &Tok, strings: &[String]) -> bool {
    match crate::lexer::lit_text(pattern, strings) {
        Some(text) => crate::lexer::lit_text(input, strings).is_some_and(|t| t == text),
        None => pattern == input,
    }
}

/// One metavariable of a matcher arm, with the repetition depth it was
/// bound at. Compile-time tables use the full record; matching reads
/// only names today, so the fields are write-only in this walk.
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub struct VarInfo {
    pub kind: FragKind,
    pub depth: u32,
}

/// One arm of a compiled macro definition.
pub struct Arm {
    pub matcher: match_::ArmMatcher,
    pub template: Vec<Tt>,
}

/// A compiled `macro_rules!` definition.
pub struct MacroDef {
    pub name: Sym,
    pub name_span: Span,
    pub arms: Vec<Arm>,
    /// Whether the def carried `#[macro_export]`. Registration acts on
    /// it at store time; the worklist reads it from the def record.
    #[allow(dead_code)]
    pub exported: bool,
    /// The def was written inside a body (not at item level), so its
    /// tokens may read locals bound before the definition (ARCH 6.3).
    pub local_def: bool,
    pub def_span: Span,
    /// Hash of the definition's raw tokens (ARCH 6.5 cache key input).
    pub fingerprint: u64,
    /// The macro name alone, for diagnostics.
    pub name_text: String,
    /// A template mentions `stringify!`, `line!`, `column!`, or
    /// `file!`: its expansion reads token positions or spacing, so
    /// the expansion cache key must include the input layout.
    pub pos_sensitive: bool,
}

/// True when template trees contain a position-reading builtin call
/// (`stringify!` spacing, `line!`/`column!`/`file!` positions).
fn template_pos_sensitive(trees: &[Tt], interner: &Interner) -> bool {
    trees.iter().enumerate().any(|(i, t)| match t {
        Tt::Tok(tok) => {
            matches!(tok.tok, Tok::Ident(s2) if matches!(interner.get(s2), "stringify" | "line" | "column" | "file"))
                && tok_at(trees, i + 1).map(|n| n.tok) == Some(Tok::Bang)
        }
        Tt::Delim(_, inner, _) => template_pos_sensitive(inner, interner),
        Tt::Frag(_, inner, _) => template_pos_sensitive(inner, interner),
    })
}

/// Hashes the span layout of input trees (every token and group
/// position), for position-sensitive expansion cache keys.
fn span_layout_hash(trees: &[Tt]) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    fn go(h: &mut impl Hasher, trees: &[Tt]) {
        for tree in trees {
            let span = tree.span();
            span.lo.hash(h);
            span.hi.hash(h);
            match tree {
                Tt::Delim(_, inner, _) | Tt::Frag(_, inner, _) => go(h, inner),
                Tt::Tok(_) => {}
            }
        }
    }
    go(&mut h, trees);
    h.finish()
}

/// Compiles the arms inside one `macro_rules!` body group into a
/// definition (matcher trees, templates, follow-set and template checks).
pub fn compile_macro(
    name: Sym,
    name_span: Span,
    body: &[Tt],
    exported: bool,
    def_span: Span,
    strings: &[String],
    interner: &Interner,
) -> Result<MacroDef, Diag> {
    let mut arms = Vec::new();
    let mut i = 0;
    while i < body.len() {
        let Some(Tt::Delim(_, matcher, mspan)) = body.get(i) else {
            let span = body.get(i).map_or(def_span, |t| t.span());
            return Err(err(C_DEF, span, "expected a macro rule", "Write each rule as `( matcher ) => { expansion };`."));
        };
        let matcher = matcher.clone();
        let mspan = *mspan;
        if tok_at(body, i + 1).map(|t| t.tok) != Some(Tok::FatArrow) {
            return Err(err(C_DEF, mspan, "expected `=>` after a macro matcher", "Write each rule as `( matcher ) => { expansion };`."));
        }
        let Some(Tt::Delim(_, template, _)) = body.get(i + 2) else {
            return Err(err(C_DEF, mspan, "expected a macro expansion group", "Write each rule as `( matcher ) => { expansion };`."));
        };
        let template = template.clone();
        let (matcher, vars) = match_::compile_arm(&matcher, mspan, interner)?;
        transcribe::check_template_vars(&template, &vars, interner)?;
        arms.push(Arm { matcher, template });
        i += 3;
        if tok_at(body, i).map(|t| t.tok) == Some(Tok::Semi) {
            i += 1;
        } else if i < body.len() {
            return Err(err(C_DEF, mspan, "expected `;` between macro rules", "End each rule with `;`."));
        }
    }
    if arms.is_empty() {
        return Err(err(C_DEF, def_span, "a macro must contain at least one rule", "Add a rule such as `() => {};`."));
    }
    let pos_sensitive = arms.iter().any(|a| template_pos_sensitive(&a.template, interner));
    Ok(MacroDef {
        name,
        name_span,
        arms,
        exported,
        local_def: false,
        def_span,
        // The fingerprint includes the body's spacing shape: an edit
        // that only respaces a template (`stringify!(x+y)` to
        // `stringify!(x + y)`) must not hit a cached transcription.
        fingerprint: hash_tts(body, strings) ^ span_hash_tts(body, body.first().map_or(0, |t| t.span().lo)),
        name_text: interner.get(name).to_string(),
        pos_sensitive,
    })
}

/// Compiles an AST `MacroRulesDef` (the shape the 6.1 worklist carries)
/// into an expander definition. The worklist is its first caller.
#[allow(dead_code)]
pub fn compile_ast_macro(def: &MacroRulesDef, exported: bool, strings: &[String], interner: &Interner) -> Result<MacroDef, Diag> {
    let body: Vec<Tt> = def.tokens.iter().map(tt_from_tree).collect();
    compile_macro(def.name, def.name_span, &body, exported, def.span, strings, interner)
}

/// The driver facts expansion needs: who interns, which file this is
/// (for `file!` and relative `include!`), the file's text (for `line!`
/// and `column!`), and the cfg environment.
pub struct ExpandCtx<'a> {
    pub interner: &'a Interner,
    pub known: &'a Known,
    /// The file path as `file!` shows it before the client view: for a
    /// Cargo crate this is workspace-relative, so it must never be used
    /// to open files. `real_path` is the filesystem path.
    pub file_path: String,
    /// The filesystem path of the file being expanded: relative
    /// `include!` family paths resolve against its directory, as in
    /// rustc (the file of the macro call site; a file pulled in by
    /// `include!` becomes the current file for its own includes).
    pub real_path: std::path::PathBuf,
    /// Env values Cargo sets for rustc for this crate (`CARGO_PKG_*`,
    /// `CARGO_MANIFEST_DIR`, `OUT_DIR`, build-script `rustc-env` pairs).
    /// `env!` reads these before the client env, as Cargo's vars win in
    /// the rustc process. Empty off the Cargo path (single file, std).
    pub cargo_env: Vec<(String, String)>,
    pub src: &'a str,
    pub cfg: builtin::CfgEnv,
    /// The module path (from the crate root) of the file being expanded.
    /// Empty for a crate root file and for single-file programs. The
    /// resolve worklist sets it per module file so `super::mac!`,
    /// `self::mac!`, and prescan module tables read from the right module.
    pub module_path: Vec<Sym>,
    /// The crate name `module_path!` starts with. The resolve worklist
    /// sets it from the crate being resolved (the Cargo package or the
    /// single-file crate name); None falls back to the current file's
    /// stem, which is right only for a crate root file.
    pub crate_name: Option<String>,
    /// The names this crate reaches as extern crates besides std, core
    /// and alloc: its dependencies (and the `$crate` magic segments of
    /// crates below it). A path call with a leading `::` (`::dep::m!`)
    /// resolves only through one of these, as rustc reads `::name` as an
    /// extern crate. Empty off the Cargo path.
    pub extern_crates: Vec<Sym>,
    /// The requesting client's env and shown paths (`for_file` gives `ClientView::PROCESS`).
    pub client: &'a ClientView,
}

/// What expansion reads from the client that asked for the compile
/// rather than from this process: the env `env!` sees, and how source
/// paths show in `file!` and `dbg!`. The driver builds one per request
/// from `protocol::Client`, so a daemon started under one env answers
/// another client as that client's own one-shot compile would.
#[derive(Clone, Default, Debug)]
pub struct ClientView {
    /// The client's env. None reads this process's start env (`builtin::compile_env`).
    pub env: Option<std::sync::Arc<Vec<(String, String)>>>,
    /// (absolute dir, shown dir): a path under the absolute dir shows as
    /// the shown dir joined with the rest, as rustc shows paths relative
    /// to the root path it was given. None shows paths as they are.
    pub shown_root: Option<(std::path::PathBuf, std::path::PathBuf)>,
}

impl ClientView {
    /// This process's env, paths shown as they are.
    pub const PROCESS: ClientView = ClientView { env: None, shown_root: None };

    /// The value of env var `name` for `env!` and `option_env!`.
    pub fn env_var(&self, name: &str) -> Option<String> {
        match &self.env {
            Some(env) => env.iter().find(|(k, _)| k == name).map(|(_, v)| v.clone()),
            None => builtin::compile_env(name),
        }
    }

    /// `path` as `file!` shows it.
    pub fn shown(&self, path: &str) -> String {
        match &self.shown_root {
            Some((abs, shown)) => match std::path::Path::new(path).strip_prefix(abs) {
                Ok(rest) => shown.join(rest).to_string_lossy().into_owned(),
                Err(_) => path.to_string(),
            },
            None => path.to_string(),
        }
    }
}

impl<'a> ExpandCtx<'a> {
    /// A context for one file under `file_path` with text `src`.
    pub fn for_file(interner: &'a Interner, known: &'a Known, file_path: &std::path::Path, src: &'a str, test: bool) -> ExpandCtx<'a> {
        ExpandCtx {
            interner,
            known,
            file_path: file_path.to_string_lossy().to_string(),
            real_path: file_path.to_path_buf(),
            cargo_env: Vec::new(),
            src,
            cfg: builtin::CfgEnv { test, debug_assertions: true, facts: Vec::new(), panic_unwind: false },
            module_path: Vec::new(),
            crate_name: None,
            extern_crates: Vec::new(),
            client: &ClientView::PROCESS,
        }
    }
    /// The crate name `module_path!` starts with: the name the resolve
    /// worklist set for this crate, or the file stem with `-` read as
    /// `_` (as rustc names a single-file crate) when none was set.
    pub fn crate_name(&self) -> String {
        if let Some(name) = &self.crate_name {
            return name.replace('-', "_");
        }
        let path = std::path::Path::new(&self.file_path);
        path.file_stem().map_or_else(|| "crate".to_string(), |s| s.to_string_lossy().replace('-', "_"))
    }
}

/// One input expansion read from outside the source text: a file an
/// `include!` family macro read (path plus a hash of its bytes), or an
/// environment variable an `env!`/`option_env!` read (name plus the
/// value seen, None when unset). The driver stores these with the
/// chunk they expanded into and drops the chunk when one changes
/// (ARCH 6.4, 6.5), so a daemon never answers from an expansion of a
/// file or environment that no longer exists in that form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Dep {
    File {
        path: std::path::PathBuf,
        hash: u64,
    },
    Env {
        name: String,
        value: Option<String>,
    },
    /// The expansion read a token position (`line!` or `column!`):
    /// a chunk carrying it must not be reused at a different start
    /// line, which the driver checks (see `deps_stale`).
    Position,
    /// The expansion showed a source path (`file!`, `dbg!`): `path` as
    /// it was, and the text it showed under the client's view then.
    Shown {
        path: String,
        shown: String,
    },
    /// Not an outside input: a cfg-disabled node of the file's own tokens
    /// (macro depth 0) that the expander grammar-checked and dropped
    /// (`check_disabled_syntax`), as file id, byte range (attribute run
    /// included), whether it was checked as an item, and whether it sat in
    /// a brace group (`check_cfg_syntax`'s `in_brace`). The body patch
    /// proves an edit inside it the same way (driver/patch.rs).
    Dropped {
        file: u32,
        lo: u32,
        hi: u32,
        item: bool,
        brace: bool,
    },
}

/// Hashes bytes for a file dependency record.
fn dep_bytes_hash(bytes: &[u8]) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    bytes.hash(&mut h);
    h.finish()
}

/// True when any recorded dependency no longer reads as it did at
/// expansion time, judging env names through `env` (the compile-time
/// env snapshot the expander itself reads). A file that cannot be
/// read counts as changed: re-expanding then reports the real error.
pub fn deps_stale_with(deps: &[Dep], env: &dyn Fn(&str) -> Option<String>) -> bool {
    deps.iter().any(|dep| match dep {
        Dep::File { path, hash } => std::fs::read(path).map_or(true, |bytes| dep_bytes_hash(&bytes) != *hash),
        Dep::Env { name, value } => env(name) != *value,
        Dep::Position | Dep::Shown { .. } | Dep::Dropped { .. } => false,
    })
}

/// `deps_stale_with` against `client`, the view this request expands
/// under (ARCH 6.4): its env, and how it shows the paths `file!` read.
pub fn deps_stale(deps: &[Dep], client: &ClientView) -> bool {
    deps_stale_in(deps, &[], client)
}

/// `deps_stale` for an expansion under a crate's Cargo env, its env names read as the
/// expander reads them (`env_value`): the multi-file resolver's expansion cache.
pub fn deps_stale_in(deps: &[Dep], cargo_env: &[(String, String)], client: &ClientView) -> bool {
    deps_stale_with(deps, &|name| env_value(cargo_env, client, name))
        || deps.iter().any(|dep| matches!(dep, Dep::Shown { path, shown } if client.shown(path) != *shown))
}

/// The compile-time value of env var `name`: the crate's Cargo env first (Cargo sets those
/// vars in the rustc process, over the inherited ones), then the requesting client's env.
pub fn env_value(cargo_env: &[(String, String)], client: &ClientView, name: &str) -> Option<String> {
    cargo_env.iter().find(|(k, _)| k == name).map(|(_, v)| v.clone()).or_else(|| client.env_var(name))
}

/// One segment of a macro call path.
#[derive(Clone)]
pub struct Seg {
    pub sym: Sym,
    pub text: String,
    pub span: Span,
}

/// A macro call the walker found: its path, the head trees as written,
/// and the delimited argument trees.
pub struct Call {
    pub segs: Vec<Seg>,
    pub leading_colon: bool,
    pub head: Vec<Tt>,
    pub delim: Delim,
    pub inner: Vec<Tt>,
    pub group_span: Span,
    pub span: Span,
}

impl Call {
    /// The last path segment as text (the macro's own name).
    pub fn name_text(&self) -> &str {
        self.segs.last().map_or("", |s| &s.text)
    }
    /// The full written path, for diagnostics.
    pub fn path_text(&self) -> String {
        let mut out = String::new();
        if self.leading_colon {
            out.push_str("::");
        }
        for (i, seg) in self.segs.iter().enumerate() {
            if i > 0 {
                out.push_str("::");
            }
            out.push_str(&seg.text);
        }
        out
    }
}

// ---- Expansion cache (ARCH 6.5) ----

#[derive(PartialEq, Eq, Hash)]
struct CacheKey {
    def_fingerprint: u64,
    input_hash: u64,
    /// Absolute input layout and the call site: a transcription embeds
    /// the caller's token spans, and `line!` and `stringify!` in the
    /// output read them, so the same tokens at a new position or with
    /// new spacing are a different expansion.
    input_span_hash: u64,
    call_file: u32,
    call_lo: u32,
    call_hi: u32,
    call_ctxt: u32,
    cfg_hash: u64,
    edition: u16,
    deps_hash: u64,
    /// Input span layout for position-sensitive templates, else 0:
    /// `f(a,b)` and `f( a , b )` hash alike as tokens but stringify
    /// apart, so they must not share a cached transcription.
    layout: u64,
}

/// One cached expansion: its trees, the strings they name as a table of
/// their own (see `own_strings`), and the expansion context it carried.
type CachedExpansion = (Vec<Tt>, Vec<String>, CtxtId);

/// The process-wide expansion cache, under a byte cap. Keys hold the call
/// position, so in a daemon every edit that moves calls adds entries and
/// strands the old ones (ts_goport: 938 MB after 300 requests). Past `cap`
/// bytes the least recently used entries go until half the cap is left
/// (a background thread frees them). Entries are a pure memo of
/// `transcribe_call`, so a dropped one only costs a transcription again.
struct ExpansionCache {
    /// Each entry with its estimated bytes and its last use (`tick`).
    map: FxMap<CacheKey, (CachedExpansion, usize, u64)>,
    bytes: usize,
    tick: u64,
    cap: usize,
}

/// The byte cap of the process-wide expansion cache (about 15 times what
/// one full resolve of ts_goport stores).
const EXPANSION_CACHE_CAP: usize = 256 << 20;

impl ExpansionCache {
    fn new(cap: usize) -> ExpansionCache {
        ExpansionCache { map: FxMap::default(), bytes: 0, tick: 0, cap }
    }

    fn get(&mut self, key: &CacheKey) -> Option<CachedExpansion> {
        self.tick += 1;
        let e = self.map.get_mut(key)?;
        e.2 = self.tick;
        Some(e.0.clone())
    }

    /// Stores one expansion of `tokens` tokens (`count_tokens`), then
    /// evicts when the cache is over its cap.
    fn insert(&mut self, key: CacheKey, exp: CachedExpansion, tokens: usize) {
        self.tick += 1;
        let bytes = tokens * std::mem::size_of::<Tt>() + exp.1.iter().map(|s| s.capacity() + std::mem::size_of::<String>()).sum::<usize>() + 128;
        self.bytes += bytes;
        if let Some(old) = self.map.insert(key, (exp, bytes, self.tick)) {
            self.bytes -= old.1;
        }
        if self.bytes > self.cap {
            let mut by_use: Vec<(u64, usize)> = self.map.values().map(|e| (e.2, e.1)).collect();
            by_use.sort_unstable();
            let (mut left, mut stamp) = (self.bytes, 0);
            for &(used, b) in &by_use {
                if left <= self.cap / 2 {
                    break;
                }
                left -= b;
                stamp = used;
            }
            // Freeing the dropped trees is millions of small frees (50 to
            // 300 ms for 128 MB on ts_goport), so it runs on its own thread,
            // not in the request and not under the cache lock.
            let mut gone = Vec::new();
            for (k, e) in std::mem::take(&mut self.map) {
                if e.2 > stamp {
                    self.map.insert(k, e);
                } else {
                    gone.push(e);
                }
            }
            self.bytes = left;
            // When no thread starts, `gone` drops here.
            crate::pool::drop_detached("lust-expcache-free", gone);
        }
    }
}

fn expansion_cache() -> &'static std::sync::Mutex<ExpansionCache> {
    static CACHE: std::sync::OnceLock<std::sync::Mutex<ExpansionCache>> = std::sync::OnceLock::new();
    CACHE.get_or_init(|| std::sync::Mutex::new(ExpansionCache::new(EXPANSION_CACHE_CAP)))
}

/// Moves the strings that tokens in `trees` name from `strings` into
/// `out`, re-indexing the tokens into `out`. The expansion cache outlives
/// one run's string table (a daemon serves many), so a cached expansion
/// keeps its strings; a hit appends them to the new table (`shift_tts`).
fn own_strings(trees: &mut [Tt], strings: &[String], out: &mut Vec<String>) {
    for tree in trees {
        match tree {
            Tt::Tok(t) => {
                for i in t.tok.string_indices_mut().into_iter().flatten() {
                    out.push(strings.get(*i as usize).cloned().unwrap_or_default());
                    *i = out.len() as u32 - 1;
                }
            }
            Tt::Delim(_, inner, _) | Tt::Frag(_, inner, _) => own_strings(inner, strings, out),
        }
    }
}

/// Adds `offset` to every string index in `trees` (see `own_strings`).
fn shift_tts(trees: &mut [Tt], offset: u32) {
    for tree in trees {
        match tree {
            Tt::Tok(t) => t.tok.shift_strings(offset),
            Tt::Delim(_, inner, _) | Tt::Frag(_, inner, _) => shift_tts(inner, offset),
        }
    }
}

static CACHE_HITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static CACHE_MISSES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// (hits, misses) of the expansion cache since process start. A daemon
/// re-check of an unchanged macro call shows up here as a hit.
pub fn cache_stats() -> (u64, u64) {
    use std::sync::atomic::Ordering;
    (CACHE_HITS.load(Ordering::Relaxed), CACHE_MISSES.load(Ordering::Relaxed))
}

/// How many entries the expansion cache holds (daemon stats lines).
pub fn cache_len() -> usize {
    expansion_cache().lock().unwrap().map.len()
}

/// True when a flat token list can contain work for the expander: a
/// `macro_rules` definition, a call to a macro the parser does not own,
/// a `use` that binds a parser macro's name (`use dep::vec;`: calls of
/// it are then the imported macro), a cfg attribute, or a
/// `recursion_limit` the expander reads. A macro-free file pays one
/// token scan and runs the unchanged pipeline.
/// Facts about crate names in one file's tokens, for macro call paths
/// (`builtin_call_path`, `lookup_macro`): the names among `std`, `core`,
/// `alloc` and the dependencies that the file binds to something else
/// (`mod std`, `use x as core`, `struct alloc`, `use a::util;`), and
/// whether the file is the crate root with a top-level `extern crate
/// alloc;` that no attribute can cfg out, the one way `alloc::` enters
/// the extern prelude.
fn crate_name_facts(tokens: &[Token], ctx: &ExpandCtx, root: bool) -> (Vec<Sym>, bool) {
    let interner = ctx.interner;
    let union = interner.intern("union");
    let mut shadowed = Vec::new();
    let mut alloc_extern = false;
    let mut depth = 0u32;
    for (i, t) in tokens.iter().enumerate() {
        match t.tok {
            Tok::LBrace | Tok::LParen | Tok::LBracket => depth += 1,
            Tok::RBrace | Tok::RParen | Tok::RBracket => depth = depth.saturating_sub(1),
            Tok::Ident(s) if matches!(interner.get(s), "std" | "core" | "alloc") || ctx.extern_crates.contains(&s) => {
                let prev = i.checked_sub(1).map(|j| tokens[j].tok);
                let next = tokens.get(i + 1).map(|n| n.tok);
                let binds = matches!(prev, Some(Tok::Mod | Tok::As | Tok::Struct | Tok::Enum | Tok::Trait | Tok::Type))
                    || prev == Some(Tok::Ident(union))
                    || (prev == Some(Tok::PathSep) && matches!(next, Some(Tok::Semi | Tok::Comma | Tok::RBrace)) && in_use_tree(tokens, i));
                if binds && !shadowed.contains(&s) {
                    shadowed.push(s);
                }
                alloc_extern |= root
                    && depth == 0
                    && interner.get(s) == "alloc"
                    && prev == Some(Tok::Crate)
                    && next == Some(Tok::Semi)
                    && i >= 2
                    && tokens[i - 2].tok == Tok::Extern
                    && (i < 3 || tokens[i - 3].tok != Tok::RBracket);
            }
            _ => {}
        }
    }
    (shadowed, alloc_extern)
}

pub fn needs_expansion(tokens: &[Token], interner: &Interner) -> bool {
    let macro_rules = interner.intern("macro_rules");
    for (i, t) in tokens.iter().enumerate() {
        match t.tok {
            Tok::Ident(s) if s == macro_rules => return true,
            // A name a use tree binds: a leaf before `;`, `,` or `}`, or
            // the name after `as`.
            Tok::Ident(s)
                if builtin::is_passthrough(interner.get(s))
                    && i > 0
                    && (tokens[i - 1].tok == Tok::As
                        || (tokens.get(i + 1).is_some_and(|n| matches!(n.tok, Tok::Semi | Tok::Comma | Tok::RBrace))
                            && in_use_tree(tokens, i))) =>
            {
                return true;
            }
            Tok::Bang => {
                // `name!`: the token before the bang names the macro.
                // A path-qualified parser macro (`std::println!`) also
                // needs the expander: it strips the prefix for the parser.
                if let Some(prev) = i.checked_sub(1).map(|j| tokens[j].tok)
                    && let Some(name) = seg_text(prev, interner)
                    && (!builtin::is_passthrough(&name) || tokens.get(i.wrapping_sub(2)).map(|t| t.tok) == Some(Tok::PathSep))
                {
                    return true;
                }
            }
            Tok::Pound => {
                // `#[cfg...]` or `#[macro...]`: the attribute's first name.
                let mut j = i + 1;
                if tokens.get(j).map(|t| t.tok) == Some(Tok::Bang) {
                    j += 1;
                }
                if tokens.get(j).map(|t| t.tok) == Some(Tok::LBracket)
                    && let Some(name) = tokens.get(j + 1).and_then(|t| seg_text(t.tok, interner))
                    && (name == "cfg" || name == "cfg_attr" || name == "macro_use" || name == "macro_export" || name == "recursion_limit" || name == "test")
                {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// True when `tokens[i]` is inside a `use` item: a `use` comes before it
/// with only use-tree tokens between (`use<..>` precise capturing is not).
fn in_use_tree(tokens: &[Token], i: usize) -> bool {
    for j in (0..i).rev() {
        match tokens[j].tok {
            Tok::Use => return tokens.get(j + 1).is_none_or(|t| t.tok != Tok::Lt),
            Tok::Ident(_) | Tok::PathSep | Tok::Comma | Tok::LBrace | Tok::RBrace | Tok::As | Tok::Star | Tok::Crate | Tok::Super => {}
            Tok::SelfLower | Tok::Underscore => {}
            _ => return false,
        }
    }
    false
}

/// The name a worklist seed defines (`macro_rules! name`), if it reads.
fn seed_name(seed: &MacroSeed, interner: &Interner) -> Option<Sym> {
    let at = seed.tokens.iter().position(|t| matches!(t.tok, Tok::Ident(s) if interner.get(s) == "macro_rules"))?;
    match (seed.tokens.get(at + 1).map(|t| t.tok), seed.tokens.get(at + 2).map(|t| t.tok)) {
        (Some(Tok::Bang), Some(Tok::Ident(s))) => Some(s),
        _ => None,
    }
}

/// True when the expander must run for this file although
/// `needs_expansion` finds no work in its tokens: a glob `use` may bring
/// a macro named like a parser macro (a seed defines one), or a
/// worklist glob seed for this file does.
fn seeds_bind_parser_name(tokens: &[Token], seeds: &[MacroSeed], extra: &[MacroSeed], interner: &Interner) -> bool {
    let glob_use = || tokens.iter().enumerate().any(|(i, t)| t.tok == Tok::Star && in_use_tree(tokens, i));
    let (imported, named) = parser_name_facts(seeds, interner);
    let (x_imported, x_named) = parser_name_facts(extra, interner);
    imported || x_imported || ((named || x_named) && glob_use())
}

/// The facts of `seeds` that `seeds_bind_parser_name` reads: some seed a
/// glob brings is ambiguous or named like a parser macro, and some seed
/// is named like one. They are the only reads of seeds a file does not
/// reach (`reach_seeds`), so the resolve's expansion cache keys every
/// file on them.
pub fn parser_name_facts(seeds: &[MacroSeed], interner: &Interner) -> (bool, bool) {
    let parser = |s: &MacroSeed| seed_name(s, interner).is_none_or(|n| builtin::is_passthrough(interner.get(n)));
    (seeds.iter().any(|s| s.import_into.is_some() && (s.ambiguous || parser(s))), seeds.iter().any(parser))
}

/// Per-file expander state. One `expand_lexed` run builds one of these.
pub struct Expander<'a> {
    ctx: &'a ExpandCtx<'a>,
    strings: Vec<String>,
    defs: Vec<Arc<MacroDef>>,
    /// Textually visible macros, in definition order. Lookups scan in
    /// reverse, so a later definition shadows an earlier one. The
    /// third field is the lexical depth (`scope_depth`) the entry
    /// was made at: macro resolution compares depths, because a
    /// glob-brought macro in an inner block does not shadow a
    /// different macro of an outer scope (rustc E0659), where a
    /// textual definition or an explicit import does.
    textual: Vec<(Sym, u32, u32)>,
    /// Names brought in by `use` in scope here, same order rule. The
    /// fourth field is the expansion the `use` was in (`expn`).
    imports: Vec<(Sym, u32, u32, u32)>,
    /// Macro names glob imports in blocks brought into scope
    /// here: (name, def, depth, expansion), or a `u32::MAX` def when
    /// the glob's own source name is ambiguous there.
    glob_macros: Vec<(Sym, u32, u32, u32)>,
    /// Type-namespace names those globs may bring (a submodule of
    /// the glob's target that macros are addressable through):
    /// (name, the module path it names, depth). A macro call
    /// path through such a name resolves it in the type namespace
    /// under the same no-shadow rule.
    glob_type_names: Vec<(Sym, Vec<Sym>, u32)>,
    /// Depth of delimiter-group nesting at the walk point (0 at a
    /// file's item list). `use` items and `macro_rules!` only
    /// appear at statement positions, so group depth orders the
    /// lexical scopes macro resolution compares.
    scope_depth: u32,
    /// The parent of each macro expansion of this walk, by expansion
    /// id. Id 0 is the file's own tokens (rustc's root expansion), its
    /// own parent. The output of every macro call, builtins included,
    /// is walked under a fresh id (`enter_expn`).
    expn_parent: Vec<u32>,
    /// The expansion whose output the walk is in.
    expn: u32,
    /// The expansion each def index was defined in, parallel to `defs`
    /// (0 for written and seeded definitions).
    def_expn: Vec<u32>,
    /// Plain macro calls walked so far, for `check_late_bindings`.
    plain_calls: Vec<PlainCall>,
    /// The `plain_calls` length where the block or module body being
    /// walked began: the calls a binding made in it can reach.
    scope_calls: usize,
    /// Item bindings rustc sees from their whole block or module, made
    /// after calls of their scope were walked: a block-level `use`, and
    /// a module-level `use` or a `#[macro_export]` definition (crate
    /// root) an expansion made. Checked at the end of the walk.
    late_bindings: Vec<LateBinding>,
    /// True while `expand_call` runs for a call written in an item list
    /// (`include!` reads items only there).
    items_call: bool,
    /// True while the list being expanded is an enum body: its first
    /// part is a variant (`A = 1 + 2`), not a block tail.
    enum_body: bool,
    /// True while the list being expanded is an impl or trait body. A
    /// `#[test]` fn there stays in every build, so the parser reports it
    /// (rustc rejects `#[test]` on an associated fn even without --test).
    assoc_body: bool,
    /// What kind of list is being expanded, for the position rules of a
    /// cfg run (`cfg_run_misplaced`).
    group: Group,
    /// Set when a `#[cfg]` that is off drops a node: the call that
    /// expands to nothing because of it is a removed list element.
    cfg_dropped: bool,
    /// `use std::vec as v;` style renames of builtin macros seen
    /// during the walk: bound name to canonical macro name.
    builtin_imports: Vec<(Sym, Sym)>,
    /// The same, per module, from the prescan.
    module_builtin_alias: FxMap<(Vec<Sym>, Sym), Sym>,
    /// `#[macro_export]` macros, visible by name at the crate root.
    exported: FxMap<Sym, u32>,
    /// Macros addressable by module path (a `use` made them so).
    by_path: FxMap<(Vec<Sym>, Sym), u32>,
    /// The module path each restricted `by_path` binding is visible
    /// within; a path call from outside it finds nothing (rustc E0603).
    by_path_vis: FxMap<(Vec<Sym>, Sym), Vec<Sym>>,
    /// Every macro definition by its defining module, from the prescan:
    /// the table `use` resolution reads (a plain macro call still needs
    /// textual order, and does not read this).
    module_defs: FxMap<(Vec<Sym>, Sym), u32>,
    /// Macro names `use` brings into each module, from the prescan:
    /// imports apply to a whole module, not from a text point.
    module_imports: FxMap<(Vec<Sym>, Sym), u32>,
    /// Macro names that globs make ambiguous in a module (see
    /// `MacroSeed::ambiguous`). An explicit import or a textual
    /// definition still wins.
    ambiguous_imports: FxMap<(Vec<Sym>, Sym), ()>,
    /// The module path of the code being walked, from the crate root.
    module: Vec<Sym>,
    /// `scope_depth` of the item list of the module being walked: a
    /// `use` at this depth binds in the module, a deeper one in a block.
    module_depth: u32,
    /// The file being expanded (its end-of-file token's), apart from
    /// macro definitions spliced in from other files.
    own_file: Option<crate::diag::FileId>,
    /// The module each textual definition written in this file was
    /// defined in, by def index. A spliced definition (inherited from
    /// a parent module or a `#[macro_use]` child file) has none.
    textual_home: FxMap<u32, Vec<Sym>>,
    /// The file `file!` currently refers to (shown form), its filesystem
    /// path for relative includes, and its text for `line!` / `column!`.
    /// `include!` swaps these.
    cur_file: String,
    cur_real: std::path::PathBuf,
    cur_src: String,
    /// The file id of the tokens being expanded (the first input token's),
    /// so `assert_msg` can tell a macro body in this file from one in
    /// another file.
    root_file: Option<crate::diag::FileId>,
    /// The crate names (`std`, `core`, `alloc`, and `ctx.extern_crates`)
    /// this file binds to something other than the crate
    /// (`crate_name_facts`): paths through them refuse.
    shadowed_crates: Vec<Sym>,
    /// This is the crate root and it has a plain `extern crate alloc;`,
    /// so `alloc::vec!` resolves (`crate_name_facts`).
    alloc_extern: bool,
    /// Hash of files and env vars read by builtins during this run
    /// (it feeds cache keys, ARCH 6.5).
    deps_hash: u64,
    /// The outside inputs this run read, in read order. The driver
    /// stores them next to the expanded chunk (see `Dep`).
    deps: Vec<Dep>,
    /// Expansion depth cap for this file: 128, or the crate root's
    /// `#![recursion_limit = "N"]` up to `RECURSION_CAP`.
    recursion_limit: u32,
    /// True when the crate asked for more depth than `RECURSION_CAP`.
    limit_capped: bool,
    total_tokens: usize,
    /// The native stack segment expansion runs on (see `expand_list`):
    /// where it began, the bytes it may use, and the bytes used by the
    /// segments below it.
    stack_base: usize,
    stack_room: usize,
    stack_below: usize,
}

/// The most expansion depth lust honors, whatever the crate's
/// `#![recursion_limit]` asks for.
const RECURSION_CAP: u32 = 2048;
/// rustc's default recursion limit.
const DEFAULT_RECURSION_LIMIT: u32 = 128;
/// Stack bytes expansion may use on its caller's thread before it
/// continues on a thread of its own. Kept small on purpose: expansion
/// also runs on threads lust does not size (unit tests, probes).
const STACK_FIRST: usize = 256 << 10;
/// The stack size of each thread expansion continues on, and the bytes
/// one such segment uses before the next; the rest is headroom for
/// work below `expand_list` (matching, transcription, fragment parses).
const STACK_HOP: usize = 64 << 20;
const STACK_HOP_ROOM: usize = 48 << 20;
/// Expansion stack, all segments together, past which a file is
/// rejected (L0801) instead of growing without bound.
const STACK_TOTAL: usize = 1 << 30;

/// One plain macro call of the walk and the binding it resolved to
/// (`Expander::note_plain_call`).
struct PlainCall {
    module: Vec<Sym>,
    name: Sym,
    span: Span,
    /// The expansion the call is in.
    expn: u32,
    /// The def it found, `u32::MAX` for a std macro.
    def: u32,
    /// The expansion and scope depth of that binding, and whether it is
    /// a textual definition (`PlainMacro::Found`) written in the call's
    /// module (`home`).
    def_expn: u32,
    depth: u32,
    textual: bool,
    home: bool,
}

/// A binding `check_late_bindings` checks against the calls walked
/// before it in its scope (`plain_calls[calls]`).
struct LateBinding {
    module: Vec<Sym>,
    name: Sym,
    def: u32,
    expn: u32,
    depth: u32,
    calls: std::ops::Range<usize>,
    /// A block glob import: rustc's glob binding is ambiguous with any
    /// different macro of the name outside it.
    glob: bool,
    /// A binding of a block, not of a module.
    block: bool,
}

/// The answer of `Expander::plain_macro` for one plain macro
/// call name.
enum PlainMacro {
    /// The def index, the expansion that made the binding, the binding's
    /// scope depth, and whether it is a textual definition (which rustc
    /// reads before any `use`).
    Found(u32, u32, u32, bool),
    /// Layers name different macros and none shadows (L0507).
    Ambiguous,
    /// The binding found first was made by a macro expansion and may
    /// not shadow a different one further out (L0507, rustc E0659).
    Expanded,
    /// No lexical layer binds the name: use the module tables.
    Fallthrough,
}

/// The address of a local: how deep the current thread's stack is.
fn stack_addr() -> usize {
    let marker = 0u8;
    std::hint::black_box(&marker) as *const u8 as usize
}

impl<'a> Expander<'a> {
    fn new(ctx: &'a ExpandCtx<'a>, strings: Vec<String>) -> Expander<'a> {
        Expander {
            ctx,
            strings,
            defs: Vec::new(),
            textual: Vec::new(),
            imports: Vec::new(),
            glob_macros: Vec::new(),
            glob_type_names: Vec::new(),
            scope_depth: 0,
            expn_parent: vec![0],
            expn: 0,
            def_expn: Vec::new(),
            plain_calls: Vec::new(),
            scope_calls: 0,
            late_bindings: Vec::new(),
            items_call: false,
            enum_body: false,
            assoc_body: false,
            group: Group::Brace,
            cfg_dropped: false,
            builtin_imports: Vec::new(),
            module_builtin_alias: FxMap::default(),
            exported: FxMap::default(),
            by_path: FxMap::default(),
            by_path_vis: FxMap::default(),
            module_defs: FxMap::default(),
            module_imports: FxMap::default(),
            module_depth: 0,
            own_file: None,
            textual_home: FxMap::default(),
            ambiguous_imports: FxMap::default(),
            module: ctx.module_path.clone(),
            cur_file: ctx.file_path.clone(),
            cur_real: ctx.real_path.clone(),
            cur_src: ctx.src.to_string(),
            root_file: None,
            shadowed_crates: Vec::new(),
            alloc_extern: false,
            deps_hash: 0,
            deps: Vec::new(),
            recursion_limit: DEFAULT_RECURSION_LIMIT,
            limit_capped: false,
            total_tokens: 0,
            stack_base: stack_addr(),
            stack_room: STACK_FIRST,
            stack_below: 0,
        }
    }

    /// Stores a string literal value and returns its index.
    pub fn push_string(&mut self, text: String) -> u32 {
        self.strings.push(text);
        self.strings.len() as u32 - 1
    }

    /// A string literal tree holding `text` at `span`.
    pub fn str_tree(&mut self, text: &str, span: Span) -> Tt {
        let i = self.push_string(text.to_string());
        Tt::Tok(Token { tok: Tok::Str(i, None), span })
    }

    /// A byte string literal tree for `bytes` at `span`: the verbatim
    /// `b"..."` text a `ByteStr` token holds, with every byte that is not
    /// printable ASCII (and `"`, `\\`) as a `\xNN` escape. `include_bytes!`
    /// makes one, so its value is the byte string's `&'static [u8; N]`.
    pub fn byte_str_tree(&mut self, bytes: &[u8], span: Span) -> Tt {
        let mut text = String::with_capacity(bytes.len() + 3);
        text.push_str("b\"");
        for &b in bytes {
            if (0x20..0x7f).contains(&b) && b != b'"' && b != b'\\' {
                text.push(b as char);
            } else {
                let _ = std::fmt::Write::write_fmt(&mut text, format_args!("\\x{b:02x}"));
            }
        }
        text.push('"');
        let i = self.push_string(text);
        Tt::Tok(Token { tok: Tok::ByteStr(i), span })
    }

    /// An identifier tree for `name` at `span`.
    pub fn ident_tree(&mut self, name: &str, span: Span) -> Tt {
        Tt::Tok(Token { tok: Tok::Ident(self.ctx.interner.intern(name)), span })
    }

    /// Folds one dependency read into the running deps hash.
    fn fold_dep(&mut self, what: &str, bytes: &[u8]) {
        let mut h = crate::intern::FxHasher::default();
        self.deps_hash.hash(&mut h);
        what.hash(&mut h);
        bytes.hash(&mut h);
        self.deps_hash = h.finish();
    }

    /// Records a file a builtin read: its path and a hash of the bytes
    /// seen, so the driver can tell when the file changes (`Dep`).
    pub fn read_dep_file(&mut self, path: &std::path::Path, bytes: &[u8]) {
        self.fold_dep(&path.to_string_lossy(), bytes);
        let dep = Dep::File { path: path.to_path_buf(), hash: dep_bytes_hash(bytes) };
        if !self.deps.contains(&dep) {
            self.deps.push(dep);
        }
    }

    /// Records that this expansion read a token position (`line!`
    /// or `column!`), whose baked value depends on the chunk's line.
    pub fn read_dep_position(&mut self) {
        if !self.deps.contains(&Dep::Position) {
            self.deps.push(Dep::Position);
        }
    }

    /// The current file as `file!` shows it, recorded as a `Dep::Shown`.
    pub fn read_dep_shown(&mut self) -> String {
        let path = self.cur_file.clone();
        let shown = self.ctx.client.shown(&path);
        self.fold_dep("shown", shown.as_bytes());
        let dep = Dep::Shown { path, shown: shown.clone() };
        if !self.deps.contains(&dep) {
            self.deps.push(dep);
        }
        shown
    }

    /// The compile-time value of env var `name` (`env_value`).
    pub fn env_lookup(&self, name: &str) -> Option<String> {
        env_value(&self.ctx.cargo_env, self.ctx.client, name)
    }

    /// Records an env var a builtin read and the value it saw.
    pub fn read_dep_env(&mut self, name: &str, value: Option<&str>) {
        self.fold_dep(&format!("env:{name}"), value.unwrap_or("").as_bytes());
        let dep = Dep::Env { name: name.to_string(), value: value.map(str::to_string) };
        if !self.deps.contains(&dep) {
            self.deps.push(dep);
        }
    }

    /// 1-based line and column of `span` in the current file's text,
    /// following expansions out to the call site (ARCH 6.3/6.4).
    pub fn line_col(&self, span: Span) -> (u32, u32) {
        let lo = span.lo as usize;
        let src = self.cur_src.as_bytes();
        let upto = lo.min(src.len());
        let line = src[..upto].iter().filter(|&&b| b == b'\n').count() as u32 + 1;
        let line_start = src[..upto].iter().rposition(|&b| b == b'\n').map_or(0, |p| p + 1);
        let col = self.cur_src[line_start..upto].chars().count() as u32 + 1;
        (line, col)
    }

    /// Lexes a small built-in template and returns its trees, stamped
    /// with `span`. Placeholder idents in the template are spliced by
    /// the caller with `splice_placeholders`.
    pub fn lex_template(&mut self, src: &str, span: Span) -> Vec<Tt> {
        let mini = crate::lexer::lex(src, span.file, 0, self.ctx.interner).expect("builtin templates lex");
        let offset = self.strings.len() as u32;
        self.strings.extend(mini.strings.iter().cloned());
        let (trees, _) = build_trees(&mini.tokens);
        fn remap(trees: &[Tt], offset: u32, span: Span) -> Vec<Tt> {
            trees
                .iter()
                .map(|t| match t {
                    Tt::Tok(tok) => {
                        let mut tok = tok.tok;
                        tok.shift_strings(offset);
                        Tt::Tok(Token { tok, span })
                    }
                    Tt::Delim(d, inner, _) => Tt::Delim(*d, remap(inner, offset, span), span),
                    Tt::Frag(k, inner, s) => Tt::Frag(*k, remap(inner, offset, span), *s),
                })
                .collect()
        }
        remap(&trees.iter().map(tt_from_tree).collect::<Vec<_>>(), offset, span)
    }

    /// Lexes an included file's text into trees in this expander's string
    /// table, keeping the file's own spans (offsets are in that file).
    pub fn lex_file_trees(&mut self, src: &str, file: crate::diag::FileId) -> Result<Vec<Tt>, Diag> {
        let mini = crate::lexer::lex(src, file, 0, self.ctx.interner)?;
        let offset = self.strings.len() as u32;
        self.strings.extend(mini.strings.iter().cloned());
        let (trees, balanced) = build_trees(&mini.tokens);
        if !balanced {
            return Err(err("L0001", Span::new(file, 0, 0), "unbalanced delimiters in included file", "Fix the syntax."));
        }
        fn remap(trees: &[Tt], offset: u32) -> Vec<Tt> {
            trees
                .iter()
                .map(|t| match t {
                    Tt::Tok(tok) => {
                        let mut kind = tok.tok;
                        kind.shift_strings(offset);
                        Tt::Tok(Token { tok: kind, span: tok.span })
                    }
                    Tt::Delim(d, inner, span) => Tt::Delim(*d, remap(inner, offset), *span),
                    Tt::Frag(k, inner, span) => Tt::Frag(*k, remap(inner, offset), *span),
                })
                .collect()
        }
        Ok(remap(&trees.iter().map(tt_from_tree).collect::<Vec<_>>(), offset))
    }
}

/// Replaces every `$`-free identifier tree named `name` in `trees` with
/// `replacement`. Builtin templates name their holes this way.
pub fn splice_placeholders(trees: Vec<Tt>, name: &str, replacement: &[Tt], interner: &Interner) -> Vec<Tt> {
    let mut out = Vec::new();
    for tree in trees {
        match tree {
            Tt::Tok(t) if matches!(t.tok, Tok::Ident(s) if interner.get(s) == name) => out.extend(replacement.iter().cloned()),
            Tt::Delim(d, inner, span) => out.push(Tt::Delim(d, splice_placeholders(inner, name, replacement, interner), span)),
            other => out.push(other),
        }
    }
    out
}

/// One macro definition the worklist hands to the expander before a
/// file walk (ARCH 6.1): a `macro_rules!` definition written in another
/// file or crate, addressable by a module path from the expanding
/// crate's root. An empty path is the crate root itself, which is where
/// `#[macro_export]` macros of this crate live (`crate::name!`); a path
/// of one segment names a dependency crate (`dep::name!`); longer paths
/// name a public re-export module (`crate::m::name!`). Seeds never enter
/// textual scope: a plain `name!` call still needs textual order or a
/// `use` in the expanding file, exactly as in Rust. `tokens` is the
/// flat token slice of the definition (from `macro_rules` to its
/// closing group and optional `;`), and `strings` is the string table
/// those tokens index into (shared, and only the strings they name); the
/// expander appends it to its own table and compiles the definition
/// there, so string values stay exact.
#[derive(Clone)]
pub struct MacroSeed {
    pub path: Vec<Sym>,
    pub tokens: Vec<Token>,
    pub strings: std::sync::Arc<Vec<String>>,
    /// When set, this seed also answers plain `name!` calls in this
    /// module path: it records a glob import (`use a::*;`) of this
    /// macro into that module, which the worklist resolved. Plain
    /// seeds leave it None and stay path-only, as before.
    pub import_into: Option<Vec<Sym>>,
    /// Set on an `import_into` seed when globs bring different macros
    /// under this name (rustc E0659): the seed defines nothing, and a
    /// plain call of the name in that module is the L0507 error.
    pub ambiguous: bool,
    /// The module path the path binding is visible within (a private
    /// or `pub(..)` re-export); None when it is public.
    pub visible_in: Option<Vec<Sym>>,
}

/// The value of a `recursion_limit` attribute from the trees after its
/// name (`= "N"`), read as rustc reads it (`usize` from the whole
/// string). A malformed one is an error in rustc, wherever it is, even
/// in a module where a valid one is ignored; so it is one here too.
fn recursion_limit_value(after_name: &[Tt], strings: &[String], span: Span) -> Result<usize, Diag> {
    match after_name {
        [Tt::Tok(eq), Tt::Tok(Token { tok: Tok::Str(idx, _), .. })] if eq.tok == Tok::Eq => {
            strings.get(*idx as usize).and_then(|s| s.parse::<usize>().ok())
        }
        _ => None,
    }
    .ok_or_else(|| {
        err(C_SYNTAX, span, "malformed `recursion_limit` attribute", "Write `#![recursion_limit = \"N\"]` with N a non-negative integer.")
    })
}

/// The crate's `#![recursion_limit = "N"]` among a root file's leading
/// inner attributes, with its span. The first one wins, as in rustc.
fn scan_recursion_limit(trees: &[Tt], strings: &[String], interner: &Interner) -> Result<Option<(usize, Span)>, Diag> {
    let mut found = None;
    let mut i = 0;
    while tok_at(trees, i).map(|t| t.tok) == Some(Tok::Pound) && tok_at(trees, i + 1).map(|t| t.tok) == Some(Tok::Bang) {
        let Some(Tt::Delim(Delim::Bracket, body, span)) = trees.get(i + 2) else { break };
        if seg_text(tok_at(body, 0).map_or(Tok::Eof, |t| t.tok), interner).as_deref() == Some("recursion_limit") {
            let n = recursion_limit_value(&body[1..], strings, *span)?;
            found.get_or_insert((n, *span));
        }
        i += 3;
    }
    Ok(found)
}

/// Expands every macro in one lexed file or chunk, returning the
/// expanded token list. A file that cannot contain macros comes back
/// unchanged (the same `Lexed`).
pub fn expand_lexed(lexed: Lexed, ctx: &ExpandCtx) -> Result<Lexed, Diag> {
    expand_lexed_seeded(lexed, ctx, &[])
}

/// `expand_lexed` with worklist macro seeds registered in the path
/// tables before the prescan, so this file's own `use` items and path
/// calls can resolve macros defined in other files and crates.
/// `expand_lexed_seeded_with_deps` without the dependency record.
pub fn expand_lexed_seeded(lexed: Lexed, ctx: &ExpandCtx, seeds: &[MacroSeed]) -> Result<Lexed, Diag> {
    expand_lexed_seeded_with_deps(lexed, ctx, seeds).map(|(lexed, _deps)| lexed)
}

/// `expand_lexed_seeded_with_deps` with no seeds: expands one lexed
/// file or chunk and returns the outside inputs expansion read
/// (`Dep` records for `include!` files and `env!` values).
pub fn expand_lexed_with_deps(lexed: Lexed, ctx: &ExpandCtx) -> Result<(Lexed, Vec<Dep>), Diag> {
    expand_lexed_seeded_with_deps(lexed, ctx, &[])
}

/// The first delimiter error in `tokens`: a closer that does not match
/// the open group, or else the innermost group still open at the end.
/// None when every delimiter is balanced (as `build_trees` judges).
pub fn delimiter_error(tokens: &[Token]) -> Option<Diag> {
    let mut open: Vec<(Tok, Span)> = Vec::new();
    for t in tokens {
        let want = match t.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => {
                open.push((t.tok, t.span));
                continue;
            }
            Tok::RParen => Tok::LParen,
            Tok::RBracket => Tok::LBracket,
            Tok::RBrace => Tok::LBrace,
            _ => continue,
        };
        if open.last().map(|o| o.0) != Some(want) {
            return Some(err("L0001", t.span, "unexpected closing delimiter", "Remove it, or close the groups opened before it first."));
        }
        open.pop();
    }
    let (_, span) = open.pop()?;
    Some(err("L0001", span, "this file contains an unclosed delimiter", "Close the group this delimiter opens."))
}

/// The seeded, dependency-returning expansion both wrappers use.
/// A file that cannot contain macros comes back unchanged (the
/// same `Lexed`, no deps). Static init closures then move into hidden
/// fns (`lazy::hoist_static_closures`, W-STD-C), so every pipeline that
/// expands sees the same items.
pub fn expand_lexed_seeded_with_deps(lexed: Lexed, ctx: &ExpandCtx, seeds: &[MacroSeed]) -> Result<(Lexed, Vec<Dep>), Diag> {
    expand_lexed_seeded_extra(lexed, ctx, seeds, &[])
}

/// `expand_lexed_seeded_with_deps` with the seeds in two lists, `seeds`
/// then `extra`: the worklist passes the crate's seeds and one file's
/// glob seeds without copying them into one list.
pub fn expand_lexed_seeded_extra(lexed: Lexed, ctx: &ExpandCtx, seeds: &[MacroSeed], extra: &[MacroSeed]) -> Result<(Lexed, Vec<Dep>), Diag> {
    let (lexed, deps) = expand_macros(lexed, ctx, seeds, extra)?;
    Ok((lazy::hoist_static_closures(lexed, ctx.interner), deps))
}

/// One list of macro seeds indexed by name, for `reach_seeds`.
pub struct SeedReach {
    /// Each seed under every `macro_rules ! NAME` in its tokens (`seed_macro` compiles the
    /// first one outside attributes; more names only take a seed more often).
    by_name: FxMap<Sym, Vec<usize>>,
    /// Each seed's distinct identifiers (`stream_idents`).
    names: Vec<Option<Vec<Sym>>>,
    /// The seeds named like a std macro.
    always: Vec<usize>,
}

impl SeedReach {
    pub fn new(seeds: &[MacroSeed], interner: &Interner) -> SeedReach {
        let macro_rules = interner.intern("macro_rules");
        let mut by_name: FxMap<Sym, Vec<usize>> = FxMap::default();
        let mut always = Vec::new();
        for (i, seed) in seeds.iter().enumerate() {
            for w in seed.tokens.windows(3) {
                if let (Tok::Ident(m), Tok::Bang, Tok::Ident(n)) = (w[0].tok, w[1].tok, w[2].tok)
                    && m == macro_rules
                {
                    let text = interner.get(n);
                    if (builtin::is_std_macro_name(text) || builtin::is_prelude_macro(text)) && always.last() != Some(&i) {
                        always.push(i);
                    }
                    by_name.entry(n).or_default().push(i);
                }
            }
        }
        SeedReach { by_name, names: seeds.iter().map(|s| stream_idents(&s.tokens, interner)).collect(), always }
    }
}

/// The distinct identifiers of `toks`, for `reach_seeds`; None when one is `include`.
pub fn stream_idents(toks: &[Token], interner: &Interner) -> Option<Vec<Sym>> {
    let include = interner.intern("include");
    let mut out: Vec<Sym> = Vec::new();
    for t in toks {
        if let Tok::Ident(s) = t.tok {
            if s == include {
                return None;
            }
            out.push(s);
        }
    }
    out.sort_unstable();
    out.dedup();
    Some(out)
}

/// The seeds of `lists` (the crate's seeds, then one file's glob seeds) that one file's
/// expansion can reach from its tokens `own` and the macro sources spliced into it
/// (`sources`, each one's `stream_idents`): per list, indices in seed order. A macro call
/// resolves by the macro's name among the seeds, and a seed's body can call others (by name,
/// or by `$crate::name`), so every seed named by an identifier of the file or of a seed
/// already in, to a fixpoint. Two more rules: a builtin's expansion can call a std macro by
/// name, so a seed of such a name is always in; and `include!` brings tokens no scan here
/// sees, so a file that names `include` reaches every seed. A seed outside the set cannot
/// change the file's expansion, so the expander seeds only these, and the resolve's
/// expansion cache keys a file on them (a moved seed re-expands only the files that reach it).
pub fn reach_seeds<'s>(lists: [&SeedReach; 2], own: &[Token], sources: impl IntoIterator<Item = Option<&'s [Sym]>>, interner: &Interner) -> [Vec<usize>; 2] {
    let every = || lists.map(|l| (0..l.names.len()).collect());
    let include = interner.intern("include");
    let mut taken = lists.map(|l| vec![false; l.names.len()]);
    let mut seen: FxMap<Sym, ()> = FxMap::default();
    let mut todo: Vec<Sym> = Vec::new();
    for t in own {
        if let Tok::Ident(s) = t.tok {
            if s == include {
                return every();
            }
            if lists.iter().any(|l| l.by_name.contains_key(&s)) && seen.insert(s, ()).is_none() {
                todo.push(s);
            }
        }
    }
    for names in sources {
        let Some(names) = names else { return every() };
        todo.extend(names.iter().copied().filter(|&s| seen.insert(s, ()).is_none()));
    }
    let mut take: Vec<(usize, usize)> = lists.iter().enumerate().flat_map(|(l, x)| x.always.iter().map(move |&i| (l, i))).collect();
    loop {
        while let Some((l, i)) = take.pop() {
            if std::mem::replace(&mut taken[l][i], true) {
                continue;
            }
            let Some(names) = &lists[l].names[i] else { return every() };
            todo.extend(names.iter().copied().filter(|&s| seen.insert(s, ()).is_none()));
        }
        let Some(s) = todo.pop() else { break };
        for (l, x) in lists.iter().enumerate() {
            take.extend(x.by_name.get(&s).into_iter().flatten().map(|&i| (l, i)));
        }
    }
    taken.map(|t| (0..t.len()).filter(|&i| t[i]).collect())
}

/// Macro expansion proper, for `expand_lexed_seeded_extra`.
fn expand_macros(lexed: Lexed, ctx: &ExpandCtx, seeds: &[MacroSeed], extra: &[MacroSeed]) -> Result<(Lexed, Vec<Dep>), Diag> {
    // rustc's lexer rejects any unbalanced or mismatched delimiter in
    // the file (attributes, cfg-off items, unused macro bodies too),
    // before any macro or parse error. The parser reads some groups
    // (attribute brackets) by depth alone, so check every file here.
    if let Some(d) = delimiter_error(&lexed.tokens) {
        return Err(d);
    }
    if !needs_expansion(&lexed.tokens, ctx.interner) && !seeds_bind_parser_name(&lexed.tokens, seeds, extra, ctx.interner) {
        return Ok((lexed, Vec::new()));
    }
    let (trees, _) = build_trees(&lexed.tokens);
    let eof = lexed.tokens.last().cloned().unwrap_or(Token { tok: Tok::Eof, span: Span::default() });
    let mut st = Expander::new(ctx, lexed.strings);
    st.root_file = lexed.tokens.first().map(|t| t.span.file);
    st.own_file = Some(eof.span.file);
    (st.shadowed_crates, st.alloc_extern) = crate_name_facts(&lexed.tokens, ctx, ctx.module_path.is_empty());
    // Only the seeds this file can reach (`reach_seeds`): a seed adds its strings to the
    // expander's table, so each one seeded would also be in the output.
    let lists = [&SeedReach::new(seeds, ctx.interner), &SeedReach::new(extra, ctx.interner)];
    let [mine, globs] = reach_seeds(lists, &lexed.tokens, std::iter::empty(), ctx.interner);
    for i in mine {
        st.seed_macro(&seeds[i])?;
    }
    for i in globs {
        st.seed_macro(&extra[i])?;
    }
    let tts: Vec<Tt> = trees.iter().map(tt_from_tree).collect();
    // Only the crate root's `#![recursion_limit]` counts, as in rustc,
    // where a module's copy is an unused attribute.
    let limit = if ctx.module_path.is_empty() { scan_recursion_limit(&tts, &st.strings, ctx.interner)? } else { None };
    if let Some((n, _)) = limit {
        st.recursion_limit = n.min(RECURSION_CAP as usize) as u32;
        st.limit_capped = n > RECURSION_CAP as usize;
    }
    st.prescan(&tts)?;
    let out = st.expand_list(tts, 0, true, false, 0)?;
    st.check_late_bindings()?;
    // A module file's top-level textual definitions reach its parent
    // under `#[macro_use]`, and the worklist passes written ones only.
    if !ctx.module_path.is_empty()
        && let Some(span) = st.expanded_textual_span()
    {
        return Err(err(
            C_UNSUPPORTED,
            span,
            "a `macro_rules!` that a macro expansion defines at the top of a module file is not supported yet",
            "Define the macro with a written `macro_rules!`, or inside a block or an inline module.",
        ));
    }
    // rustc also checks type, trait, and layout depth against a lowered
    // limit, and lust does not track those: a crate that lowers it is
    // rejected (after its macros got rustc's own depth error, if any).
    if let Some((n, span)) = limit
        && n < DEFAULT_RECURSION_LIMIT as usize
    {
        return Err(err(
            C_ATTR,
            span,
            "a `#![recursion_limit]` below the default 128 is not supported yet",
            "Remove the attribute, or set it to 128 or more.",
        ));
    }
    if std::env::var_os("LUST_EXPAND_STATS").is_some() {
        let (hits, misses) = cache_stats();
        eprintln!("expand cache: {hits} hits, {misses} misses");
    }
    let mut tokens = Vec::new();
    flatten_final(&out, &mut tokens);
    if std::env::var_os("LUST_EXPAND_DEBUG").is_some() {
        let texts: Vec<String> = tokens.iter().map(|t| tok_text(&t.tok, &st.strings, ctx.interner)).collect();
        eprintln!("expanded tokens: {}", texts.join(" "));
    }
    tokens.push(eof);
    Ok((Lexed { tokens, strings: st.strings }, st.deps))
}

/// The frozen worklist interface (ARCH 6.1): expand one call against one
/// compiled definition. `strings` must be the same table the call's
/// tokens index into. The worklist is its first caller.
#[allow(dead_code)]
pub fn expand_call(call: &MacroCall, def: &MacroDef, strings: &[String], ctx: &ExpandCtx) -> Result<Vec<TokenTree>, Diag> {
    let mut st = Expander::new(ctx, strings.to_vec());
    let inner: Vec<Tt> = call.tokens.iter().map(tt_from_tree).collect();
    let syn = Call {
        segs: call.path.iter().map(|seg| Seg { sym: seg.name, text: ctx.interner.get(seg.name).to_string(), span: call.span }).collect(),
        leading_colon: false,
        head: Vec::new(),
        delim: call.delim,
        inner,
        group_span: call.span,
        span: call.span,
    };
    let out = st.transcribe_call(def, &syn, 0)?;
    let mut trees = Vec::new();
    trees_from_tts(&out, &mut trees);
    Ok(trees)
}

/// `lust expand <file.rs>`: prints the file's expanded token stream to
/// stdout, one space between tokens. This is lust's own expansion (the
/// parser's builtin macros such as `println!` stay in their written
/// form); the macro corpus compares it against rustc's
/// `-Zunpretty=expanded` through tests/macros/normalize.py, which
/// canonicalizes the forms the two compilers print differently.
/// Returns the process exit code.
pub fn run_expand(args: &[String]) -> i32 {
    let [file] = args else {
        eprintln!("usage: lust expand <file.rs>");
        return 2;
    };
    let path = std::path::Path::new(file);
    let src = match std::fs::read_to_string(path) {
        Ok(src) => src,
        Err(e) => {
            eprintln!("error: cannot read {}: {e}", path.display());
            return 2;
        }
    };
    let mut map = crate::diag::SourceMap::default();
    map.add_file(file, &src);
    let interner = Interner::default();
    let known = Known::new(&interner);
    let out = crate::lexer::lex(&src, crate::diag::FileId(0), 0, &interner).and_then(|lexed| {
        let ctx = ExpandCtx::for_file(&interner, &known, path, &src, false);
        expand_lexed_with_deps(lexed, &ctx).map(|(lexed, _deps)| lexed)
    });
    match out {
        Ok(lexed) => {
            let mut text = String::new();
            for tok in &lexed.tokens {
                if tok.tok == Tok::Eof {
                    continue;
                }
                if !text.is_empty() {
                    text.push(' ');
                }
                text.push_str(&tok_text(&tok.tok, &lexed.strings, &interner));
            }
            println!("{text}");
            0
        }
        Err(mut d) => {
            eprint!("{}", crate::diag::render(std::slice::from_mut(&mut d), &map, &src, false, 20));
            1
        }
    }
}

/// True when a tree sequence already reads as one atomic operand in a
/// flat token stream, so precedence parens around it would only add
/// noise: a single tree, a place or call shape (`a.b`, `f(x)`,
/// `vec![x]`, `a[i]`), or a block-like expression head.
fn atomic_shaped(trees: &[Tt]) -> bool {
    if trees.len() == 1 {
        return true;
    }
    if matches!(trees.first(), Some(Tt::Tok(t)) if matches!(t.tok, Tok::Match | Tok::If | Tok::Loop | Tok::While | Tok::For)) {
        return true;
    }
    fn place_tok(tok: Tok) -> bool {
        matches!(
            tok,
            Tok::Ident(_)
                | Tok::SelfUpper
                | Tok::SelfLower
                | Tok::Crate
                | Tok::Super
                | Tok::Dot
                | Tok::PathSep
                | Tok::Int(..)
                | Tok::Bang
                | Tok::Lt
                | Tok::Gt
                | Tok::Comma
                | Tok::Lifetime(_)
        )
    }
    // A call or index shape: place tokens, then one trailing group.
    if let Some((last, head)) = trees.split_last()
        && matches!(last, Tt::Delim(_, _, _))
        && !head.is_empty()
        && head.iter().all(|t| matches!(t, Tt::Tok(tok) if place_tok(tok.tok)) || matches!(t, Tt::Delim(Delim::Bracket, _, _)))
    {
        return true;
    }
    trees.iter().all(|t| match t {
        Tt::Tok(tok) => matches!(tok.tok, Tok::Ident(_) | Tok::SelfUpper | Tok::SelfLower | Tok::Dot | Tok::PathSep | Tok::Int(..)),
        Tt::Delim(Delim::Bracket, _, _) => true,
        _ => false,
    })
}

/// Flattens expanded trees for the parser. An expression fragment with
/// more than one token gets parens, so forwarding one into a larger
/// expression keeps its rustc atomic shape in the flat token stream,
/// and a statement fragment gets its `;` (see `match_::stmt_semi`).
fn flatten_final(trees: &[Tt], out: &mut Vec<Token>) {
    for tree in trees {
        match tree {
            // A doc comment's string bound as a `literal` or `expr` is the
            // raw string literal rustc's tokens hold; the parser reads a
            // string token there.
            Tt::Frag(FragKind::Literal | FragKind::Expr | FragKind::Expr2021, inner, _)
                if matches!(inner.as_slice(), [Tt::Tok(t)] if matches!(t.tok, Tok::DocStr(_))) =>
            {
                if let [Tt::Tok(Token { tok: Tok::DocStr(i), span })] = inner.as_slice() {
                    out.push(Token { tok: Tok::Str(*i, None), span: *span });
                }
            }
            // A negative literal fragment (`-2`) is one operand; without
            // parens `- 2 . pow(..)` would read as `-(2.pow(..))`.
            Tt::Frag(FragKind::Literal, inner, span) if matches!(inner.first(), Some(Tt::Tok(t)) if t.tok == Tok::Minus) => {
                out.push(Token { tok: Tok::LParen, span: *span });
                flatten_final(inner, out);
                out.push(Token { tok: Tok::RParen, span: *span });
            }
            Tt::Frag(k, inner, span)
                if matches!(k, FragKind::Expr | FragKind::Expr2021) && count_tokens(inner) > 1 && !atomic_shaped(inner) =>
            {
                out.push(Token { tok: Tok::LParen, span: *span });
                flatten_final(inner, out);
                out.push(Token { tok: Tok::RParen, span: *span });
            }
            Tt::Tok(t) => push_split_token(out, t),
            Tt::Delim(d, inner, span) => {
                let (open, close) = match d {
                    Delim::Paren => (Tok::LParen, Tok::RParen),
                    Delim::Bracket => (Tok::LBracket, Tok::RBracket),
                    Delim::Brace => (Tok::LBrace, Tok::RBrace),
                };
                out.push(Token { tok: open, span: *span });
                flatten_final(inner, out);
                out.push(Token { tok: close, span: *span });
            }
            Tt::Frag(kind, inner, _) => {
                flatten_final(inner, out);
                if *kind == FragKind::Stmt
                    && let Some(semi) = match_::stmt_semi(inner)
                {
                    out.push(semi);
                }
            }
        }
    }
}

impl builtin::CfgRead for Expander<'_> {
    fn ident_text(&self, tok: Tok) -> Option<String> {
        match tok {
            Tok::Ident(s) => Some(self.ctx.interner.get(s).to_string()),
            _ => seg_text(tok, self.ctx.interner),
        }
    }
    fn string_text(&self, tok: Tok) -> Option<String> {
        match tok {
            Tok::Str(i, _) => self.strings.get(i as usize).cloned(),
            _ => None,
        }
    }
}

impl<'a> Expander<'a> {
    /// Finds macro definitions and module-level `use` items anywhere in
    /// the file before the main walk. Path forms (`crate::name!`) and
    /// imports apply to a whole module, not from a text point, so uses
    /// below a call site still import (ARCH 6.1). Plain calls keep
    /// textual order in the main walk; this pass only feeds the path
    /// and import tables.
    fn prescan(&mut self, trees: &[Tt]) -> Result<(), Diag> {
        type UseSite = (Vec<Sym>, Vec<Seg>, bool, Sym, bool);
        fn walk(st: &mut Expander, trees: &[Tt], module: &mut Vec<Sym>, at_module_list: bool, uses: &mut Vec<UseSite>) -> Result<(), Diag> {
            let mut i = 0;
            let mut exported = false;
            let mut cfg_off = false;
            while i < trees.len() {
                if let Some(attr) = attr_at(trees, i, st.ctx.interner) {
                    if attr.path == "macro_export" {
                        exported = true;
                    }
                    if attr.path == "cfg" {
                        cfg_off = !builtin::eval_cfg(&attr.inner, &st.ctx.cfg, st, attr.span)?;
                    }
                    if attr.path == "cfg_attr" {
                        // `cfg_attr(cond, macro_export)` exports under
                        // cond; `cfg_attr(cond, cfg(..))` gates likewise.
                        let split = attr.inner.iter().position(|t| t.is_tok(Tok::Comma)).unwrap_or(attr.inner.len());
                        if builtin::eval_cfg(&attr.inner[..split], &st.ctx.cfg, st, attr.span)? {
                            let rest = &attr.inner[split + 1.min(attr.inner.len() - split)..];
                            let head = rest.first().and_then(|t| match t {
                                Tt::Tok(tok) => seg_text(tok.tok, st.ctx.interner),
                                _ => None,
                            });
                            match head.as_deref() {
                                Some("macro_export") => exported = true,
                                Some("cfg") => {
                                    if let Some(Tt::Delim(_, group, _)) = rest.get(1) {
                                        cfg_off = !builtin::eval_cfg(group, &st.ctx.cfg, st, attr.span)?;
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    i = attr.end;
                    continue;
                }
                if let Some(def) = macro_rules_at(trees, i, st.ctx.interner) {
                    if !cfg_off {
                        let body = match &trees[def.group] {
                            Tt::Delim(_, inner, _) => inner.clone(),
                            _ => unreachable!(),
                        };
                        st.check_dup_export(def.name, def.name_span, exported)?;
                        check_def_form(trees, &def)?;
                        let mut compiled = compile_macro(def.name, def.name_span, &body, exported, def.span, &st.strings, st.ctx.interner)?;
                        compiled.local_def = !at_module_list;
                        let idx = st.register(Arc::new(compiled), exported, false);
                        if at_module_list {
                            st.module_defs.insert((module.clone(), def.name), idx);
                        }
                    }
                    exported = false;
                    cfg_off = false;
                    i = def.end;
                    continue;
                }
                // Any other tree here is the node the pending
                // attributes attach to, so they are spent: a `#[cfg]`
                // on a plain item must not leak onto a macro
                // definition that comes later in the same list.
                exported = false;
                cfg_off = false;
                if tok_at(trees, i).map(|t| t.tok) == Some(Tok::Mod)
                    && matches!(tok_at(trees, i + 1).map(|t| t.tok), Some(Tok::Ident(_)))
                    && matches!(trees.get(i + 2), Some(Tt::Delim(Delim::Brace, _, _)))
                {
                    let sym = tok_at(trees, i + 1).and_then(|t| seg_sym(t.tok, st.ctx.interner));
                    let Tt::Delim(_, inner, _) = &trees[i + 2] else { unreachable!() };
                    let inner = inner.clone();
                    if let Some(sym) = sym {
                        module.push(sym);
                    }
                    let r = walk(st, &inner, module, true, uses);
                    if sym.is_some() {
                        module.pop();
                    }
                    r?;
                    i += 3;
                    continue;
                }
                if at_module_list && let Some((public, content, end)) = use_span_at(trees, i) {
                    for (segs, leading, alias) in collect_use_sites(&trees[content..end - 1], &[], st.ctx.interner) {
                        uses.push((module.clone(), segs, leading, alias, public));
                    }
                    i = end;
                    continue;
                }
                if let Tt::Delim(_, inner, _) = &trees[i] {
                    let inner = inner.clone();
                    walk(st, &inner, module, false, uses)?;
                }
                i += 1;
            }
            Ok(())
        }
        let mut uses: Vec<UseSite> = Vec::new();
        let mut module: Vec<Sym> = self.ctx.module_path.clone();
        walk(self, trees, &mut module, true, &mut uses)?;
        // Public re-exports first, so other modules' imports can resolve
        // through the path table they create. A seed from the worklist's
        // re-export fixpoint already holds the answer for a `use` it
        // resolved (it reads textual scope at the `use`, which this
        // prescan does not), so it is kept.
        for (module, segs, leading, alias, public) in &uses {
            if *public
                && !self.by_path.contains_key(&(module.clone(), *alias))
                && let Some(idx) = self.resolve_for_use(segs, *leading, module)
            {
                self.by_path.insert((module.clone(), *alias), idx);
            }
        }
        for (module, segs, leading, alias, _) in &uses {
            let seeded = self.by_path.get(&(module.clone(), *alias)).copied();
            if let Some(idx) = seeded.or_else(|| self.resolve_for_use(segs, *leading, module)) {
                self.module_imports.insert((module.clone(), *alias), idx);
            } else if self.ctx.interner.get(*alias) != "_"
                && let Some(canon) = self.std_builtin_macro(segs)
            {
                self.module_builtin_alias.insert((module.clone(), *alias), canon);
            }
        }
        Ok(())
    }

    /// Resolves a `use` target in the prescan tables, from `from` module:
    /// exported names, `pub use` path entries, and the defining module's
    /// own definitions (for same-module re-exports).
    fn resolve_for_use(&self, segs: &[Seg], leading_colon: bool, from: &[Sym]) -> Option<u32> {
        if segs.is_empty() {
            return None;
        }
        let last = segs[segs.len() - 1].sym;
        let texts: Vec<&str> = segs.iter().map(|s| s.text.as_str()).collect();
        let middle: Vec<Sym> = segs[..segs.len() - 1].iter().map(|s| s.sym).collect();
        let path = |module: &[Sym]| self.by_path.get(&(module.to_vec(), last)).copied();
        match texts[0] {
            _ if segs.len() == 1 && !leading_colon => {
                self.module_defs.get(&(from.to_vec(), last)).copied().or_else(|| self.module_imports.get(&(from.to_vec(), last)).copied())
            }
            "crate" => {
                let module = &middle[1.min(middle.len())..];
                if module.is_empty() { self.exported.get(&last).copied() } else { path(module) }
            }
            "self" => {
                let mut module = from.to_vec();
                module.extend_from_slice(&middle[1.min(middle.len())..]);
                path(&module).or_else(|| self.module_defs.get(&(module, last)).copied())
            }
            "super" => {
                let supers = texts.iter().take_while(|&&t| t == "super").count();
                let keep = from.len().saturating_sub(supers);
                let mut module: Vec<Sym> = from[..keep].to_vec();
                module.extend_from_slice(&middle[supers.min(middle.len())..]);
                path(&module)
            }
            _ => {
                if leading_colon {
                    return if middle.is_empty() { self.exported.get(&last).copied() } else { path(&middle) };
                }
                let mut module = from.to_vec();
                module.extend_from_slice(&middle);
                path(&module).or_else(|| path(&middle)).or_else(|| self.module_defs.get(&(module.clone(), last)).copied())
            }
        }
    }

    /// Compiles one worklist macro seed into this expander's path
    /// tables. The seed's string table is appended to this run's table
    /// and its tokens are remapped before compilation, so the compiled
    /// definition reads strings from the right table. A seed whose
    /// tokens hold no `macro_rules!` definition is ignored: the
    /// worklist only seeds outline-proven definitions.
    fn seed_macro(&mut self, seed: &MacroSeed) -> Result<(), Diag> {
        let offset = self.strings.len() as u32;
        self.strings.extend(seed.strings.iter().cloned());
        let toks: Vec<Token> = seed
            .tokens
            .iter()
            .map(|t| {
                let mut tok = t.tok;
                tok.shift_strings(offset);
                Token { tok, span: t.span }
            })
            .collect();
        let (trees, balanced) = build_trees(&toks);
        if !balanced {
            return Ok(());
        }
        let tts: Vec<Tt> = trees.iter().map(tt_from_tree).collect();
        let mut i = 0;
        while i < tts.len() {
            if let Some(attr) = attr_at(&tts, i, self.ctx.interner) {
                i = attr.end;
                continue;
            }
            if let Some(def) = macro_rules_at(&tts, i, self.ctx.interner) {
                let body = match &tts[def.group] {
                    Tt::Delim(_, inner, _) => inner.clone(),
                    _ => return Ok(()),
                };
                if seed.ambiguous {
                    if let Some(module) = &seed.import_into {
                        self.ambiguous_imports.insert((module.clone(), def.name), ());
                    }
                    return Ok(());
                }
                let at_root = seed.path.is_empty();
                let compiled = compile_macro(def.name, def.name_span, &body, at_root, def.span, &self.strings, self.ctx.interner)?;
                let idx = self.register(Arc::new(compiled), at_root, false);
                self.by_path.insert((seed.path.clone(), def.name), idx);
                match &seed.visible_in {
                    Some(v) => self.by_path_vis.insert((seed.path.clone(), def.name), v.clone()),
                    None => self.by_path_vis.remove(&(seed.path.clone(), def.name)),
                };
                if let Some(module) = &seed.import_into {
                    self.module_imports.insert((module.clone(), def.name), idx);
                }
                return Ok(());
            }
            i += 1;
        }
        Ok(())
    }

    /// Stores a compiled definition. `path` also puts it in the crate
    /// root table; `textual` makes it visible from this point on.
    /// Two `#[macro_export]` definitions under one name do not shadow:
    /// the second is a definition error (rustc E0428). The same def
    /// seen again (same name span, from the walk after the prescan)
    /// is not a duplicate.
    fn check_dup_export(&self, name: Sym, name_span: Span, exported: bool) -> Result<(), Diag> {
        if exported
            && let Some(&idx) = self.exported.get(&name)
            && self.defs[idx as usize].name_span != name_span
        {
            return Err(err(
                C_DEF,
                name_span,
                format!("macro `{}` is exported more than once", self.ctx.interner.get(name)),
                "Rename one of the exported macros.",
            )
            .with_label(self.defs[idx as usize].name_span, "first exported here"));
        }
        Ok(())
    }

    fn register(&mut self, def: Arc<MacroDef>, path: bool, textual: bool) -> u32 {
        let idx = self.defs.len() as u32;
        if path {
            self.exported.insert(def.name, idx);
        }
        if textual {
            self.push_textual(def.name, idx, def.name_span);
        }
        self.defs.push(def);
        self.def_expn.push(self.expn);
        idx
    }

    /// Makes one definition textually visible from here on, and notes
    /// its module when it is written in this file.
    fn push_textual(&mut self, name: Sym, idx: u32, name_span: Span) {
        self.textual.push((name, idx, self.scope_depth));
        if Some(name_span.file) == self.own_file {
            self.textual_home.insert(idx, self.module.clone());
        }
    }

    /// True when two def indices are the same macro definition:
    /// the same `macro_rules!` compiled more than once (a textual
    /// walk and a worklist seed) keeps its name span, so defs
    /// compare by it, not by index.
    fn same_macro(&self, a: u32, b: u32) -> bool {
        a == b
            || (a != u32::MAX
                && b != u32::MAX
                && self.defs.get(a as usize).zip(self.defs.get(b as usize)).is_some_and(|(x, y)| x.name_span == y.name_span))
    }

    /// `same_macro`, and made by the same expansion: two calls of one
    /// macro that defines a `macro_rules!` give two different macros
    /// with the same name span.
    fn same_def(&self, a: u32, b: u32) -> bool {
        self.same_macro(a, b) && (a == b || self.def_expn.get(a as usize) == self.def_expn.get(b as usize))
    }

    /// The name span of a textual definition in scope here that a macro
    /// expansion made, if any.
    fn expanded_textual_span(&self) -> Option<Span> {
        let &(_, idx, _) = self.textual.iter().find(|&&(_, i, _)| self.def_expn.get(i as usize).is_some_and(|&e| e != 0))?;
        Some(self.defs[idx as usize].name_span)
    }

    /// Starts a new expansion inside the current one. Returns the
    /// current one, which the caller restores when the walk of the new
    /// expansion's output ends.
    fn enter_expn(&mut self) -> u32 {
        self.expn_parent.push(self.expn);
        std::mem::replace(&mut self.expn, self.expn_parent.len() as u32 - 1)
    }

    /// True when expansion `e` is `outer` or was made inside it.
    fn expn_within(&self, mut e: u32, outer: u32) -> bool {
        while e != outer {
            if e == 0 {
                return false;
            }
            e = self.expn_parent[e as usize];
        }
        true
    }

    /// rustc's rule for a macro-expanded macro binding (E0659,
    /// "macro-expanded `macro_rules!`s may not shadow existing macros",
    /// rustc_resolve `may_appear_after`). A plain call found `inner`,
    /// made in expansion `e_inner`, first. Every different binding of
    /// the name further out (`outers`, as (def, expansion), and the std
    /// prelude macro when `std_outer`) is ambiguous with it, unless the
    /// call or that outer binding is inside `e_inner`.
    fn expanded_shadows(&self, inner: u32, e_inner: u32, outers: impl IntoIterator<Item = (u32, u32)>, std_outer: bool) -> bool {
        if self.expn_within(self.expn, e_inner) {
            return false;
        }
        std_outer || outers.into_iter().any(|(i, e)| !self.same_def(i, inner) && !self.expn_within(e, e_inner))
    }

    /// Resolves a plain (one-segment) macro call name over the
    /// lexical candidates of this walk point: textual definitions,
    /// explicit `use`s, and block glob imports, each with its
    /// depth. Rustc's macro resolution, reduced to these layers:
    /// a textual definition at the innermost depth wins over both
    /// others at its depth; an explicit import wins over a glob
    /// at its depth or outside it, but is ambiguous with a
    /// different textual definition of an outer scope; a
    /// glob-brought name in the innermost layer is ambiguous with
    /// any different binding outside it (an outer scope, the
    /// module's imports, an exported root macro, or a std macro
    /// of the same name). The same macro by any two layers is
    /// never ambiguous. A binding a macro expansion made also obeys
    /// `expanded_shadows` (`PlainMacro::Expanded`). `Fallthrough`
    /// leaves the name to the module tables in `lookup_macro`.
    fn plain_macro(&self, name: Sym, name_text: &str) -> PlainMacro {
        // Stack order is source order and scopes nest, so the
        // latest live entry of each kind is its innermost one.
        let textual = self.textual.iter().rposition(|(n, _, _)| *n == name);
        let explicit = self.imports.iter().rev().find(|(n, ..)| *n == name).map(|&(_, i, d, e)| (i, d, e));
        let globs: Vec<(u32, u32, u32)> = self.glob_macros.iter().filter(|(n, ..)| *n == name).map(|&(_, i, d, e)| (i, d, e)).collect();
        let gdepth = globs.iter().map(|&(_, d, _)| d).max();
        let module_idx = self.module_imports.get(&(self.module.clone(), name)).copied();
        let exported_idx = if self.module.is_empty() { self.exported.get(&name).copied() } else { None };
        let std_outer = builtin::is_prelude_macro(name_text);
        let def_expn = |i: u32| self.def_expn.get(i as usize).copied().unwrap_or(0);
        // rustc reads textual scope first: a textual definition is the
        // answer whenever there is one, and a different macro a `use` or
        // glob binds is only an ambiguity check (E0659, macro_rules vs
        // modularized). It passes for a block binding when the
        // definition is inside that block, and for a module binding when
        // the definition is written in that same module.
        if let Some(pos) = textual {
            let (_, tidx, dt) = self.textual[pos];
            let home = self.textual_home.get(&tidx) == Some(&self.module);
            let ok = |idx: u32, d: Option<u32>| -> bool {
                self.same_macro(tidx, idx)
                    || match d {
                        Some(d) if d > self.module_depth => dt >= d,
                        _ => home,
                    }
            };
            let clash = self.imports.iter().any(|&(n, i, d, _)| n == name && !ok(i, Some(d)))
                || globs.iter().any(|&(i, d, _)| !ok(i, Some(d)))
                || module_idx.is_some_and(|i| !ok(i, None))
                || exported_idx.is_some_and(|i| !ok(i, None))
                || (module_idx.is_none() && !home && self.ambiguous_imports.contains_key(&(self.module.clone(), name)));
            if clash {
                return PlainMacro::Ambiguous;
            }
            // Outer textual definitions first, then the module scopes.
            let outers = (self.textual[..pos].iter().filter(|(n, _, _)| *n == name).map(|&(_, i, _)| (i, def_expn(i))))
                .chain(self.imports.iter().filter(|(n, ..)| *n == name).map(|&(_, i, _, e)| (i, e)))
                .chain(globs.iter().map(|&(i, _, e)| (i, e)))
                .chain(module_idx.map(|i| (i, 0)))
                .chain(exported_idx.map(|i| (i, def_expn(i))));
            if self.expanded_shadows(tidx, def_expn(tidx), outers, std_outer) {
                return PlainMacro::Expanded;
            }
            return PlainMacro::Found(tidx, def_expn(tidx), dt, true);
        }
        if let Some((eidx, de, ee)) = explicit
            && gdepth.is_none_or(|dg| de >= dg)
        {
            let outers = (self.imports.iter().filter(|&&(n, _, d, _)| n == name && d < de).map(|&(_, i, _, e)| (i, e)))
                .chain(globs.iter().filter(|&&(_, d, _)| d < de).map(|&(i, _, e)| (i, e)))
                .chain(module_idx.map(|i| (i, 0)))
                .chain(exported_idx.map(|i| (i, def_expn(i))));
            if self.expanded_shadows(eidx, ee, outers, std_outer) {
                return PlainMacro::Expanded;
            }
            return PlainMacro::Found(eidx, ee, de, false);
        }
        let Some(dg) = gdepth else {
            // An exported macro an expansion made, found through the
            // crate root's macro namespace.
            if module_idx.is_none()
                && let Some(x) = exported_idx
                && self.expanded_shadows(x, def_expn(x), [], std_outer)
            {
                return PlainMacro::Expanded;
            }
            return PlainMacro::Fallthrough;
        };
        let mut at: Vec<u32> = Vec::new();
        for &(i, _, _) in globs.iter().filter(|&&(_, d, _)| d == dg) {
            if !at.iter().any(|&j| self.same_macro(i, j)) {
                at.push(i);
            }
        }
        if at.len() != 1 || at[0] == u32::MAX {
            return PlainMacro::Ambiguous;
        }
        let gidx = at[0];
        let gexpn = globs.iter().find(|&&(i, d, _)| d == dg && i == gidx).map_or(0, |&(_, _, e)| e);
        let module_idx = module_idx.or(exported_idx);
        // Any different binding outside the innermost glob layer
        // counts, not only the nearest one of each kind.
        let outer_diff = self.textual.iter().any(|(n, i, d)| *n == name && *d < dg && !self.same_macro(*i, gidx))
            || self.imports.iter().any(|&(n, i, d, _)| n == name && d < dg && !self.same_macro(i, gidx))
            || globs.iter().any(|&(i, d, _)| d < dg && !self.same_macro(i, gidx))
            || module_idx.is_some_and(|i| !self.same_macro(i, gidx))
            || (module_idx.is_none() && self.ambiguous_imports.contains_key(&(self.module.clone(), name)))
            || builtin::is_std_macro_name(name_text);
        if outer_diff {
            PlainMacro::Ambiguous
        } else {
            PlainMacro::Found(gidx, gexpn, dg, false)
        }
    }

    /// Records one plain macro call and the binding it resolves to, for
    /// `check_late_bindings`. Runs at the call, in its expansion.
    fn note_plain_call(&mut self, seg: &Seg, span: Span) {
        let (def, def_expn, depth, textual) = match self.plain_macro(seg.sym, &seg.text) {
            PlainMacro::Found(i, e, d, t) => (i, e, d, t),
            PlainMacro::Fallthrough => match self.lookup_macro(std::slice::from_ref(seg), false) {
                Some(i) if self.module_imports.contains_key(&(self.module.clone(), seg.sym)) => (i, 0, self.module_depth, false),
                Some(i) => (i, self.def_expn.get(i as usize).copied().unwrap_or(0), self.module_depth, false),
                None => (u32::MAX, 0, 0, false),
            },
            PlainMacro::Ambiguous | PlainMacro::Expanded => return,
        };
        let home = textual && self.textual_home.get(&def) == Some(&self.module);
        let module = self.module.clone();
        self.plain_calls.push(PlainCall { module, name: seg.sym, span, expn: self.expn, def, def_expn, depth, textual, home });
    }

    /// rustc's resolution of the calls a late binding X can reach
    /// (`late_bindings`), which lust walked before X. Where X is inside
    /// the binding a call found (a std macro, or a `use` of an outer
    /// scope), rustc picks X: ambiguous (L0507) when an expansion made X
    /// and the call is outside it, or when X is a glob over a std macro,
    /// else a different answer than lust's (L0809). Where X is outside
    /// it, `expanded_shadows` applies.
    fn check_late_bindings(&self) -> Result<(), Diag> {
        for x in &self.late_bindings {
            for c in &self.plain_calls[x.calls.clone()] {
                if c.name != x.name || c.module != x.module {
                    continue;
                }
                let text = self.ctx.interner.get(x.name);
                if self.same_def(c.def, x.def) {
                    // A written `#[macro_export]` definition in a macro's
                    // input is in the prescan's root table before its
                    // expansion runs: the call found X itself, and X may
                    // not shadow the std macro from outside its expansion.
                    if c.def == x.def && x.expn != 0 && !self.expn_within(c.expn, x.expn) && builtin::is_prelude_macro(text) {
                        return Err(Diag::new(
                            "L0507",
                            c.span,
                            format!("`{text}` is ambiguous: a macro-expanded macro may not shadow an existing macro of this name"),
                            "Rename the macro the expansion defines or imports, or call it only inside that expansion.",
                        ));
                    }
                    continue;
                }
                let ambiguous = || {
                    Diag::new(
                        "L0507",
                        c.span,
                        format!("`{text}` is ambiguous: a macro-expanded macro may not shadow an existing macro of this name"),
                        "Rename the macro the expansion defines or imports, or call it only inside that expansion.",
                    )
                };
                // rustc reads a textual definition first; a binding of a
                // module or block is the outer one then, ambiguous unless
                // the definition is inside that block or written in that
                // module (`plain_macro`, macro_rules vs modularized).
                if c.textual && !(if x.block { c.depth >= x.depth } else { c.home }) {
                    return Err(Diag::new(
                        "L0507",
                        c.span,
                        format!("`{text}` is ambiguous: a `macro_rules!` name and a macro imported in this scope"),
                        "Rename one of them, or call the imported one by its path.",
                    ));
                }
                let x_inner = c.def == u32::MAX || (!c.textual && c.depth <= x.depth);
                if x_inner {
                    if x.expn != 0 && !self.expn_within(c.expn, x.expn) {
                        return Err(ambiguous());
                    }
                    if x.glob && c.def == u32::MAX {
                        return Err(Diag::new(
                            "L0507",
                            c.span,
                            format!("`{text}` is ambiguous: a glob import in this scope and the std macro"),
                            "Import the macro you mean explicitly, or call the std one as `std::{text}!`.",
                        ));
                    }
                    return Err(err(
                        C_UNSUPPORTED,
                        c.span,
                        format!("this call of `{text}!` comes before the `use` that binds `{text}` in its scope"),
                        "Move the `use` above the call.",
                    ));
                }
                if !self.expn_within(x.expn, c.def_expn) && !self.expn_within(c.expn, c.def_expn) {
                    return Err(ambiguous());
                }
            }
        }
        Ok(())
    }

    /// True when a plain call of this name is the L0507 glob
    /// ambiguity: the lexical layers conflict (`plain_macro`), or
    /// globs of the module left the name ambiguous with no
    /// explicit or std-rename winner. The parser-owned builtin
    /// fast path reads this too, so an ambiguous `assert!` is
    /// never read as the std macro.
    fn plain_call_ambiguous(&self, seg: &Seg) -> bool {
        match self.plain_macro(seg.sym, &seg.text) {
            PlainMacro::Ambiguous | PlainMacro::Expanded => true,
            PlainMacro::Found(..) => false,
            PlainMacro::Fallthrough => {
                self.ambiguous_imports.contains_key(&(self.module.clone(), seg.sym))
                    && !self.module_imports.contains_key(&(self.module.clone(), seg.sym))
                    && self.builtin_alias_of(seg.sym).is_none()
            }
        }
    }

    /// The ambiguity check of a macro call path (`q::z!()`): the
    /// first segment resolves in the type namespace under macro
    /// resolution, so a block glob that brings a module `q` does
    /// not shadow a different module `q` reachable from here.
    /// Errors when the module this call would walk from differs
    /// from a glob-brought one that also addresses the macro.
    fn check_macro_path_first(&self, call: &Call) -> Result<(), Diag> {
        let first = &call.segs[0];
        if matches!(first.text.as_str(), "crate" | "self" | "super") {
            return Ok(());
        }
        let last = call.segs[call.segs.len() - 1].sym;
        let middle: Vec<Sym> = call.segs[..call.segs.len() - 1].iter().map(|s| s.sym).collect();
        let mut from_here = self.module.clone();
        from_here.extend_from_slice(&middle);
        let chosen = [from_here, middle.clone()].into_iter().find(|m| self.by_path.contains_key(&(m.clone(), last)));
        let Some(chosen) = chosen else { return Ok(()) };
        for (name, gpath, _) in &self.glob_type_names {
            if *name != first.sym {
                continue;
            }
            let mut cand = gpath.clone();
            cand.extend_from_slice(&middle[1.min(middle.len())..]);
            if cand != chosen {
                return Err(crate::resolve::imports::ambiguous_diag(&first.text, call.span));
            }
        }
        Ok(())
    }

    /// True when a call path names a builtin macro as rustc 1.99 resolves
    /// it: a plain name, or a std path `builtin::std_macro_path` lists,
    /// with or without a leading `::`, whose crate segment really is that
    /// crate here (no binding of the name in this file; `alloc` only
    /// after the root's `extern crate alloc;`). `::println!` names an
    /// extern crate `println` (E0433).
    fn builtin_call_path(&self, segs: &[Seg], leading_colon: bool) -> bool {
        if segs.len() == 1 {
            return !leading_colon;
        }
        let texts: Vec<&str> = segs.iter().map(|s| s.text.as_str()).collect();
        if self.shadowed_crates.contains(&segs[0].sym) || (texts[0] == "alloc" && !self.alloc_extern) {
            return false;
        }
        builtin::std_macro_path(&texts)
    }

    /// Resolves a macro call path to a definition index. This is the
    /// single macro lookup entry point: today it reads this single
    /// file's textual scope, imports, and path tables. S7's frozen
    /// `Program::macro_binding` query is landed, but it answers from a
    /// collected `Program`, which holds no macro defs yet (expansion
    /// runs before parse and collect, and macro answers are `Absent`
    /// there by design until W-RESOLVE). When the 6.1 worklist makes
    /// collect own macro defs, this function is the one place that
    /// moves behind `macro_binding`; nothing else changes.
    fn lookup_macro(&self, segs: &[Seg], leading_colon: bool) -> Option<u32> {
        if segs.is_empty() {
            return None;
        }
        let last = segs[segs.len() - 1].sym;
        let texts: Vec<&str> = segs.iter().map(|s| s.text.as_str()).collect();
        // Dependency macros sit in the path tables under the crate name,
        // as if it were a root module. In rustc `crate::util` (also
        // through `self` and `super`) reaches a dependency only by an
        // import lust does not track, so it finds nothing here.
        let by_module = |module: &[Sym]| -> Option<u32> {
            let from_crate = !leading_colon && matches!(texts[0], "crate" | "self" | "super");
            if from_crate && module.first().is_some_and(|c| self.ctx.extern_crates.contains(c)) {
                return None;
            }
            let key = (module.to_vec(), last);
            let visible = self.by_path_vis.get(&key).is_none_or(|v| self.module.starts_with(v));
            if visible { self.by_path.get(&key).copied() } else { None }
        };
        if !leading_colon && segs.len() == 1 {
            match self.plain_macro(last, texts[0]) {
                PlainMacro::Found(idx, ..) => return Some(idx),
                PlainMacro::Ambiguous | PlainMacro::Expanded => return None,
                PlainMacro::Fallthrough => {}
            }
            if let Some(idx) = self.module_imports.get(&(self.module.clone(), last)).copied() {
                return Some(idx);
            }
            if self.ambiguous_imports.contains_key(&(self.module.clone(), last)) {
                return None;
            }
            // An exported macro lives in the crate root's macro
            // namespace, so a plain call in the root module finds it
            // whatever the textual order.
            return if self.module.is_empty() { self.exported.get(&last).copied() } else { None };
        }
        // Path forms, resolved against module paths from the crate root.
        let middle: Vec<Sym> = segs[..segs.len() - 1].iter().map(|s| s.sym).collect();
        match texts[0] {
            "crate" => {
                let module = &middle[1.min(middle.len())..];
                if module.is_empty() { self.exported.get(&last).copied().or_else(|| by_module(module)) } else { by_module(module) }
            }
            "self" => {
                let mut module = self.module.clone();
                module.extend_from_slice(&middle[1.min(middle.len())..]);
                if module.is_empty() { self.exported.get(&last).copied().or_else(|| by_module(&module)) } else { by_module(&module) }
            }
            "super" => {
                let supers = texts.iter().take_while(|&&t| t == "super").count();
                // `super` past the crate root is rustc E0433.
                if supers > self.module.len() {
                    return None;
                }
                let mut module: Vec<Sym> = self.module[..self.module.len() - supers].to_vec();
                module.extend_from_slice(&middle[supers.min(middle.len())..]);
                by_module(&module)
            }
            _ => {
                // `::name` and a first segment the current module does not
                // bind name an extern crate (rustc 2018+): a dependency,
                // never a module of this crate. `::m!` names no macro.
                let extern_crate = middle.first().is_some_and(|c| self.ctx.extern_crates.contains(c));
                // A file that binds the name to something else (`mod util`)
                // shares the table key with the dependency: refuse.
                if extern_crate && self.shadowed_crates.contains(&middle[0]) {
                    return None;
                }
                if leading_colon {
                    return if extern_crate { by_module(&middle) } else { None };
                }
                let mut module = self.module.clone();
                module.extend_from_slice(&middle);
                by_module(&module)
                    .or_else(|| self.glob_path_lookup(segs))
                    .or_else(|| if extern_crate { by_module(&middle) } else { None })
            }
        }
    }

    /// Matches and transcribes one user macro call against `def`, with
    /// the expansion cache in front (ARCH 6.5). The result is one
    /// expansion step only, never chased: callers re-walk it.
    pub fn transcribe_call(&mut self, def: &MacroDef, call: &Call, depth: u32) -> Result<Vec<Tt>, Diag> {
        use std::sync::atomic::Ordering;
        self.check_depth(depth, 0, call.span, || def.name_text.clone())?;
        let key = CacheKey {
            def_fingerprint: def.fingerprint,
            input_hash: hash_tts(&call.inner, &self.strings),
            input_span_hash: span_hash_tts(&call.inner, 0),
            call_file: call.span.file.0,
            call_lo: call.span.lo,
            call_hi: call.span.hi,
            call_ctxt: call.span.ctxt.0,
            cfg_hash: self.ctx.cfg.hash(),
            edition: 2024,
            deps_hash: 0,
            layout: if def.pos_sensitive { span_layout_hash(&call.inner) } else { 0 },
        };
        let hit = expansion_cache().lock().unwrap().get(&key);
        if let Some((cached, strings, old_ctxt)) = hit {
            CACHE_HITS.fetch_add(1, Ordering::Relaxed);
            let ctxt =
                register_expansion(crate::diag::Expansion { macro_def: DefId::PLACEHOLDER, call_span: call.span, parent: call.span.ctxt });
            register_hygiene(ctxt, HygieneMark { def_span: def.name_span, local_def: def.local_def });
            let mut out = cached;
            shift_tts(&mut out, self.strings.len() as u32);
            self.strings.extend(strings);
            restamp_ctxt(&mut out, old_ctxt, ctxt);
            return Ok(out);
        }
        CACHE_MISSES.fetch_add(1, Ordering::Relaxed);
        let mut chosen: Option<(usize, BindMap)> = None;
        let mut matcher = match_::Matcher::new(self.ctx.interner, self.ctx.known, &self.strings, call.span);
        for (arm_i, arm) in def.arms.iter().enumerate() {
            match match_::match_arm(&mut matcher, &arm.matcher, &call.inner)? {
                match_::ArmMatch::Match(binds) => {
                    chosen = Some((arm_i, binds));
                    break;
                }
                match_::ArmMatch::NoMatch => {}
                // Local ambiguity is fatal: rustc stops at the first
                // ambiguous token, it does not fall through to a later arm.
                match_::ArmMatch::Ambiguous => {
                    return Err(err(
                        C_AMBIG,
                        call.span,
                        format!("local ambiguity when calling macro `{}!`", def.name_text),
                        "Make the matcher decide each token's role without guessing between fragments.",
                    )
                    .with_label(def.def_span, "the macro is defined here"));
                }
                // A fragment parser that began and failed is rustc's
                // hard error: the call fails here instead of falling
                // through to a later arm that token-matches the input.
                match_::ArmMatch::BadFragment => {
                    return Err(err(
                        C_CALL,
                        call.span,
                        format!("a fragment in this call to `{}!` does not parse", def.name_text),
                        "Check the call tokens against the fragment kinds in the macro's rules.",
                    )
                    .with_label(def.def_span, "the macro is defined here"));
                }
            }
        }
        let Some((arm_i, binds)) = chosen else {
            return Err(err(
                C_CALL,
                call.span,
                format!("no rules expected this input to macro `{}!`", def.name_text),
                "Check the call against the macro's rules.",
            )
            .with_label(def.def_span, "the macro is defined here"));
        };
        let ctxt =
            register_expansion(crate::diag::Expansion { macro_def: DefId::PLACEHOLDER, call_span: call.span, parent: call.span.ctxt });
        register_hygiene(ctxt, HygieneMark { def_span: def.name_span, local_def: def.local_def });
        let out = transcribe::transcribe(&def.arms[arm_i].template, &binds, ctxt, call.span, self.ctx.interner)
            .map_err(|d| d.with_label(def.def_span, "the macro is defined here"))?;
        let count = count_tokens(&out);
        if count > 1_000_000 {
            return Err(err(
                C_CAP,
                call.span,
                format!("expansion of `{}!` is too large", def.name_text),
                "Simplify the macro or the call.",
            ));
        }
        self.total_tokens += count;
        if self.total_tokens > 16_000_000 {
            return Err(err(C_CAP, call.span, "total expanded size limit reached", "Simplify the macros in this file."));
        }
        let mut cached = out.clone();
        let mut strings = Vec::new();
        own_strings(&mut cached, &self.strings, &mut strings);
        expansion_cache().lock().unwrap().insert(key, (cached, strings, ctxt), count);
        Ok(out)
    }
}

/// Re-contexts cached output: tokens stamped with the cached expansion's
/// context take the new expansion's context instead (ARCH 6.5).
fn restamp_ctxt(trees: &mut [Tt], old: CtxtId, new: CtxtId) {
    fn fix(span: &mut Span, old: CtxtId, new: CtxtId) {
        if span.ctxt == old {
            span.ctxt = new;
        }
    }
    for tree in trees {
        match tree {
            Tt::Tok(t) => fix(&mut t.span, old, new),
            Tt::Delim(_, inner, span) => {
                fix(span, old, new);
                restamp_ctxt(inner, old, new);
            }
            // Fragment tokens are the caller's, not the macro body's.
            Tt::Frag(_, _, _) => {}
        }
    }
}

/// An attribute the walker found at a list position.
pub struct AttrInfo {
    /// Path as written, segments joined by `::`.
    pub path: String,
    /// The trees inside the brackets, after the path (raw, with any
    /// leading `=` or group intact, starting past the path tokens).
    pub inner: Vec<Tt>,
    /// Index just past this attribute in the list it was found in.
    pub end: usize,
    pub span: Span,
    pub inner_attr: bool,
}

/// If an attribute (`#[...]` or `#![...]`) starts at `trees[i]`, reads it.
pub fn attr_at(trees: &[Tt], i: usize, interner: &Interner) -> Option<AttrInfo> {
    if !matches!(trees.get(i), Some(Tt::Tok(t)) if t.tok == Tok::Pound) {
        return None;
    }
    let span = trees[i].span();
    let mut j = i + 1;
    let mut inner_attr = false;
    if tok_at(trees, j).map(|t| t.tok) == Some(Tok::Bang) {
        inner_attr = true;
        j += 1;
    }
    let Tt::Delim(Delim::Bracket, body, _) = trees.get(j)? else { return None };
    // `#[unsafe(..)]` reads as one attribute named `unsafe`, so no
    // attribute the expander acts on (cfg and kin) matches it.
    if tok_at(body, 0).map(|t| t.tok) == Some(Tok::Unsafe)
        && let Some(Tt::Delim(Delim::Paren, group, _)) = body.get(1)
    {
        return Some(AttrInfo { path: "unsafe".to_string(), inner: group.clone(), end: j + 1, span, inner_attr });
    }
    // Path: segments joined by :: from the front of the body. A leading
    // `::` stays in the path text, so `#[::cfg(..)]` is not `cfg`.
    let global = tok_at(body, 0).map(|t| t.tok) == Some(Tok::PathSep);
    let mut segs = Vec::new();
    let mut k = usize::from(global);
    loop {
        match tok_at(body, k).map(|t| t.tok) {
            Some(t) if is_seg_tok(t) => {
                segs.push(t);
                k += 1;
            }
            _ => break,
        }
        if tok_at(body, k).map(|t| t.tok) == Some(Tok::PathSep) {
            k += 1;
        } else {
            break;
        }
    }
    if segs.is_empty() {
        return None;
    }
    // After the path: nothing, one group, or `= value`. Anything else
    // (`#[cfg(all()) x]`) is not an attribute the expander acts on; the
    // parser reports its grammar error.
    match body.get(k) {
        None => {}
        Some(Tt::Delim(..)) if k + 1 == body.len() => {}
        Some(Tt::Tok(t)) if t.tok == Tok::Eq => {}
        _ => return None,
    }
    // cfg and friends read only the group's trees; a `path(...)` attr
    // keeps the group as its input, a `path = v` keeps from the `=` on.
    let inner = match body.get(k) {
        Some(Tt::Delim(_, group, _)) => group.clone(),
        _ => body[k..].to_vec(),
    };
    let path = segs.iter().filter_map(|t| seg_text(*t, interner)).collect::<Vec<_>>().join("::");
    let path = if global { format!("::{path}") } else { path };
    Some(AttrInfo { path, inner, end: j + 1, span, inner_attr })
}

/// Checks a written `#[macro_export ..]` input: nothing or
/// `(local_inner_macros)`. An `= v` input is malformed (rustc E0539);
/// any other list is rustc's deny-by-default lint
/// `invalid_macro_export_arguments` unless `leveled`.
fn check_macro_export_input(trees: &[Tt], attr: &AttrInfo, leveled: bool, interner: &Interner) -> Result<(), Diag> {
    let Some(Tt::Delim(Delim::Bracket, body, _)) = attr.end.checked_sub(1).and_then(|k| trees.get(k)) else { return Ok(()) };
    let is_name = |t: &Tt, name: &str| matches!(t, Tt::Tok(x) if seg_text(x.tok, interner).as_deref() == Some(name));
    // `#[macro_export ..]`, or `#[cfg_attr(cond, macro_export ..)]`: the
    // input is what follows the name, up to the next top-level comma.
    let rest: &[Tt] = if body.first().is_some_and(|t| is_name(t, "macro_export")) {
        &body[1..]
    } else if body.first().is_some_and(|t| is_name(t, "cfg_attr"))
        && let Some(Tt::Delim(Delim::Paren, group, _)) = body.get(1)
        && let Some(at) = group.iter().position(|t| is_name(t, "macro_export"))
    {
        let tail = &group[at + 1..];
        &tail[..tail.iter().position(|t| t.is_tok(Tok::Comma)).unwrap_or(tail.len())]
    } else {
        return Ok(());
    };
    let ok = match rest {
        [] => true,
        [Tt::Delim(Delim::Paren, group, _)] => {
            matches!(group.as_slice(), [Tt::Tok(t)] if seg_text(t.tok, interner).as_deref() == Some("local_inner_macros"))
        }
        _ => false,
    };
    if ok {
        return Ok(());
    }
    if matches!(rest.first(), Some(Tt::Tok(t)) if t.tok == Tok::Eq) {
        return Err(err("L0524", attr.span, "malformed `macro_export` attribute input", "Write `#[macro_export]` or `#[macro_export(local_inner_macros)]`."));
    }
    if leveled {
        return Ok(());
    }
    Err(err(
        "L0524",
        attr.span,
        "valid forms for the attribute are `macro_export` and `macro_export(local_inner_macros)`",
        "Write `#[macro_export]` or `#[macro_export(local_inner_macros)]` (rustc `invalid_macro_export_arguments`).",
    ))
}

/// A `macro_rules! name <group>` definition found in a tree list.
pub struct DefStart {
    pub name: Sym,
    pub name_span: Span,
    pub group: usize,
    pub end: usize,
    pub span: Span,
    /// The delimiter of the definition body group.
    pub delim: Delim,
}

/// A `macro_rules!` definition whose body is not brace-delimited must
/// end with `;`, like every item macro call (rustc: "macros that
/// expand to items must be delimited with braces or followed by a
/// semicolon").
fn check_def_form(trees: &[Tt], def: &DefStart) -> Result<(), Diag> {
    if def.delim != Delim::Brace && tok_at(trees, def.group + 1).map(|t| t.tok) != Some(Tok::Semi) {
        return Err(err(
            C_CALL,
            def.span,
            "a macro definition not delimited with braces must end with `;`",
            "Write the definition with braces or end it with `;`.",
        ));
    }
    Ok(())
}

/// If a `macro_rules!` definition starts at `trees[i]`, describes it.
pub fn macro_rules_at(trees: &[Tt], i: usize, interner: &Interner) -> Option<DefStart> {
    let head = tok_at(trees, i)?;
    if seg_text(head.tok, interner).as_deref() != Some("macro_rules") {
        return None;
    }
    if tok_at(trees, i + 1).map(|t| t.tok) != Some(Tok::Bang) {
        return None;
    }
    let name_tok = tok_at(trees, i + 2)?;
    let Tok::Ident(name) = name_tok.tok else { return None };
    match trees.get(i + 3) {
        Some(Tt::Delim(d, _, group_span)) => {
            let mut end = i + 4;
            if *d != Delim::Brace && tok_at(trees, end).map(|t| t.tok) == Some(Tok::Semi) {
                end += 1;
            }
            Some(DefStart { name, name_span: name_tok.span, group: i + 3, end, span: head.span.to(*group_span), delim: *d })
        }
        _ => None,
    }
}

/// If a macro call starts at `trees[i]`, describes it (path, head trees,
/// and the index of its argument group).
fn path_call_at(trees: &[Tt], i: usize, interner: &Interner) -> Option<(Vec<Seg>, bool, usize)> {
    let mut j = i;
    let mut leading_colon = false;
    if tok_at(trees, j).map(|t| t.tok) == Some(Tok::PathSep) {
        leading_colon = true;
        j += 1;
    }
    let mut segs: Vec<Seg> = Vec::new();
    loop {
        let seg_tok = tok_at(trees, j)?;
        let sym = seg_sym(seg_tok.tok, interner)?;
        let text = seg_text(seg_tok.tok, interner)?;
        segs.push(Seg { sym, text, span: seg_tok.span });
        j += 1;
        match tok_at(trees, j).map(|t| t.tok) {
            Some(Tok::Bang) => {
                return match trees.get(j + 1) {
                    Some(Tt::Delim(_, _, _)) => Some((segs, leading_colon, j + 1)),
                    _ => None,
                };
            }
            Some(Tok::PathSep) => j += 1,
            _ => return None,
        }
    }
}

/// True when the item at `i` is a function: item qualifiers, then `fn`.
/// A `#[test]` attribute drops only this shape in a non-test build.
fn next_is_fn(trees: &[Tt], mut i: usize) -> bool {
    loop {
        match tok_at(trees, i).map(|t| t.tok) {
            Some(Tok::Pub) => {
                i += 1;
                if matches!(trees.get(i), Some(Tt::Delim(Delim::Paren, _, _))) {
                    i += 1;
                }
            }
            Some(Tok::Const | Tok::Async | Tok::Unsafe | Tok::Extern | Tok::Str(..)) => i += 1,
            Some(Tok::Fn) => return true,
            _ => return false,
        }
    }
}

/// True when trees start an item (`fn`, `pub struct`, an attribute, ...),
/// for the item-position macro rules. A leading item fragment counts,
/// and any other fragment is looked through to its first tokens.
fn starts_item(trees: &[Tt], interner: &Interner) -> bool {
    // Only the head is read: attributes and qualifiers, then the keyword
    // and one tree after it. Copy that much, not the whole tail callers
    // pass (a copy per call made long macro inputs quadratic).
    let head_tree = |t: &Tt| match t {
        Tt::Frag(..) | Tt::Delim(Delim::Bracket | Delim::Paren, _, _) => true,
        Tt::Tok(t) => matches!(t.tok, Tok::Pound | Tok::Bang | Tok::Pub | Tok::Const | Tok::Async | Tok::Unsafe | Tok::Extern),
        Tt::Delim(..) => false,
    };
    let head = trees.iter().take_while(|t| head_tree(t)).count() + 2;
    // Splice leading fragments in place so a vis fragment before the
    // item keyword (as in `$v:vis fn`) still reads as an item start.
    let mut flat: Vec<Tt> = trees[..head.min(trees.len())].to_vec();
    loop {
        match flat.first() {
            Some(Tt::Frag(FragKind::Item, _, _)) => return true,
            Some(Tt::Frag(_, inner, _)) => {
                let inner = inner.clone();
                flat.splice(0..1, inner);
            }
            _ => break,
        }
    }
    let mut i = 0;
    // Skip attributes and item qualifiers to the item keyword. An
    // attribute whose body is a fragment (`#[$m]`) has no readable
    // path for attr_at; skip its two trees directly.
    loop {
        if let Some(attr) = attr_at(&flat, i, interner) {
            i = attr.end;
        } else if tok_at(&flat, i).map(|t| t.tok) == Some(Tok::Pound) && matches!(flat.get(i + 1), Some(Tt::Delim(Delim::Bracket, _, _))) {
            i += 2;
        } else {
            break;
        }
    }
    // A vis fragment after the attributes (`#[must_use] $v:vis fn`)
    // splices in place as a leading one does.
    while let Some(Tt::Frag(kind, inner, _)) = flat.get(i) {
        if *kind == FragKind::Item {
            return true;
        }
        let inner = inner.clone();
        flat.splice(i..i + 1, inner);
    }
    let trees: &[Tt] = &flat;
    loop {
        match tok_at(trees, i).map(|t| t.tok) {
            Some(Tok::Pub) => {
                i += 1;
                if matches!(trees.get(i), Some(Tt::Delim(Delim::Paren, _, _))) {
                    i += 1;
                }
            }
            Some(Tok::Const) => {
                // `const fn` is a qualified fn; `const NAME` is the item.
                if matches!(tok_at(trees, i + 1).map(|t| t.tok), Some(Tok::Ident(_) | Tok::Underscore)) {
                    return true;
                }
                i += 1;
            }
            Some(Tok::Async | Tok::Unsafe | Tok::Extern) => i += 1,
            // The ABI string of `extern "C" fn`.
            Some(Tok::Str(..)) if i > 0 && tok_at(trees, i - 1).map(|t| t.tok) == Some(Tok::Extern) => i += 1,
            Some(Tok::Fn | Tok::Struct | Tok::Enum | Tok::Impl | Tok::Mod | Tok::Trait | Tok::Type | Tok::Static | Tok::Use) => {
                return true;
            }
            Some(t) if seg_text(t, interner).as_deref() == Some("macro_rules") => return true,
            _ => return false,
        }
    }
}

/// The end index of one item starting at `start` in a tree list, for
/// dropping `#[cfg(off)]` items before expansion (ARCH 6.1 step order).
/// None when the item shape is not one this can bound with confidence.
fn item_end(trees: &[Tt], start: usize, interner: &Interner) -> Option<usize> {
    if !starts_item(&trees[start..], interner) && tok_at(trees, start).map(|t| t.tok) != Some(Tok::Static) {
        // `static` and `const` items reach starts_item through the
        // qualifier loop only when directly named; accept them plainly.
        match tok_at(trees, start).map(|t| t.tok) {
            Some(Tok::Const | Tok::Static) => {}
            _ => return None,
        }
    }
    for j in start..trees.len() {
        match &trees[j] {
            Tt::Tok(t) if t.tok == Tok::Semi => return Some(j + 1),
            Tt::Delim(Delim::Brace, _, _) => {
                if tok_at(trees, j + 1).map(|t| t.tok) == Some(Tok::Semi) {
                    return Some(j + 2);
                }
                return Some(j + 1);
            }
            _ => {}
        }
    }
    None
}

/// True when the first call argument in `trees` is written as one string
/// literal (a fragment that holds one counts, as the literal was written
/// by the caller and only forwarded).
fn is_str_lit_arg(trees: &[Tt]) -> bool {
    let end = trees.iter().position(|t| t.is_tok(Tok::Comma)).unwrap_or(trees.len());
    match &trees[..end] {
        [Tt::Tok(t)] => matches!(t.tok, Tok::Str(..)),
        [Tt::Frag(_, inner, _)] => is_str_lit_arg(inner),
        _ => false,
    }
}

/// Stamps the first argument of an expanded format-macro call, when it is
/// one string literal, as macro-produced: the parser then rejects named
/// captures in it, as rustc does for `println!(concat!("{x}", ""))`.
fn mark_format_str(expanded: &mut [Tt], span: Span) {
    fn stamp(t: &mut Token, span: Span) {
        let ctxt = register_expansion(crate::diag::Expansion { macro_def: DefId::PLACEHOLDER, call_span: span, parent: t.span.ctxt });
        mark_no_capture(ctxt);
        t.span.ctxt = ctxt;
    }
    fn first_str(trees: &mut [Tt], span: Span) {
        match trees {
            [Tt::Tok(t)] if matches!(t.tok, Tok::Str(..)) => stamp(t, span),
            [Tt::Frag(_, inner, _)] => first_str(inner, span),
            _ => {}
        }
    }
    let end = expanded.iter().position(|t| t.is_tok(Tok::Comma)).unwrap_or(expanded.len());
    if end == 1 {
        first_str(&mut expanded[..1], span);
    }
}

/// The end index of one non-item node starting at `start`: a statement
/// (let, expression, or block-like), a match arm, or a comma-ended part
/// (struct field, enum variant, parameter). Delimited groups are one
/// tree, so a top-level `;`, `,`, `=>`, or a brace group bounds the
/// node. A brace group ends the node unless an operator, `else`, or
/// `;` follows it. With no terminator the node is the list's tail.
/// Used to drop `#[cfg(off)]` nodes exactly as rustc does. A brace
/// group in a head position does not end the node when what follows
/// it can only continue the head: a second brace group (the real
/// block after a struct literal scrutinee), `=>`, `if`, or `in` (a
/// struct pattern), or any operator. A brace group that starts the
/// node is the node's own block and always ends it.
fn node_end(trees: &[Tt], start: usize) -> Option<usize> {
    if start >= trees.len() {
        return None;
    }
    // A `let` statement ends at its `;` (commas in closure parameters or
    // generic arguments do not end it).
    if tok_at(trees, start).map(|t| t.tok) == Some(Tok::Let) {
        return Some(semi_end(trees, start));
    }
    // A block-like expression statement ends at its last block, as in
    // rustc (no `;` needed, no binary operator, call, or index after it),
    // unless `.` or `?` continues it into a plain expression statement.
    // A head this scan cannot bound gives no end: the caller rejects.
    if block_like_start(trees, start) {
        let e = block_like_end(trees, start)?;
        return Some(match tok_at(trees, e).map(|t| t.tok) {
            Some(Tok::Semi) => e + 1,
            Some(Tok::Dot | Tok::Question) => semi_end(trees, e),
            _ => e,
        });
    }
    let mut j = start;
    while j < trees.len() {
        match &trees[j] {
            Tt::Tok(t) if t.tok == Tok::Semi => return Some(j + 1),
            Tt::Tok(t) if t.tok == Tok::Comma => return Some(j + 1),
            Tt::Tok(t) if t.tok == Tok::FatArrow => {
                // A match arm: a block-like body ends at its last block
                // (`1 => match c { .. }` needs no comma, as in rustc)
                // unless `.` or `?` continues it; any other body runs up
                // to the next comma.
                if block_like_start(trees, j + 1) {
                    let e = block_like_end(trees, j + 1)?;
                    match tok_at(trees, e).map(|t| t.tok) {
                        Some(Tok::Comma) => return Some(e + 1),
                        Some(Tok::Dot | Tok::Question) => {}
                        _ => return Some(e),
                    }
                }
                let mut k = j + 1;
                while k < trees.len() {
                    if matches!(&trees[k], Tt::Tok(t) if t.tok == Tok::Comma) {
                        return Some(k + 1);
                    }
                    k += 1;
                }
                return Some(trees.len());
            }
            Tt::Delim(Delim::Brace, _, _) if j > start && matches!(trees.get(j + 1), Some(Tt::Delim(Delim::Brace, _, _))) => {
                // A struct literal or pattern in a head position; the
                // next brace group is the node's block. Step over the
                // head group and let that group end the node.
                j += 1;
            }
            // A call or index on a struct literal or inner block (`S {}(x)`,
            // `x = { v }[0]`) continues the expression.
            Tt::Delim(Delim::Brace, _, _)
                if j > start && matches!(trees.get(j + 1), Some(Tt::Delim(Delim::Paren | Delim::Bracket, _, _))) =>
            {
                j += 1;
            }
            Tt::Delim(Delim::Brace, _, _) => match tok_at(trees, j + 1).map(|t| t.tok) {
                Some(Tok::Semi) => return Some(j + 2),
                Some(Tok::Comma) => return Some(j + 2),
                Some(Tok::Else) => j += 2,
                // A struct pattern's guard, arm arrow, or `for .. in`.
                Some(Tok::FatArrow | Tok::If | Tok::In) if j > start => j += 1,
                Some(
                    Tok::Dot
                    | Tok::Question
                    | Tok::Plus
                    | Tok::Minus
                    | Tok::Star
                    | Tok::Slash
                    | Tok::Percent
                    | Tok::EqEq
                    | Tok::Ne
                    | Tok::Lt
                    | Tok::Gt
                    | Tok::Le
                    | Tok::Ge
                    | Tok::AndAnd
                    | Tok::OrOr
                    | Tok::Amp
                    | Tok::Pipe
                    | Tok::Caret
                    | Tok::Shl
                    | Tok::As
                    | Tok::PlusEq
                    | Tok::MinusEq
                    | Tok::StarEq
                    | Tok::SlashEq
                    | Tok::PercentEq
                    | Tok::AmpEq
                    | Tok::PipeEq
                    | Tok::CaretEq
                    | Tok::ShlEq
                    | Tok::Shr
                    | Tok::ShrEq
                    | Tok::Eq
                    | Tok::DotDot
                    | Tok::DotDotEq,
                ) => j += 1,
                _ => return Some(j + 1),
            },
            _ => j += 1,
        }
    }
    Some(trees.len())
}

/// True when an attribute run with a `cfg` or `cfg_attr` ends at `after`,
/// on an expression statement whose top level is a binary operation,
/// assignment, cast, or range. rustc rejects that whatever the cfg
/// says, even when the run expands to no attribute at all (E0658). The
/// parser checks the attributes that reach it; a run the expander strips
/// is checked here. The caller passes only runs at a statement start (after `;`, a
/// brace group, or nothing); a node that ends with `;` counts, as no
/// field, variant, or arm does, and so does a block tail (`after_stmt`:
/// not the first part of an enum body).
fn cfg_on_operator_stmt(trees: &[Tt], after: usize, after_stmt: bool, interner: &Interner) -> bool {
    if tok_at(trees, after).map(|t| t.tok) == Some(Tok::Let) || item_end(trees, after, interner).is_some() {
        return false;
    }
    // A block-like statement counts only when `.` or `?` continues it
    // (`{ s }.a + 1;`).
    let (scan, operand) = if block_like_start(trees, after) {
        match block_like_end(trees, after) {
            Some(e) if matches!(tok_at(trees, e).map(|t| t.tok), Some(Tok::Dot | Tok::Question)) => (e, false),
            _ => return false,
        }
    } else {
        (after, true)
    };
    if let Some((_, _, g)) = path_call_at(trees, after, interner)
        && matches!(trees.get(g), Some(Tt::Delim(Delim::Brace, _, _)))
        && !matches!(tok_at(trees, g + 1).map(|t| t.tok), Some(Tok::Dot | Tok::Question))
    {
        return false;
    }
    let Some(end) = node_end(trees, after) else { return false };
    // A top-level `:`, `,`, or `=>` shows a field, parameter, variant, or
    // arm, not an expression statement.
    if trees[scan..end].iter().any(|t| t.is_tok(Tok::Colon) || t.is_tok(Tok::Comma) || t.is_tok(Tok::FatArrow)) {
        return false;
    }
    if end > scan + 1 && trees[end - 1].is_tok(Tok::Semi) {
        return expr_stmt_has_top_op(trees, scan, end - 1, operand);
    }
    // A block's tail (no `;`): `after_stmt` is false where the node may be
    // an enum variant (a field or an arm has a `:` or `=>`, checked above).
    after_stmt && end == trees.len() && end > scan && expr_stmt_has_top_op(trees, scan, end, operand)
}

/// What kind of list `expand_list` walks, for `cfg_run_misplaced`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Group {
    /// The file, a module, or a brace group: items, statements, a block's
    /// tail, fields, variants, arms.
    Brace,
    /// Call or method arguments: `(..)` after an operand.
    Args,
    /// Fn parameters, or the fields of a tuple struct or variant.
    Decl,
    /// A tuple or a parenthesized expression: any other `(..)`.
    Tuple,
    /// An array: `[..]` after no operand.
    Array,
    /// `vec![..]`: elements, or a value and a length.
    Vec,
    /// A type, an index, or the arguments of a builtin macro other than
    /// `vec!`: no outer attribute fits.
    Closed,
    /// A pattern, and the groups inside it: no outer attribute fits.
    Pat,
    /// An expression fragment, or a macro expansion in expression
    /// position: true when an attribute fits where it lands.
    Expr(bool),
}

impl Group {
    /// True for a comma-separated list of expressions or parameters.
    fn is_list(self) -> bool {
        matches!(self, Group::Args | Group::Decl | Group::Tuple | Group::Array | Group::Vec)
    }
}

/// The index after the list element that starts at `s`: after its
/// top-level `,`, or the list end.
fn elem_end(trees: &[Tt], s: usize) -> usize {
    (s..trees.len()).find(|&k| trees[k].is_tok(Tok::Comma)).map_or(trees.len(), |k| k + 1)
}

/// The kind of the delimited group `d` that follows `out` (the trees
/// before it in a list of kind `outer`); `next` is the tree after it.
fn group_kind(d: Delim, out: &[Tt], next: Option<&Tt>, outer: Group, enum_body: bool) -> Group {
    let prev = prev_tree(out);
    let prev_tok = match prev {
        Some(Tt::Tok(t)) => Some(t.tok),
        _ => None,
    };
    // A pattern: after `let` or `for` (the scan stops at the `=` or `in`
    // that ends one), before `=>` or `in`, or inside another pattern.
    let after_let = out
        .iter()
        .rev()
        .take_while(|t| !matches!(t, Tt::Delim(Delim::Brace, _, _)) && ![Tok::Semi, Tok::Eq, Tok::In, Tok::FatArrow].iter().any(|&k| t.is_tok(k)))
        .any(|t| t.is_tok(Tok::Let) || t.is_tok(Tok::For));
    let pattern = after_let || outer == Group::Pat || matches!(next, Some(Tt::Tok(t)) if matches!(t.tok, Tok::FatArrow | Tok::In));
    match d {
        Delim::Brace => Group::Brace,
        Delim::Paren if enum_body || decl_params(out) => Group::Decl,
        _ if pattern => Group::Pat,
        Delim::Paren if prev_tok == Some(Tok::Arrow) => Group::Closed,
        Delim::Paren if ends_operand(out) => Group::Args,
        Delim::Bracket if ends_operand(out) => Group::Closed,
        Delim::Paren => Group::Tuple,
        Delim::Bracket => Group::Array,
    }
}

/// The last tree of `out`, looking inside transparent fragments (a
/// forwarded `tt`, ident, or lifetime).
fn prev_tree(out: &[Tt]) -> Option<&Tt> {
    for t in out.iter().rev() {
        match t {
            Tt::Frag(k, inner, _) if k.transparent() => {
                if let Some(t) = prev_tree(inner) {
                    return Some(t);
                }
            }
            _ => return Some(t),
        }
    }
    None
}

/// True when `out` ends with a complete operand, so a `(` or `[` after
/// it is a call or an index: a name, a literal, a group other than a
/// block, `?`, an expression fragment, or the `>` of a turbofish.
fn ends_operand(out: &[Tt]) -> bool {
    match prev_tree(out) {
        Some(Tt::Delim(d, _, _)) => *d != Delim::Brace,
        Some(Tt::Frag(k, _, _)) => matches!(k, FragKind::Expr | FragKind::Expr2021 | FragKind::Path | FragKind::Literal | FragKind::Ty),
        Some(Tt::Tok(t)) => match t.tok {
            Tok::Ident(_)
            | Tok::Int(..)
            | Tok::Float(_)
            | Tok::Str(..)
            | Tok::ByteStr(_)
            | Tok::ByteChar(_)
            | Tok::Char(..)
            | Tok::True
            | Tok::False
            | Tok::SelfLower
            | Tok::SelfUpper
            | Tok::Super
            | Tok::Crate
            | Tok::Await
            | Tok::Question => true,
            Tok::Gt | Tok::Shr => (0..out.len()).any(|k| {
                out[k].is_tok(Tok::PathSep) && out.get(k + 1).is_some_and(|t| t.is_tok(Tok::Lt)) && generics_end(out, k + 1, out.len()) == Some(out.len())
            }),
            _ => false,
        },
        None => false,
    }
}

/// True when `out` ends with the head of a fn or tuple struct whose
/// parameter or field list comes next: `fn name`, `struct Name`, either
/// with generic parameters.
fn decl_params(out: &[Tt]) -> bool {
    let mut e = out.len();
    if out.last().is_some_and(|t| t.is_tok(Tok::Gt) || t.is_tok(Tok::Shr)) {
        // Back to the `<` that opens the generic parameters.
        let mut depth = 0i32;
        let open = (0..e).rev().find(|&k| {
            match tok_at(out, k).map(|t| t.tok) {
                Some(Tok::Gt) => depth += 1,
                Some(Tok::Shr) => depth += 2,
                Some(Tok::Lt) => depth -= 1,
                Some(Tok::Shl) => depth -= 2,
                _ => {}
            }
            depth <= 0
        });
        let Some(open) = open else { return false };
        e = open;
    }
    e >= 2 && matches!(out[e - 1], Tt::Tok(Token { tok: Tok::Ident(_), .. })) && matches!(tok_at(out, e - 2).map(|t| t.tok), Some(Tok::Fn | Tok::Struct))
}

/// True when the top level of `trees[s..]` has `tok`.
fn has_top(trees: &[Tt], s: usize, tok: Tok) -> bool {
    trees[s.min(trees.len())..].iter().any(|t| t.is_tok(tok))
}

/// True when the list element (call argument, array or tuple element)
/// that starts at `s` and runs to the next top-level `,` has a binary
/// operator, cast, range, or assignment at its top level. An element
/// with a top-level `:` is a parameter or field, not an expression.
fn element_has_top_op(trees: &[Tt], s: usize) -> bool {
    let e = (s..trees.len()).find(|&k| trees[k].is_tok(Tok::Comma)).unwrap_or(trees.len());
    !trees[s.min(e)..e].iter().any(|t| t.is_tok(Tok::Colon)) && expr_stmt_has_top_op(trees, s, e, true)
}

/// `element_has_top_op` for a `vec!` part, which also ends at a
/// top-level `;` (`vec![value; length]`).
fn element_has_top_op_semi(trees: &[Tt], s: usize) -> bool {
    let e = (s..trees.len()).find(|&k| trees[k].is_tok(Tok::Comma) || trees[k].is_tok(Tok::Semi)).unwrap_or(trees.len());
    expr_stmt_has_top_op(trees, s, e, true)
}

/// True when a `cfg` or `cfg_attr` run that ends at `after` sits where
/// rustc takes no outer attribute, so rustc rejects it whatever the cfg
/// says (E0658). `out` holds the trees before the run in a list of kind
/// `group` (not an item list). rustc takes outer attributes on items,
/// statements, a block's tail, fields, variants, arms, and parameters,
/// and on the elements of call arguments, arrays, and tuples. On a
/// statement or element whose top level is a binary operator, cast,
/// range, or assignment, the attribute goes to the left operand: an
/// error too.
fn cfg_run_misplaced(out: &[Tt], trees: &[Tt], after: usize, group: Group, enum_body: bool, interner: &Interner) -> bool {
    if in_where_clause(out) {
        return true;
    }
    let prev = prev_tree(out);
    let prev_tok = match prev {
        Some(Tt::Tok(t)) => Some(t.tok),
        _ => None,
    };
    let stmt_start = match prev {
        None => true,
        Some(Tt::Tok(t)) => t.tok == Tok::Semi,
        Some(Tt::Delim(d, _, _)) => *d == Delim::Brace,
        Some(Tt::Frag(k, _, _)) => matches!(k, FragKind::Stmt | FragKind::Item | FragKind::Block),
    };
    let first_or_comma = prev.is_none() || prev_tok == Some(Tok::Comma);
    match group {
        // A run with nothing before it in a brace list may sit on a
        // block's only tail, except in an enum body.
        Group::Brace if stmt_start => cfg_on_operator_stmt(trees, after, prev.is_some() || !enum_body, interner),
        Group::Brace | Group::Decl if first_or_comma => false,
        Group::Expr(ok) if prev.is_none() => !ok || element_has_top_op(trees, after),
        // `(#[a] x)` is a parenthesized expression; `[#[a] x; n]` a repeat.
        Group::Tuple if prev.is_none() && !has_top(trees, after, Tok::Comma) => true,
        // `vec![#[a] x; n]`: from_elem's arguments (a cfg that is off
        // drops one, which the drop path rejects).
        Group::Vec if first_or_comma || prev_tok == Some(Tok::Semi) => element_has_top_op_semi(trees, after),
        Group::Array if has_top(trees, after, Tok::Semi) => true,
        // A later closure parameter: `g(|a, #[a] b| ..)`.
        Group::Args | Group::Tuple | Group::Array | Group::Vec if prev_tok == Some(Tok::Comma) && in_closure_params(out) => false,
        Group::Args | Group::Tuple | Group::Array | Group::Vec if first_or_comma => element_has_top_op(trees, after),
        // Closure parameters: `|#[a] x|` opens them, `x | #[a] y` does not.
        _ if prev_tok == Some(Tok::Pipe) => ends_operand(&out[..out.len() - 1]),
        // Generic parameters: `fn f<#[a] T>`, `impl<#[a] T>`.
        _ if prev_tok == Some(Tok::Lt) => !generics_open(&out[..out.len() - 1], interner),
        _ => true,
    }
}

/// True when `out` ends inside a where clause, which takes no attribute
/// (rustc E0658).
fn in_where_clause(out: &[Tt]) -> bool {
    out.iter().rev().take_while(|t| !t.is_tok(Tok::Semi) && !matches!(t, Tt::Delim(Delim::Brace, _, _))).any(|t| t.is_tok(Tok::Where))
}

/// True when `out` ends inside closure parameters: its last top-level
/// `|` opens them (no operand before it).
fn in_closure_params(out: &[Tt]) -> bool {
    let Some(k) = (0..out.len()).rev().find(|&k| out[k].is_tok(Tok::Pipe) || out[k].is_tok(Tok::OrOr)) else { return false };
    out[k].is_tok(Tok::Pipe) && !ends_operand(&out[..k])
}

/// True when a `<` after `out` opens generic parameters: after `impl` or
/// `for`, or after the name of a fn, struct, enum, union, trait, or type.
fn generics_open(out: &[Tt], interner: &Interner) -> bool {
    let n = out.len();
    match tok_at(out, n.wrapping_sub(1)).map(|t| t.tok) {
        Some(Tok::Impl | Tok::For) => true,
        Some(Tok::Ident(_)) => match tok_at(out, n.wrapping_sub(2)).map(|t| t.tok) {
            Some(Tok::Fn | Tok::Struct | Tok::Enum | Tok::Trait | Tok::Type) => true,
            // `union` is a contextual keyword.
            Some(t @ Tok::Ident(_)) => seg_text(t, interner).as_deref() == Some("union"),
            _ => false,
        },
        _ => false,
    }
}

/// The end of a dropped macro call node whose group is at `g` (the
/// path starts at `start`). A brace call is a whole statement or item,
/// as in rustc, unless `.` or `?` continues it or `=>` or `,` shows it
/// is a pattern or operand; a `;` after the group joins the node. A
/// paren or bracket call is an expression that may go on (`m!() - x`,
/// `m!().f()`), bounded as any other node.
fn macro_node_end(trees: &[Tt], start: usize, g: usize) -> Option<usize> {
    let next = tok_at(trees, g + 1).map(|t| t.tok);
    if next == Some(Tok::Semi) {
        return Some(g + 2);
    }
    let brace = matches!(trees.get(g), Some(Tt::Delim(Delim::Brace, _, _)));
    if brace && !matches!(next, Some(Tok::Dot | Tok::Question | Tok::FatArrow | Tok::Comma)) {
        return Some(g + 1);
    }
    node_end(trees, start)
}

/// The index after the first top-level `;` at or after `j`, or the list
/// end (a tail expression).
fn semi_end(trees: &[Tt], j: usize) -> usize {
    (j..trees.len()).find(|&k| trees[k].is_tok(Tok::Semi)).map_or(trees.len(), |k| k + 1)
}

/// True when a block-like expression starts at `s`: `if`, `match`,
/// `loop`, `while`, `for`, a block, `unsafe {`, `const {`, or a label
/// on one of these (rustc's `expr_requires_semi_to_be_stmt` is false).
fn block_like_start(trees: &[Tt], s: usize) -> bool {
    let brace_at = |k: usize| matches!(trees.get(k), Some(Tt::Delim(Delim::Brace, _, _)));
    match trees.get(s) {
        Some(Tt::Delim(Delim::Brace, _, _) | Tt::Frag(FragKind::Block, _, _)) => true,
        Some(Tt::Tok(t)) => match t.tok {
            Tok::If | Tok::Match | Tok::Loop | Tok::While | Tok::For => true,
            Tok::Unsafe | Tok::Const => brace_at(s + 1),
            Tok::Lifetime(_) => tok_at(trees, s + 1).map(|t| t.tok) == Some(Tok::Colon) && block_like_start(trees, s + 2),
            _ => false,
        },
        _ => false,
    }
}

/// The index after the block-like expression at `s` (see
/// `block_like_start`): after its block, or after the last block of an
/// `if .. else if .. else` chain. None when the head has a form this
/// token scan does not bound (a closure, `async`, a stray `;`).
fn block_like_end(trees: &[Tt], s: usize) -> Option<usize> {
    let brace_at = |k: usize| matches!(trees.get(k), Some(Tt::Delim(Delim::Brace, _, _)));
    match trees.get(s)? {
        Tt::Delim(Delim::Brace, _, _) | Tt::Frag(FragKind::Block, _, _) => return Some(s + 1),
        Tt::Tok(_) => {}
        _ => return None,
    }
    match tok_at(trees, s)?.tok {
        Tok::Unsafe | Tok::Const | Tok::Loop => brace_at(s + 1).then_some(s + 2),
        Tok::Lifetime(_) if tok_at(trees, s + 1).map(|t| t.tok) == Some(Tok::Colon) => block_like_end(trees, s + 2),
        Tok::Match | Tok::While => Some(body_brace(trees, s + 1)? + 1),
        Tok::For => {
            // The pattern runs to the first top-level `in`.
            let in_at = (s + 1..trees.len()).find(|&k| trees[k].is_tok(Tok::In))?;
            Some(body_brace(trees, in_at + 1)? + 1)
        }
        Tok::If => {
            let e = body_brace(trees, s + 1)? + 1;
            if tok_at(trees, e).map(|t| t.tok) != Some(Tok::Else) {
                return Some(e);
            }
            if tok_at(trees, e + 1).map(|t| t.tok) == Some(Tok::If) {
                return block_like_end(trees, e + 1);
            }
            brace_at(e + 1).then_some(e + 2)
        }
        _ => None,
    }
}

/// The index of the body block of an `if`, `while`, `match`, or `for`
/// whose head expression starts at `j`. The head is an expression with
/// no struct literal: a brace group in operand position is a block
/// expression, one after a macro path is the macro's group, an inner
/// block-like expression is skipped whole, and the first other brace
/// group is the body. `let` patterns run to their `=`. None for a head
/// this scan does not bound: a closure, `async`, or a `;`, `,`, `=>`.
fn body_brace(trees: &[Tt], mut j: usize) -> Option<usize> {
    let mut operand = true;
    while j < trees.len() {
        match &trees[j] {
            Tt::Delim(Delim::Brace, _, _) if !operand => return Some(j),
            Tt::Delim(..) | Tt::Frag(..) => {
                operand = false;
                j += 1;
            }
            Tt::Tok(t) => match t.tok {
                Tok::Let => {
                    j = (j + 1..trees.len()).find(|&k| trees[k].is_tok(Tok::Eq))? + 1;
                    operand = true;
                }
                Tok::If | Tok::Match | Tok::Loop | Tok::While | Tok::For | Tok::Unsafe | Tok::Const | Tok::Lifetime(_)
                    if operand && block_like_start(trees, j) =>
                {
                    j = block_like_end(trees, j)?;
                    operand = false;
                }
                Tok::Semi | Tok::Comma | Tok::FatArrow | Tok::Async | Tok::Move => return None,
                Tok::Pipe | Tok::OrOr if operand => return None,
                // A macro call: path, `!`, and its group (any delimiter).
                Tok::Bang if !operand && matches!(trees.get(j + 1), Some(Tt::Delim(..))) => j += 2,
                // Turbofish generic arguments: skip to the matching `>`.
                Tok::PathSep if tok_at(trees, j + 1).map(|t| t.tok) == Some(Tok::Lt) => {
                    j = generics_end(trees, j + 1, trees.len())?;
                    operand = false;
                }
                Tok::Ident(_)
                | Tok::Reserved(_)
                | Tok::Int(..)
                | Tok::Float(_)
                | Tok::Str(..)
                | Tok::ByteStr(_)
                | Tok::ByteChar(_)
                | Tok::Char(..)
                | Tok::Lifetime(_)
                | Tok::True
                | Tok::False
                | Tok::SelfLower
                | Tok::SelfUpper
                | Tok::Crate
                | Tok::Super
                | Tok::Await
                | Tok::Question
                | Tok::Underscore => {
                    operand = false;
                    j += 1;
                }
                // `.`, `::`, and every operator or prefix keyword expects
                // more of the expression before a body can start.
                _ => {
                    if t.tok != Tok::PathSep {
                        operand = t.tok != Tok::Dot;
                    }
                    j += 1;
                }
            },
        }
    }
    None
}

/// The index after the `>` that closes the generic argument list whose
/// `<` is at `lt`, scanning below `e`; None when it does not close.
fn generics_end(trees: &[Tt], lt: usize, e: usize) -> Option<usize> {
    let mut depth = 0i32;
    for j in lt..e {
        match tok_at(trees, j).map(|t| t.tok) {
            Some(Tok::Lt) => depth += 1,
            Some(Tok::Shl) => depth += 2,
            Some(Tok::Gt) => depth -= 1,
            Some(Tok::Shr) => depth -= 2,
            Some(Tok::Semi | Tok::FatArrow) => return None,
            _ => {}
        }
        if depth <= 0 {
            return Some(j + 1);
        }
    }
    None
}

/// True when the expression statement in `trees[s..e]` (no attributes)
/// has a binary operator, assignment, cast, or range at its top level.
/// `operand` is false when the scan starts after a first operand (the
/// `.` or `?` that continues a block-like expression). rustc puts a statement's outer attributes on the
/// leftmost operand then, which is an error for `cfg` as for any other
/// attribute (E0658, and "removing an expression is not supported in
/// this position" when the cfg is off). A prefix `return`, `break`, or
/// closure takes the whole rest, so the attribute covers it all.
fn expr_stmt_has_top_op(trees: &[Tt], s: usize, e: usize, mut operand: bool) -> bool {
    let mut j = s;
    while j < e {
        match &trees[j] {
            Tt::Delim(..) | Tt::Frag(..) => operand = false,
            Tt::Tok(t) => match t.tok {
                Tok::Return | Tok::Break | Tok::Pipe | Tok::OrOr | Tok::Move | Tok::Async | Tok::Static if operand => return false,
                Tok::If | Tok::Match | Tok::Loop | Tok::While | Tok::For | Tok::Unsafe | Tok::Const | Tok::Lifetime(_)
                    if operand && block_like_start(trees, j) =>
                {
                    let Some(end) = block_like_end(trees, j) else { return true };
                    j = end;
                    operand = false;
                    continue;
                }
                Tok::Minus | Tok::Star | Tok::Amp | Tok::AndAnd | Tok::Bang | Tok::Mut if operand => {}
                // A qualified path `<T as Tr>::f`, or turbofish arguments.
                Tok::Lt | Tok::PathSep
                    if (operand && t.tok == Tok::Lt) || (t.tok == Tok::PathSep && tok_at(trees, j + 1).map(|t| t.tok) == Some(Tok::Lt)) =>
                {
                    let lt = if t.tok == Tok::Lt { j } else { j + 1 };
                    let Some(end) = generics_end(trees, lt, e) else { return true };
                    j = end;
                    operand = false;
                    continue;
                }
                Tok::DotDot | Tok::DotDotEq => return true,
                Tok::Bang if matches!(trees.get(j + 1), Some(Tt::Delim(..))) => j += 1,
                Tok::Semi => return false,
                Tok::As
                | Tok::Eq
                | Tok::EqEq
                | Tok::Ne
                | Tok::Lt
                | Tok::Le
                | Tok::Gt
                | Tok::Ge
                | Tok::Plus
                | Tok::Minus
                | Tok::Star
                | Tok::Slash
                | Tok::Percent
                | Tok::PlusEq
                | Tok::MinusEq
                | Tok::StarEq
                | Tok::SlashEq
                | Tok::PercentEq
                | Tok::AmpEq
                | Tok::PipeEq
                | Tok::CaretEq
                | Tok::ShlEq
                | Tok::ShrEq
                | Tok::Amp
                | Tok::AndAnd
                | Tok::Pipe
                | Tok::OrOr
                | Tok::Caret
                | Tok::Shl
                | Tok::Shr => return true,
                Tok::Dot | Tok::PathSep => {}
                _ => operand = false,
            },
        }
        j += 1;
    }
    false
}

/// Takes `trees[i]` out by value, leaving a placeholder behind.
fn take(trees: &mut [Tt], i: usize) -> Tt {
    std::mem::replace(&mut trees[i], Tt::Tok(Token { tok: Tok::Eof, span: Span::default() }))
}

impl<'a> Expander<'a> {
    /// Errors when a call to `name()!` at `depth`, whose own expansion
    /// reaches `extra` levels deeper (see `builtin::rustc_depth`), would
    /// pass the recursion limit. Past `RECURSION_CAP` the limit is
    /// lust's, not the crate's, and the message says so.
    fn check_depth(&self, depth: u32, extra: u32, span: Span, name: impl FnOnce() -> String) -> Result<(), Diag> {
        if depth + extra < self.recursion_limit {
            return Ok(());
        }
        let name = name();
        if self.limit_capped {
            return Err(err(
                C_CAP,
                span,
                format!("expansion depth reached lust's limit of {RECURSION_CAP} while expanding `{name}!`"),
                "Lust expands macros at most 2048 levels deep, whatever the crate's recursion limit.",
            ));
        }
        Err(err(C_CAP, span, format!("recursion limit reached while expanding `{name}!`"), "Give the macro a base case it can reach."))
    }

    /// Expands one tree list, outermost first (ARCH 6.1). `depth` is the
    /// expansion nesting depth of this list; `item_list` marks the file
    /// root and module bodies, where item-position rules apply;
    /// `stmt_list` marks a block body, where a brace-delimited macro
    /// call at a statement boundary is a whole statement; `nest`
    /// bounds delimiter recursion so pathological input cannot overflow.
    /// Every recursion of expansion passes through here. When the
    /// current stack segment is used up, the list expands on a new
    /// thread with a fresh stack (rustc grows its stack the same way),
    /// so deep expansion cannot overflow the native stack, whatever
    /// thread it started on.
    pub fn expand_list(&mut self, trees: Vec<Tt>, depth: u32, item_list: bool, stmt_list: bool, nest: u32) -> Result<Vec<Tt>, Diag> {
        let used = self.stack_base.abs_diff(stack_addr());
        if used < self.stack_room {
            return self.expand_list_here(trees, depth, item_list, stmt_list, nest);
        }
        let span = trees.first().map_or(Span::default(), Tt::span);
        if self.stack_below + used > STACK_TOTAL {
            return Err(err(C_CAP, span, "macro expansion nests too deeply", "Simplify the macros or the nesting in this file."));
        }
        let saved = (self.stack_base, self.stack_room, self.stack_below);
        self.stack_below += used;
        let joined = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .name("lust-expand".into())
                .stack_size(STACK_HOP)
                .spawn_scoped(scope, || {
                    self.stack_base = stack_addr();
                    self.stack_room = STACK_HOP_ROOM;
                    self.expand_list_here(trees, depth, item_list, stmt_list, nest)
                })
                .map(|thread| thread.join())
        });
        (self.stack_base, self.stack_room, self.stack_below) = saved;
        match joined {
            Ok(Ok(result)) => result,
            Ok(Err(panic)) => std::panic::resume_unwind(panic),
            Err(_) => Err(err(C_CAP, span, "macro expansion nests too deeply for this thread's stack", "Simplify the macros or the nesting in this file.")),
        }
    }

    /// `expand_list` on the current stack segment.
    fn expand_list_here(&mut self, mut trees: Vec<Tt>, depth: u32, item_list: bool, stmt_list: bool, nest: u32) -> Result<Vec<Tt>, Diag> {
        if nest > 1000 {
            return Ok(trees);
        }
        let mut out: Vec<Tt> = Vec::with_capacity(trees.len());
        let mut pending_macro_use = false;
        let mut i = 0;
        while i < trees.len() {
            // An attribute run: cfg stripping first (ARCH 6.1 step 1),
            // then macro definition attributes, then plain passthrough.
            if let Some(first) = attr_at(&trees, i, self.ctx.interner) {
                i = self.attr_run(&mut trees, i, first, &mut pending_macro_use, &mut out, item_list, depth)?;
                continue;
            }
            // A macro definition never reaches the parser.
            if let Some(def) = macro_rules_at(&trees, i, self.ctx.interner) {
                self.define_macro(&trees, &def, false, !item_list)?;
                i = def.end;
                pending_macro_use = false;
                continue;
            }
            // An inline module: its body is its own macro scope and path.
            if tok_at(&trees, i).map(|t| t.tok) == Some(Tok::Mod)
                && matches!(tok_at(&trees, i + 1).map(|t| t.tok), Some(Tok::Ident(_)))
                && matches!(trees.get(i + 2), Some(Tt::Delim(Delim::Brace, _, _)))
            {
                let (name_sym, name_ok) = match tok_at(&trees, i + 1) {
                    Some(t) => (seg_sym(t.tok, self.ctx.interner), true),
                    None => (None, false),
                };
                let _ = name_ok;
                let group = take(&mut trees, i + 2);
                let Tt::Delim(_, inner, gspan) = group else { unreachable!() };
                let textual_len = self.textual.len();
                // Names `use` and globs bind in the enclosing module or
                // block are not in scope in a nested module; textual
                // definitions are.
                let imports = std::mem::take(&mut self.imports);
                let globs = std::mem::take(&mut self.glob_macros);
                let glob_tys = std::mem::take(&mut self.glob_type_names);
                let builtins = std::mem::take(&mut self.builtin_imports);
                if let Some(sym) = name_sym {
                    self.module.push(sym);
                }
                self.scope_depth += 1;
                let module_depth = std::mem::replace(&mut self.module_depth, self.scope_depth);
                let scope_calls = std::mem::replace(&mut self.scope_calls, self.plain_calls.len());
                let expanded = self.expand_list(inner, depth, true, false, nest + 1);
                self.scope_calls = scope_calls;
                self.module_depth = module_depth;
                self.scope_depth -= 1;
                if name_sym.is_some() {
                    self.module.pop();
                }
                (self.imports, self.glob_macros, self.glob_type_names, self.builtin_imports) = (imports, globs, glob_tys, builtins);
                let inner = expanded?;
                let added: Vec<(Sym, u32, u32)> = self.textual[textual_len..].to_vec();
                self.textual.truncate(textual_len);
                if pending_macro_use {
                    // The definitions join this scope from here on,
                    // at this depth (see `plain_macro`).
                    let depth = self.scope_depth;
                    self.textual.extend(added.into_iter().map(|(n, i, _)| (n, i, depth)));
                }
                pending_macro_use = false;
                out.push(take(&mut trees, i));
                out.push(take(&mut trees, i + 1));
                out.push(Tt::Delim(Delim::Brace, inner, gspan));
                i += 3;
                continue;
            }
            // An out-of-line module: its file sees this textual scope, but
            // the worklist passes it written definitions only.
            if item_list
                && tok_at(&trees, i).map(|t| t.tok) == Some(Tok::Mod)
                && matches!(tok_at(&trees, i + 1).map(|t| t.tok), Some(Tok::Ident(_)))
                && tok_at(&trees, i + 2).map(|t| t.tok) == Some(Tok::Semi)
                && let Some(span) = self.expanded_textual_span()
            {
                return Err(err(
                    C_UNSUPPORTED,
                    span,
                    "a `macro_rules!` that a macro expansion defines is in scope of an out-of-line module (`mod name;`)",
                    "Define the macro with a written `macro_rules!`, or move the module declaration above the macro call.",
                ));
            }
            // A `use` item: register what it imports, emit it unchanged.
            if let Some(end) = self.use_item_at(&trees, i, item_list) {
                for k in i..end {
                    let tree = take(&mut trees, k);
                    out.push(tree);
                }
                i = end;
                pending_macro_use = false;
                continue;
            }
            // A parser-owned macro call (println! and kin): emit it as
            // written, with its argument trees expanded. This is a
            // structural case, not an expansion step: re-walking the
            // same call as new output would never finish.
            if let Some((segs, leading_colon, group_idx)) = path_call_at(&trees, i, self.ctx.interner)
                && self.lookup_macro(&segs, leading_colon).is_none()
                && !(segs.len() == 1 && !leading_colon && self.plain_call_ambiguous(&segs[0]))
                && self.builtin_call_path(&segs, leading_colon)
                && builtin::is_passthrough(segs.last().map_or("", |s| &s.text))
            {
                let (delim, inner, group_span) = match &trees[group_idx] {
                    Tt::Delim(d, inner, span) => (*d, inner.clone(), *span),
                    _ => unreachable!(),
                };
                if let [seg] = &segs[..]
                    && !leading_colon
                {
                    self.note_plain_call(seg, seg.span.to(group_span));
                }
                // The parser owns only the plain `name!` form, so a
                // path-qualified call (`std::println!`) keeps just its
                // last segment and the bang. The name spans the whole
                // path: rustc reports a panic at the path's start.
                let start = tok_at(&trees, i).map(|t| t.span);
                let mut name_tt = take(&mut trees, group_idx - 2);
                if let (Tt::Tok(t), Some(start)) = (&mut name_tt, start)
                    && (start.file, start.ctxt) == (t.span.file, t.span.ctxt)
                {
                    t.span = start.to(t.span);
                }
                out.push(name_tt);
                out.push(take(&mut trees, group_idx - 1));
                let fmt_name = segs.last().map_or("", |s| s.text.as_str());
                let written_lit = is_str_lit_arg(&inner);
                // A passthrough builtin counts depth as rustc's expansion
                // of it does (see `builtin::rustc_depth`).
                let (extra, args) = builtin::rustc_depth(fmt_name, &inner);
                let call_span = segs.first().map_or(group_span, |s| s.span.to(group_span));
                self.check_depth(depth, extra, call_span, || fmt_name.to_string())?;
                let msg = if fmt_name == "assert" { builtin::assert_message(self, &inner, call_span)? } else { Vec::new() };
                // `vec!` arguments are array elements or from_elem's
                // arguments; the other builtins take no outer attribute.
                let group = if fmt_name == "vec" { Group::Vec } else { Group::Closed };
                let outer_group = std::mem::replace(&mut self.group, group);
                let outer_expn = self.enter_expn();
                let expanded_inner = self.expand_list(inner, depth + args, false, false, nest + 1);
                self.expn = outer_expn;
                self.group = outer_group;
                let mut expanded_inner = expanded_inner?;
                expanded_inner.extend(msg);
                if !written_lit && matches!(fmt_name, "println" | "print" | "eprintln" | "eprint" | "format" | "panic") {
                    mark_format_str(&mut expanded_inner, group_span);
                }
                out.push(Tt::Delim(delim, expanded_inner, group_span));
                i = group_idx + 1;
                pending_macro_use = false;
                continue;
            }
            // A macro call.
            if let Some((segs, leading_colon, group_idx)) = path_call_at(&trees, i, self.ctx.interner) {
                let (delim, inner, group_span) = match &trees[group_idx] {
                    Tt::Delim(d, inner, span) => (*d, inner.clone(), *span),
                    _ => unreachable!(),
                };
                let head: Vec<Tt> = trees[i..group_idx].to_vec();
                let span = segs.first().map_or(group_span, |s| s.span.to(group_span));
                let call = Call { segs, leading_colon, head, delim, inner, group_span, span };
                let mut next = group_idx + 1;
                // The call's output, and what walking it expands, is a new
                // expansion (`expanded_shadows`).
                let outer_expn = self.enter_expn();
                let outer_items = std::mem::replace(&mut self.items_call, item_list);
                let expanded = self.expand_call(&call, depth);
                self.items_call = outer_items;
                // An expansion in expression position takes an outer
                // attribute where the call could have one.
                let at_stmt = item_list
                    || (self.group == Group::Brace
                        && (out.is_empty()
                            || matches!(out.last(), Some(Tt::Tok(t)) if t.tok == Tok::Semi)
                            || matches!(out.last(), Some(Tt::Delim(Delim::Brace, _, _)))));
                let group = if at_stmt {
                    self.group
                } else {
                    Group::Expr(!cfg_run_misplaced(&out, &trees, i, self.group, self.enum_body, self.ctx.interner))
                };
                // Whether a cfg that is off dropped a node while this
                // expansion ran (in it or in a call inside it): an empty
                // result is then a removed list element (below).
                let outer_dropped = std::mem::replace(&mut self.cfg_dropped, false);
                let outer_group = std::mem::replace(&mut self.group, group);
                let expanded = expanded.and_then(|e| self.expand_list(e, depth + 1, item_list, stmt_list, nest));
                self.group = outer_group;
                self.expn = outer_expn;
                let cfg_headed = self.cfg_dropped;
                self.cfg_dropped |= outer_dropped;
                let mut expanded = expanded?;
                // A list element the call is the whole of (`[a, m!(..), b]`)
                // whose expansion a cfg removed goes with its comma, as a
                // written `#[cfg(off)]` element does.
                if expanded.is_empty()
                    && cfg_headed
                    && self.group.is_list()
                    && (out.is_empty() || matches!(out.last(), Some(Tt::Tok(t)) if t.tok == Tok::Comma))
                    && tok_at(&trees, next).map(|t| t.tok) == Some(Tok::Comma)
                {
                    next += 1;
                }
                let begins_item = starts_item(&expanded, self.ctx.interner);
                let next_is_semi = tok_at(&trees, next).map(|t| t.tok) == Some(Tok::Semi);
                if item_list && !expanded.is_empty() && begins_item && call.delim != Delim::Brace && !next_is_semi {
                    return Err(err(
                        C_CALL,
                        call.span,
                        "a macro that expands to items needs `{ }` or a trailing `;`",
                        "Write the call with braces or end it with `;`.",
                    ));
                }
                // The call's own `;` is consumed with an empty or item
                // expansion only at a statement or item boundary. In
                // expression position the empty expansion is an error,
                // and dropping the `;` would let the flat stream read
                // the next statement as the expression.
                // A matched item, stmt, or block fragment ends a statement
                // too, as `stmt_start` reads it: `m!({ $i:item });` then
                // an empty `n!(..);` in an impl body.
                let stmt_boundary = item_list
                    || out.is_empty()
                    || matches!(out.last(), Some(Tt::Tok(t)) if t.tok == Tok::Semi)
                    || matches!(out.last(), Some(Tt::Delim(Delim::Brace, _, _)))
                    || matches!(out.last(), Some(Tt::Frag(FragKind::Stmt | FragKind::Item | FragKind::Block, _, _)));
                if next_is_semi && begins_item {
                    next += 1;
                } else if next_is_semi && expanded.is_empty() && stmt_boundary {
                    next += 1;
                }
                // A statement-position expansion whose last statement
                // is a `let` without its own `;` is incomplete: the
                // call's `;` belongs to the macro statement, it does
                // not finish the let.
                if !item_list && stmt_boundary && ends_with_unfinished_let(&expanded) {
                    return Err(err(
                        C_CALL,
                        call.span,
                        "this macro expansion ends with an incomplete `let` statement",
                        "End the `let` with `;` inside the macro expansion.",
                    ));
                }
                // A `{}` call at a statement boundary is a statement of its
                // own in rustc (see `brace_stmt` below), never an operand.
                let brace_call_stmt = stmt_list && !item_list && stmt_boundary && call.delim == Delim::Brace && !begins_item;
                // A `m!(..);` call at a statement boundary is a statement
                // macro: rustc parses its expansion as statements, so it
                // is spliced as written (`#[a] if c {} {}` is two).
                let semi_stmt = stmt_list && !item_list && stmt_boundary && next_is_semi;
                if !brace_call_stmt
                    && !semi_stmt
                    && should_wrap(&expanded, &out, tok_at(&trees, next).map(|t| t.tok), trees.get(next), self.ctx.interner)
                {
                    expanded = vec![Tt::Delim(Delim::Paren, expanded, call.span)];
                }
                // A `()` or `[]` call in statement position, or as a match
                // arm's body, is an expression in rustc, so an operator
                // after it continues it: `matches!(x, 1) || y`. A
                // block-like expansion (`match x { .. }`) would end the
                // statement or the arm in the flat stream, so it gets
                // parens.
                let arm_body = matches!(out.last(), Some(Tt::Tok(t)) if t.tok == Tok::FatArrow);
                if (stmt_list && !item_list && stmt_boundary || arm_body)
                    && call.delim != Delim::Brace
                    && starts_block_like(&expanded)
                    && continues_expr(tok_at(&trees, next).map(|t| t.tok))
                {
                    expanded = vec![Tt::Delim(Delim::Paren, expanded, call.span)];
                }
                // A brace-delimited call in statement position is a
                // whole statement in rustc: `m!{} - 1;` is the call,
                // then a separate `-1` statement. The flat stream
                // would glue the operator onto the expansion's last
                // expression, so close the statement where rustc
                // does. Only statement lists qualify: in expression
                // position the operator belongs to the expansion.
                let brace_stmt = stmt_list
                    && !item_list
                    && stmt_boundary
                    && call.delim == Delim::Brace
                    && !expanded.is_empty()
                    && !begins_item
                    && !next_is_semi
                    && !matches!(expanded.last(), Some(Tt::Tok(t)) if t.tok == Tok::Semi)
                    && !matches!(expanded.first(), Some(Tt::Tok(t)) if t.tok == Tok::Let)
                    && continues_expr(tok_at(&trees, next).map(|t| t.tok));
                // An expansion with no statements is one expression
                // statement there, which rustc types as `()` unless a `.`
                // or `?` continues it (`m!{x}.max(3)`): a block gives the
                // parser both rules. Other expansions end with a `;`.
                if brace_stmt && !expanded.iter().any(|t| t.is_tok(Tok::Semi)) {
                    expanded = vec![Tt::Delim(Delim::Brace, expanded, call.span)];
                    out.extend(expanded);
                } else {
                    out.extend(expanded);
                    if brace_stmt {
                        out.push(Tt::Tok(Token { tok: Tok::Semi, span: call.span }));
                    }
                }
                i = next;
                pending_macro_use = false;
                continue;
            }
            // Any other group: expand inside, under its own scope.
            if matches!(trees.get(i), Some(Tt::Delim(_, _, _))) {
                let tree = take(&mut trees, i);
                let Tt::Delim(d, inner, gspan) = tree else { unreachable!() };
                let textual_len = self.textual.len();
                let imports_len = self.imports.len();
                let glob_len = self.glob_macros.len();
                let glob_ty_len = self.glob_type_names.len();
                self.scope_depth += 1;
                // An enum body: its first part is a variant, never a
                // block's tail (`cfg_on_operator_stmt`).
                let enum_body = d == Delim::Brace
                    && out
                        .iter()
                        .rev()
                        .take_while(|t| !t.is_tok(Tok::Semi) && !matches!(t, Tt::Delim(Delim::Brace, _, _)))
                        .any(|t| t.is_tok(Tok::Enum));
                // An `impl` or `trait` header with no `fn` in it (`fn f() ->
                // impl Tr {` is a fn body).
                let assoc_body = d == Delim::Brace && {
                    let head = || out.iter().rev().take_while(|t| !t.is_tok(Tok::Semi) && !matches!(t, Tt::Delim(Delim::Brace, _, _)));
                    head().any(|t| t.is_tok(Tok::Impl) || t.is_tok(Tok::Trait)) && !head().any(|t| t.is_tok(Tok::Fn))
                };
                let group = group_kind(d, &out, trees.get(i + 1), self.group, self.enum_body);
                // A tuple stays a tuple when cfg drops all but one element:
                // `(#[cfg(off)] a, b)` is `(b,)`.
                let tuple = group == Group::Tuple && has_top(&inner, 0, Tok::Comma);
                let outer_group = std::mem::replace(&mut self.group, group);
                let outer_enum = std::mem::replace(&mut self.enum_body, enum_body);
                let outer_assoc = std::mem::replace(&mut self.assoc_body, assoc_body);
                let scope_calls = std::mem::replace(&mut self.scope_calls, self.plain_calls.len());
                let expanded = self.expand_list(inner, depth, false, d == Delim::Brace, nest + 1);
                self.scope_calls = scope_calls;
                self.enum_body = outer_enum;
                self.assoc_body = outer_assoc;
                self.group = outer_group;
                let expanded = match expanded {
                    Ok(mut e) if tuple && !e.is_empty() && !has_top(&e, 0, Tok::Comma) => {
                        e.push(Tt::Tok(Token { tok: Tok::Comma, span: gspan }));
                        Ok(e)
                    }
                    other => other,
                };
                self.scope_depth -= 1;
                self.textual.truncate(textual_len);
                self.imports.truncate(imports_len);
                self.glob_macros.truncate(glob_len);
                self.glob_type_names.truncate(glob_ty_len);
                out.push(Tt::Delim(d, expanded?, gspan));
                i += 1;
                pending_macro_use = false;
                continue;
            }
            if matches!(&trees[i], Tt::Tok(t) if t.tok != Tok::Eof) {
                out.push(take(&mut trees, i));
            } else if matches!(&trees[i], Tt::Frag(..)) {
                // Macro calls inside a fragment expand when the
                // fragment lands in place: matching captures them
                // unexpanded (`add!(add!(1, 2), 3)` binds the inner
                // call inside the expr fragment), so walk the
                // fragment's trees like any other list here.
                let group = match &trees[i] {
                    Tt::Frag(FragKind::Expr | FragKind::Expr2021, _, _) => {
                        Group::Expr(item_list || !cfg_run_misplaced(&out, &trees, i, self.group, self.enum_body, self.ctx.interner))
                    }
                    Tt::Frag(FragKind::Stmt | FragKind::Item | FragKind::Block, _, _) => Group::Brace,
                    Tt::Frag(k, _, _) if k.transparent() => self.group,
                    _ => Group::Closed,
                };
                let tree = take(&mut trees, i);
                let Tt::Frag(kind, inner, fspan) = tree else { unreachable!() };
                let outer_group = std::mem::replace(&mut self.group, group);
                let expanded = self.expand_list(inner, depth, false, false, nest + 1);
                self.group = outer_group;
                out.push(Tt::Frag(kind, expanded?, fspan));
            }
            i += 1;
        }
        Ok(out)
    }

    /// Grammar-checks one cfg-disabled node (`trees[start..end]`, its
    /// attribute run included) before it is dropped, as rustc parses
    /// all code before cfg stripping. The check parses syntax only:
    /// no macro inside expands, no name resolution or type check runs,
    /// and a disabled `mod name;` never loads a file (module loading
    /// stays with the outline, which already honors cfg).
    /// A node of the file's own tokens (`depth` 0) is recorded as a
    /// `Dep::Dropped`.
    fn check_disabled_syntax(&mut self, trees: &[Tt], start: usize, end: usize, hint: crate::parser::CfgSyntaxHint, depth: u32) -> Result<(), Diag> {
        let mut toks = Vec::new();
        flatten_final(&trees[start..end], &mut toks);
        let brace = self.group == Group::Brace;
        crate::parser::check_cfg_syntax(&toks, &self.strings, self.ctx.interner, self.ctx.known, hint, brace)?;
        if let (0, Some(first), Some(last)) = (depth, toks.first(), toks.last()) {
            let (a, b) = (first.span, last.span);
            if a.ctxt == CtxtId::ROOT && b.ctxt == CtxtId::ROOT && a.file == b.file && a.lo < b.hi {
                let item = hint == crate::parser::CfgSyntaxHint::Item;
                self.deps.push(Dep::Dropped { file: a.file.0, lo: a.lo, hi: b.hi, item, brace });
            }
        }
        Ok(())
    }

    /// Handles an attribute run starting at `i` in `trees`, appending any
    /// kept trees to `out`. Returns the next index to walk.
    fn attr_run(
        &mut self,
        trees: &mut Vec<Tt>,
        start: usize,
        first: AttrInfo,
        pending_macro_use: &mut bool,
        out: &mut Vec<Tt>,
        item_list: bool,
        depth: u32,
    ) -> Result<usize, Diag> {
        // The expander reads `#![recursion_limit]` itself; once its value
        // is checked it passes on to the parser, so the checker reads the
        // same limit for trait and type depth (check/where_overflow.rs).
        if first.inner_attr && first.path == "recursion_limit" {
            recursion_limit_value(&first.inner, &self.strings, first.span)?;
        }
        // An inner attribute applies to the enclosing item or crate:
        // nothing for the expander to do with it here.
        if first.inner_attr {
            for k in start..first.end {
                out.push(take(trees, k));
            }
            return Ok(first.end);
        }
        let mut attrs = vec![first];
        let mut after = attrs[0].end;
        while let Some(next) = attr_at(trees, after, self.ctx.interner) {
            after = next.end;
            attrs.push(next);
        }
        // The parser checks attributes that reach it; a run the expander
        // strips here is checked first.
        if let Some(a) = attrs.iter().find(|a| matches!(a.path.as_str(), "cfg" | "cfg_attr"))
            && if item_list { in_where_clause(out) } else { cfg_run_misplaced(out, trees, after, self.group, self.enum_body, self.ctx.interner) }
        {
            return Err(err(
                C_SYNTAX,
                a.span,
                "attributes on expressions are not permitted in this context",
                "Put the attribute on a block around the statement, or use cfg!.",
            ));
        }
        // cfg_attr(cond, attr): keep, drop, or substitute. One level is
        // enough for the shapes in use; a substituted cfg is honored by
        // falling through to the cfg check below with its own trees.
        // rustc's deny-by-default `invalid_macro_export_arguments`, lifted
        // by a level on the same item (one written on a module or the
        // crate is not read: a false reject).
        let export_leveled = attrs.iter().any(|a| {
            matches!(a.path.as_str(), "allow" | "warn" | "expect")
                && a.inner.iter().any(|t| matches!(t, Tt::Tok(x) if matches!(seg_text(x.tok, self.ctx.interner).as_deref(), Some("invalid_macro_export_arguments" | "future_incompatible"))))
        });
        let mut kept: Vec<(AttrInfo, usize)> = Vec::new();
        let mut pos = start;
        for attr in attrs {
            let attr_start = pos;
            pos = attr.end;
            if attr.path == "cfg_attr" {
                let split = attr.inner.iter().position(|t| t.is_tok(Tok::Comma)).unwrap_or(attr.inner.len());
                let on = builtin::eval_cfg(&attr.inner[..split], &self.ctx.cfg, self, attr.span)?;
                if !on {
                    continue;
                }
                // Rebuild as the inner attribute written plainly. An
                // inner attribute the expander itself acts on (cfg,
                // macro_export, macro_use) joins this run as if
                // written, so `cfg_attr(.., macro_export)` exports.
                let rest: Vec<Tt> = attr.inner[split + 1.min(attr.inner.len() - split)..].to_vec();
                let fake_path = rest.iter().find_map(|t| match t {
                    Tt::Tok(tok) => seg_text(tok.tok, self.ctx.interner),
                    _ => None,
                });
                let span = attr.span;
                let end = attr.end;
                drop(attr);
                if matches!(fake_path.as_deref(), Some("cfg" | "macro_export" | "macro_use")) {
                    let inner = match rest.get(1) {
                        Some(Tt::Delim(_, group, _)) => group.clone(),
                        _ => Vec::new(),
                    };
                    kept.push((AttrInfo { path: fake_path.unwrap(), inner, end, span, inner_attr: false }, usize::MAX));
                    continue;
                }
                out.push(Tt::Tok(Token { tok: Tok::Pound, span }));
                out.push(Tt::Delim(Delim::Bracket, rest, span));
                continue;
            }
            kept.push((attr, attr_start));
        }
        // A cfg that is off drops the item before expansion can see it,
        // so a disabled compile_error! or include! never runs (6.1).
        // The dropped node is still grammar-checked (rustc parses
        // before it strips), except a macro invocation or definition,
        // whose group rustc does not parse. A `#[test]` item outside a
        // test build drops the same way, as in rustc: it never reaches
        // name resolution.
        let mut exported = false;
        let mut macro_use_attr = false;
        for (attr, attr_start) in &kept {
            let mut off = false;
            match attr.path.as_str() {
                "cfg" => {
                    let on = builtin::eval_cfg(&attr.inner, &self.ctx.cfg, self, attr.span)?;
                    if !on {
                        self.cfg_dropped = true;
                        // A list element (argument, parameter, tuple or
                        // array element) runs to its comma, even a
                        // block-like one (`[#[cfg(off)] if c {1} else {2}, 3]`).
                        if self.group.is_list() {
                            // `vec![x; n]` takes two arguments: rustc
                            // rejects one that cfg removes.
                            if self.group == Group::Vec
                                && (has_top(trees, after, Tok::Semi) || out.iter().any(|t| t.is_tok(Tok::Semi)))
                            {
                                return Err(err(
                                    C_SYNTAX,
                                    attr.span,
                                    "`#[cfg]` cannot remove a part of `vec![value; length]`",
                                    "Remove the attribute, or put the cfg on the whole statement.",
                                ));
                            }
                            let end = elem_end(trees, after);
                            self.check_disabled_syntax(trees, start, end, crate::parser::CfgSyntaxHint::Node, depth)?;
                            return Ok(end);
                        }
                        if let Some(def) = macro_rules_at(trees, after, self.ctx.interner) {
                            // A definition body is token trees rustc
                            // does not grammar-check before stripping;
                            // only its outer form counts.
                            check_def_form(trees, &def)?;
                            return Ok(def.end);
                        }
                        // A macro call is boundable even though it is
                        // not a keyword item: path, `!`, its group,
                        // and an optional `;`. Dropping it here keeps
                        // a disabled `include!` or `compile_error!`
                        // from ever expanding (found in ts-rust's
                        // wasm-only bundled embed).
                        if let Some((_, _, group_idx)) = path_call_at(trees, after, self.ctx.interner)
                            && let Some(end) = macro_node_end(trees, after, group_idx)
                        {
                            return Ok(end);
                        }
                        if let Some(end) = item_end(trees, after, self.ctx.interner) {
                            self.check_disabled_syntax(trees, start, end, crate::parser::CfgSyntaxHint::Item, depth)?;
                            return Ok(end);
                        }
                        // A statement, match arm, or comma-ended part:
                        // bounded at token level, dropped whole so
                        // nothing inside it expands.
                        if let Some(end) = node_end(trees, after) {
                            self.check_disabled_syntax(trees, start, end, crate::parser::CfgSyntaxHint::Node, depth)?;
                            return Ok(end);
                        }
                        let _ = attr_start;
                        return Err(err(
                            C_UNSUPPORTED,
                            attr.span,
                            "`#[cfg]` on this statement form is not supported yet",
                            "Move the cfg to an item, or rewrite the statement with cfg!.",
                        ));
                    }
                }
                // Only a free fn drops: `#[test]` anywhere else (also on
                // an impl or trait fn) is an error in every build, and the
                // parser reports it.
                "test" => off = !self.ctx.cfg.test && !self.assoc_body && next_is_fn(trees, after),
                "macro_export" => {
                    check_macro_export_input(trees, &attr, export_leveled, self.ctx.interner)?;
                    exported = true;
                }
                "macro_use" => macro_use_attr = true,
                _ => {}
            }
            if off {
                if let Some(def) = macro_rules_at(trees, after, self.ctx.interner) {
                    check_def_form(trees, &def)?;
                    return Ok(def.end);
                }
                // A macro call is boundable even though it is
                // not a keyword item: path, `!`, its group,
                // and an optional `;`. Dropping it here keeps
                // a disabled `include!` or `compile_error!`
                // from ever expanding (found in ts-rust's
                // wasm-only bundled embed).
                if let Some((_, _, group_idx)) = path_call_at(trees, after, self.ctx.interner)
                    && let Some(end) = macro_node_end(trees, after, group_idx)
                {
                    return Ok(end);
                }
                if let Some(end) = item_end(trees, after, self.ctx.interner) {
                    self.check_disabled_syntax(trees, start, end, crate::parser::CfgSyntaxHint::Item, depth)?;
                    return Ok(end);
                }
                // A statement, match arm, or comma-ended part:
                // bounded at token level, dropped whole so
                // nothing inside it expands.
                if let Some(end) = node_end(trees, after) {
                    self.check_disabled_syntax(trees, start, end, crate::parser::CfgSyntaxHint::Node, depth)?;
                    return Ok(end);
                }
                let _ = attr_start;
                return Err(err(
                    C_UNSUPPORTED,
                    attr.span,
                    "`#[cfg]` on this statement form is not supported yet",
                    "Move the cfg to an item, or rewrite the statement with cfg!.",
                ));
            }
        }
        if exported || macro_rules_at(trees, after, self.ctx.interner).is_some() {
            if let Some(def) = macro_rules_at(trees, after, self.ctx.interner) {
                self.define_macro(trees, &def, exported, !item_list)?;
                return Ok(def.end);
            }
        }
        if macro_use_attr {
            *pending_macro_use = true;
        }
        // Keep attributes the expander does not own, minus the ones it
        // just acted on (a cfg that is on, macro_export/use markers).
        for (attr, attr_start) in &kept {
            if matches!(attr.path.as_str(), "cfg" | "macro_export" | "macro_use") {
                continue;
            }
            for k in *attr_start..attr.end {
                out.push(take(trees, k));
            }
        }
        let _ = item_list;
        Ok(after)
    }

    /// Compiles and registers the `macro_rules!` definition at `def`.
    fn define_macro(&mut self, trees: &[Tt], def: &DefStart, exported: bool, local_def: bool) -> Result<(), Diag> {
        // A `#[macro_export]` definition an expansion produced is only
        // a textual macro: rustc keeps it out of the crate root path
        // namespace ("macro-expanded macro_export macros cannot be
        // referred to by absolute paths"). Written defs carry the
        // root context; expansion output is stamped with its own.
        let export_attr = exported;
        let exported = exported && def.span.ctxt == CtxtId::ROOT;
        self.check_dup_export(def.name, def.name_span, exported)?;
        check_def_form(trees, def)?;
        let Tt::Delim(_, body, _) = &trees[def.group] else { unreachable!() };
        let body = body.clone();
        // An exported def was already compiled in the prescan; the walk
        // still makes it textually visible from here on.
        if exported
            && let Some(&idx) = self.exported.get(&def.name)
            && self.defs[idx as usize].name_span == def.name_span
        {
            self.def_expn[idx as usize] = self.expn;
            self.push_textual(def.name, idx, def.name_span);
            self.note_late_export(export_attr, def.name, idx);
            return Ok(());
        }
        let mut compiled = compile_macro(def.name, def.name_span, &body, exported, def.span, &self.strings, self.ctx.interner)?;
        compiled.local_def = local_def;
        let idx = self.register(Arc::new(compiled), exported, true);
        self.note_late_export(export_attr, def.name, idx);
        Ok(())
    }

    /// Records a `#[macro_export]` definition an expansion made as a
    /// crate root binding (`late_bindings`).
    fn note_late_export(&mut self, export_attr: bool, name: Sym, idx: u32) {
        if export_attr && self.expn != 0 {
            let calls = 0..self.plain_calls.len();
            let x = LateBinding { module: Vec::new(), name, def: idx, expn: self.expn, depth: 0, calls, glob: false, block: false };
            self.late_bindings.push(x);
        }
    }

    /// If a `use` item a macro cares about starts at `trees[i]`, registers
    /// its macro imports and returns the index just past the `;`.
    fn use_item_at(&mut self, trees: &[Tt], i: usize, item_list: bool) -> Option<usize> {
        let (public, content, end) = use_span_at(trees, i)?;
        let first = self.imports.len();
        for (segs, leading, alias) in collect_use_sites(&trees[content..end - 1], &[], self.ctx.interner) {
            self.import_macro(&segs, leading, alias, public && item_list);
        }
        // A block-level `use` binds in its whole block, and so does a
        // module-level one an expansion made (the prescan reads the
        // written ones).
        if !item_list || self.expn != 0 {
            for k in first..self.imports.len() {
                let (name, def, depth, expn) = self.imports[k];
                let calls = self.scope_calls..self.plain_calls.len();
                let x = LateBinding { module: self.module.clone(), name, def, expn, depth, calls, glob: false, block: !item_list };
                self.late_bindings.push(x);
            }
        }
        // A glob in a block brings the target module's macros into
        // this lexical scope (module-level globs are seeded by the
        // worklist instead; registering them again at file depth
        // would double-count). A glob at item-list level of a
        // module in this file is module scope, so only a `use`
        // below an item list (a fn body or block) registers here.
        // A module-level glob an expansion made is not among the
        // worklist's seeds (they come from written code), so it registers
        // here too.
        if !item_list || self.expn != 0 {
            let first = self.glob_macros.len();
            for (segs, leading) in collect_use_globs(&trees[content..end - 1], &[], self.ctx.interner) {
                self.import_glob_macros(&segs, leading);
            }
            for k in first..self.glob_macros.len() {
                let (name, def, depth, expn) = self.glob_macros[k];
                let calls = self.scope_calls..self.plain_calls.len();
                let x = LateBinding { module: self.module.clone(), name, def, expn, depth, calls, glob: true, block: !item_list };
                self.late_bindings.push(x);
            }
        }
        Some(end)
    }

    /// The canonical builtin macro a `use` path names, when the
    /// path is an exact canonical std macro path lust expands by
    /// that name (`std::vec`, `core::panic`).
    fn std_builtin_macro(&self, segs: &[Seg]) -> Option<Sym> {
        let path: Vec<&str> = segs.iter().map(|s| s.text.as_str()).collect();
        if crate::ty::lang::std_path_kind(&path) != Some(crate::ty::lang::StdPathKind::Macro) {
            return None;
        }
        let last = segs.last()?;
        (builtin::is_token_builtin(&last.text) || builtin::is_passthrough(&last.text)).then_some(last.sym)
    }

    /// The builtin macro a plain call name was bound to by a std
    /// macro import rename, if any. Latest binding wins.
    fn builtin_alias_of(&self, name: Sym) -> Option<Sym> {
        if let Some(&(_, canon)) = self.builtin_imports.iter().rev().find(|(n, _)| *n == name) {
            return Some(canon);
        }
        self.module_builtin_alias.get(&(self.module.clone(), name)).copied()
    }

    /// Registers the macros one block glob import (`use a::*;` in
    /// a body) brings into this lexical scope, at the current
    /// depth. The target module is read from the path tables the
    /// prescan and the worklist seeds built (`by_path` for public
    /// re-exports, `module_imports` for a module's own imports,
    /// which is where a module-level glob into that module lands).
    /// Textual `macro_rules!` definitions of the target are not
    /// glob-importable, so `module_defs` does not contribute. The
    /// submodule names macros are addressable through go to
    /// `glob_type_names` for macro call paths.
    fn import_glob_macros(&mut self, segs: &[Seg], leading_colon: bool) {
        if segs.is_empty() {
            return;
        }
        let syms: Vec<Sym> = segs.iter().map(|s| s.sym).collect();
        let texts: Vec<&str> = segs.iter().map(|s| s.text.as_str()).collect();
        let has = |m: &[Sym]| {
            let under = |k: &Vec<Sym>| k == m || (k.len() > m.len() && k[..m.len()] == *m);
            self.by_path.keys().any(|(k, _)| under(k)) || self.module_imports.keys().any(|(k, _)| under(k))
        };
        let target: Vec<Sym> = match texts[0] {
            "crate" => syms[1..].to_vec(),
            "self" => {
                let mut m = self.module.clone();
                m.extend_from_slice(&syms[1..]);
                m
            }
            "super" => {
                let supers = texts.iter().take_while(|&&t| t == "super").count();
                let keep = self.module.len().saturating_sub(supers);
                let mut m: Vec<Sym> = self.module[..keep].to_vec();
                m.extend_from_slice(&syms[supers.min(syms.len())..]);
                m
            }
            _ if leading_colon => syms.clone(),
            _ => {
                let mut m = self.module.clone();
                m.extend_from_slice(&syms);
                if has(&syms) {
                    syms.clone()
                } else if has(&m) {
                    m
                } else {
                    syms.clone()
                }
            }
        };
        let depth = self.scope_depth;
        let mut names: Vec<Sym> = Vec::new();
        for (m, name) in self.by_path.keys().chain(self.module_imports.keys()) {
            if *m == target && !names.contains(name) {
                names.push(*name);
            }
        }
        names.sort_by(|a, b| self.ctx.interner.get(*a).cmp(self.ctx.interner.get(*b)));
        for name in names {
            // A re-export (`by_path`) visible from here is what a glob
            // of the target sees from outside; the target's own private
            // imports (`module_imports`) only count for a glob in
            // a body of that same module.
            let own = if target == self.module { self.module_imports.get(&(target.clone(), name)).copied() } else { None };
            let key = (target.clone(), name);
            let visible = self.by_path_vis.get(&key).is_none_or(|v| self.module.starts_with(v));
            let idx = match self.by_path.get(&key).copied().filter(|_| visible).or(own) {
                Some(i) => i,
                None if self.ambiguous_imports.contains_key(&(target.clone(), name)) => u32::MAX,
                None => continue,
            };
            self.glob_macros.push((name, idx, depth, self.expn));
        }
        let mut subs: Vec<Vec<Sym>> = Vec::new();
        for m in self.by_path.keys().map(|(m, _)| m).chain(self.module_imports.keys().map(|(m, _)| m)) {
            if m.len() == target.len() + 1 && m[..target.len()] == target[..] && !subs.contains(m) {
                subs.push(m.clone());
            }
        }
        subs.sort();
        for sub in subs {
            let name = *sub.last().unwrap();
            self.glob_type_names.push((name, sub, depth));
        }
    }

    /// A macro addressed by a path whose first segment a block
    /// glob brought in as a module name (`use m::*; use q::z;`
    /// or a `q::z!()` call): the module the glob binding names,
    /// with the rest of the path walked from it.
    fn glob_path_lookup(&self, segs: &[Seg]) -> Option<u32> {
        if segs.len() < 2 {
            return None;
        }
        let last = segs[segs.len() - 1].sym;
        let middle: Vec<Sym> = segs[1..segs.len() - 1].iter().map(|s| s.sym).collect();
        let mut found: Option<(Vec<Sym>, u32)> = None;
        for (name, gpath, _) in self.glob_type_names.iter().rev() {
            if *name != segs[0].sym {
                continue;
            }
            let mut cand = gpath.clone();
            cand.extend_from_slice(&middle);
            let key = (cand.clone(), last);
            if let Some(&idx) = self.by_path.get(&key)
                && self.by_path_vis.get(&key).is_none_or(|v| self.module.starts_with(v))
            {
                match &found {
                    Some((m, _)) if *m != cand => return None,
                    _ => found = Some((cand, idx)),
                }
            }
        }
        found.map(|(_, i)| i)
    }

    /// Records `alias` for the macro `segs` names, if it names one.
    fn import_macro(&mut self, segs: &[Seg], leading_colon: bool, alias: Sym, public: bool) {
        if segs.is_empty() {
            return;
        }
        let module = self.module.clone();
        let found = self
            .lookup_macro(segs, leading_colon)
            .or_else(|| self.resolve_for_use(segs, leading_colon, &module))
            .or_else(|| if leading_colon { None } else { self.glob_path_lookup(segs) });
        if let Some(idx) = found {
            self.imports.push((alias, idx, self.scope_depth, self.expn));
            if public {
                self.by_path.insert((self.module.clone(), alias), idx);
            }
        } else if self.ctx.interner.get(alias) != "_"
            && let Some(canon) = self.std_builtin_macro(segs)
        {
            self.builtin_imports.push((alias, canon));
        }
    }

    /// Expands one macro call one step: a user macro through the matcher,
    /// a token builtin through `builtin`, a parser macro through
    /// unchanged with its arguments expanded.
    pub fn expand_call(&mut self, call: &Call, depth: u32) -> Result<Vec<Tt>, Diag> {
        self.check_depth(depth, 0, call.span, || call.path_text())?;
        // A glob-brought name that does not shadow an outer macro
        // is the L0507 ambiguity error, not a missing macro.
        if !call.leading_colon && call.segs.len() == 1 {
            let seg = &call.segs[0];
            if matches!(self.plain_macro(seg.sym, &seg.text), PlainMacro::Expanded) {
                return Err(Diag::new(
                    "L0507",
                    call.span,
                    format!("`{}` is ambiguous: a macro-expanded macro may not shadow an existing macro of this name", seg.text),
                    "Rename the macro the expansion defines, or call it only inside that expansion.",
                ));
            }
            if self.plain_call_ambiguous(seg) {
                // With a textual definition in scope the conflict is
                // rustc's macro_rules-vs-import one (`plain_macro`).
                if self.textual.iter().any(|(n, _, _)| *n == seg.sym) {
                    return Err(Diag::new(
                        "L0507",
                        call.span,
                        format!("`{}` is ambiguous: a `macro_rules!` name and a macro imported from another module", seg.text),
                        "Rename one of them, or call the imported one by its path.",
                    ));
                }
                return Err(crate::resolve::imports::ambiguous_diag(&seg.text, call.span));
            }
            self.note_plain_call(seg, call.span);
        }
        if !call.leading_colon && call.segs.len() > 1 {
            self.check_macro_path_first(call)?;
        }
        if let Some(idx) = self.lookup_macro(&call.segs, call.leading_colon) {
            let def = self.defs[idx as usize].clone();
            return self.transcribe_call(&def, call, depth);
        }
        // A plain name bound by a std macro import rename expands
        // exactly as the canonical builtin name.
        let alias = if call.segs.len() == 1 && !call.leading_colon { self.builtin_alias_of(call.segs[0].sym) } else { None };
        let name = match alias {
            Some(canon) => self.ctx.interner.get(canon).to_string(),
            None => call.name_text().to_string(),
        };
        if self.builtin_call_path(&call.segs, call.leading_colon) {
            // A builtin counts depth as rustc's expansion of it does (see
            // `builtin::rustc_depth`): its arguments expand `args` levels
            // down, so a token builtin's own one-level-down expansions
            // run from `depth + args - 1`.
            let (extra, args) = builtin::rustc_depth(&name, &call.inner);
            if builtin::is_token_builtin(&name) {
                self.check_depth(depth, extra, call.span, || name.clone())?;
                return builtin::expand_builtin(self, &name, call, depth + args - 1);
            }
            if builtin::is_passthrough(&name) {
                self.check_depth(depth, extra, call.span, || name.clone())?;
                // The head already ends with the call's `!`. The parser
                // owns only the plain `name!` form, so keep just the
                // last segment and the bang of a qualified path.
                let head = &call.head[call.head.len().saturating_sub(2)..];
                let mut out: Vec<Tt> = head.to_vec();
                // The name spans the whole path, as in `expand_list`.
                if let (Some(Tt::Tok(tok)), Some(Tt::Tok(first))) = (out.first_mut(), call.head.first())
                    && (first.span.file, first.span.ctxt) == (tok.span.file, tok.span.ctxt)
                {
                    tok.span = first.span.to(tok.span);
                }
                // A renamed call keeps the canonical head name:
                // the parser owns only the plain builtin spellings.
                if let Some(canon) = alias
                    && let Some(Tt::Tok(tok)) = out.first_mut()
                    && matches!(tok.tok, Tok::Ident(_))
                {
                    tok.tok = Tok::Ident(canon);
                }
                let written_lit = is_str_lit_arg(&call.inner);
                let msg = if name == "assert" { builtin::assert_message(self, &call.inner, call.span)? } else { Vec::new() };
                let group = if name == "vec" { Group::Vec } else { Group::Closed };
                let outer_group = std::mem::replace(&mut self.group, group);
                let inner = self.expand_list(call.inner.clone(), depth + args, false, false, 0);
                self.group = outer_group;
                let mut inner = inner?;
                inner.extend(msg);
                if !written_lit && matches!(name.as_str(), "println" | "print" | "eprintln" | "eprint" | "format" | "panic") {
                    mark_format_str(&mut inner, call.span);
                }
                out.push(Tt::Delim(call.delim, inner, call.group_span));
                return Ok(out);
            }
        }
        if !call.leading_colon
            && let [seg] = &call.segs[..]
            && self.ambiguous_imports.contains_key(&(self.module.clone(), seg.sym))
        {
            return Err(crate::resolve::imports::ambiguous_diag(&seg.text, call.span));
        }
        Err(err(
            C_UNKNOWN,
            call.span,
            format!("cannot find macro `{}` in this scope", call.path_text()),
            "Define it with macro_rules! above this point, export it, or import it with use.",
        ))
    }

    /// Expands trees that must come back as statements or expressions of
    /// their written shape (builtin arguments), one level from `depth`.
    pub fn expand_more(&mut self, trees: Vec<Tt>, depth: u32) -> Result<Vec<Tt>, Diag> {
        self.expand_list(trees, depth + 1, false, false, 0)
    }

    /// The current module path as `module_path!` prints it.
    pub fn module_path_text(&self) -> String {
        let mut parts = vec![self.ctx.crate_name()];
        for seg in &self.module {
            parts.push(self.ctx.interner.get(*seg).to_string());
        }
        parts.join("::")
    }
}

/// True when the last top-level statement segment of an expansion
/// starts with `let` and carries no `;` of its own.
fn ends_with_unfinished_let(expanded: &[Tt]) -> bool {
    let seg = match expanded.iter().rposition(|t| t.is_tok(Tok::Semi)) {
        Some(i) => &expanded[i + 1..],
        None => expanded,
    };
    matches!(seg.first(), Some(Tt::Tok(t)) if t.tok == Tok::Let)
}

/// True when a one-step expansion should be parenthesized in the flat
/// token stream. A macro call is one syntax node in rustc; in a flat
/// stream a multi-token expansion would re-bind under surrounding
/// operators, so expression-shaped output is wrapped. Item and
/// statement sequences, single trees, and type-looking positions are
/// left alone.
/// True when a token after an expression continues it (a binary or
/// assignment operator, `.`, `?`, `as`, or a range): at statement start,
/// rustc reads `m!(..) op ..` as one expression.
fn continues_expr(t: Option<Tok>) -> bool {
    matches!(
        t,
        Some(
            Tok::Minus
                | Tok::Plus
                | Tok::Star
                | Tok::Slash
                | Tok::Percent
                | Tok::EqEq
                | Tok::Ne
                | Tok::Lt
                | Tok::Le
                | Tok::Gt
                | Tok::Ge
                | Tok::AndAnd
                | Tok::OrOr
                | Tok::Amp
                | Tok::Pipe
                | Tok::Caret
                | Tok::Shl
                | Tok::Shr
                | Tok::Dot
                | Tok::Question
                | Tok::As
                | Tok::DotDot
                | Tok::DotDotEq
                | Tok::Eq
                | Tok::PlusEq
                | Tok::MinusEq
                | Tok::StarEq
                | Tok::SlashEq
                | Tok::PercentEq
                | Tok::AmpEq
                | Tok::PipeEq
                | Tok::CaretEq
                | Tok::ShlEq
                | Tok::ShrEq
        )
    )
}

/// True when an expansion starts with a block-like expression (`match`,
/// `if`, a loop, `unsafe`, or a `{ }` block), which the parser ends a
/// statement at.
fn starts_block_like(expanded: &[Tt]) -> bool {
    match expanded.first() {
        Some(Tt::Tok(t)) => matches!(t.tok, Tok::Match | Tok::If | Tok::Loop | Tok::While | Tok::For | Tok::Unsafe),
        Some(Tt::Delim(Delim::Brace, _, _)) => true,
        _ => false,
    }
}

fn should_wrap(expanded: &[Tt], prev_out: &[Tt], next_tok: Option<Tok>, next_tree: Option<&Tt>, interner: &Interner) -> bool {
    if expanded.len() <= 1 || starts_item(expanded, interner) {
        return false;
    }
    if expanded.iter().any(|t| t.is_tok(Tok::Semi)) {
        // Statement sequences stand as written. In expression
        // position a `;` in the expansion is where rustc stops
        // ("trailing semicolon in macro used in expression
        // position", "macro expansion ignores ..."); wrapping makes
        // the flat stream reject there too instead of silently
        // reading the expansion as statements of the caller.
        let prev_expr = matches!(prev_out.last(), Some(Tt::Tok(t)) if matches!(
            t.tok,
            Tok::Eq
                | Tok::Comma
                | Tok::Colon
                | Tok::Plus
                | Tok::Minus
                | Tok::Star
                | Tok::Slash
                | Tok::Percent
                | Tok::EqEq
                | Tok::Ne
                | Tok::Lt
                | Tok::Le
                | Tok::Gt
                | Tok::Ge
                | Tok::AndAnd
                | Tok::OrOr
                | Tok::Amp
                | Tok::Pipe
                | Tok::Caret
                | Tok::Shl
                | Tok::PlusEq
                | Tok::MinusEq
                | Tok::StarEq
                | Tok::SlashEq
                | Tok::PercentEq
                | Tok::AmpEq
                | Tok::PipeEq
                | Tok::CaretEq
                | Tok::ShlEq
                    | Tok::Shr
                    | Tok::ShrEq
                | Tok::Dot
                | Tok::Question
                | Tok::As
                | Tok::Return
                | Tok::FatArrow
        ));
        let next_expr = matches!(
            next_tok,
            Some(
                Tok::Plus
                    | Tok::Minus
                    | Tok::Star
                    | Tok::Slash
                    | Tok::Percent
                    | Tok::EqEq
                    | Tok::Ne
                    | Tok::Lt
                    | Tok::Le
                    | Tok::Gt
                    | Tok::Ge
                    | Tok::AndAnd
                    | Tok::OrOr
                    | Tok::Amp
                    | Tok::Pipe
                    | Tok::Caret
                    | Tok::Shl
                    | Tok::PlusEq
                    | Tok::MinusEq
                    | Tok::StarEq
                    | Tok::SlashEq
                    | Tok::PercentEq
                    | Tok::AmpEq
                    | Tok::PipeEq
                    | Tok::CaretEq
                    | Tok::ShlEq
                    | Tok::Shr
                    | Tok::ShrEq
                    | Tok::Eq
                    | Tok::Dot
                    | Tok::Question
                    | Tok::As
                    | Tok::DotDot
                    | Tok::DotDotEq
            )
        );
        return prev_expr || next_expr;
    }
    if matches!(expanded.first(), Some(Tt::Tok(t)) if t.tok == Tok::Let) {
        return false;
    }
    // After `:` in a let or field, or inside `< ... >`, the expansion is
    // most often a type; parens would make it a tuple/paren type shape.
    if matches!(prev_out.last(), Some(Tt::Tok(t)) if matches!(t.tok, Tok::Colon | Tok::Lt | Tok::As)) {
        return false;
    }
    // One atomic operand (a call, a place, a block-like head) binds as
    // tightly as the macro call did, so it needs no parens.
    if atomic_shaped(expanded) {
        return false;
    }
    // A whole comma piece (a call argument, an array element) parses as
    // one expression in place; parens only matter when the expansion
    // itself would split the piece with a top-level comma.
    let piece_start = prev_out.is_empty() || matches!(prev_out.last(), Some(Tt::Tok(t)) if t.tok == Tok::Comma);
    let piece_end = next_tree.is_none() || next_tok == Some(Tok::Comma);
    if piece_start && piece_end && !expanded.iter().any(|t| t.is_tok(Tok::Comma)) {
        return false;
    }
    // A path-shaped expansion directly before a `{ }` group is most
    // often a struct literal head; parens would split it from its fields.
    let _ = next_tok;
    if matches!(next_tree, Some(Tt::Delim(Delim::Brace, _, _)))
        && expanded
            .iter()
            .all(|t| matches!(t, Tt::Tok(tok) if is_seg_tok(tok.tok) || matches!(tok.tok, Tok::PathSep | Tok::Lt | Tok::Gt | Tok::Comma)))
    {
        return false;
    }
    true
}

/// If a `use` item starts at `trees[i]`, returns whether it is public,
/// the content start (just past `use`), and the end (just past `;`).
fn use_span_at(trees: &[Tt], i: usize) -> Option<(bool, usize, usize)> {
    let mut j = i;
    let mut public = false;
    if tok_at(trees, j).map(|t| t.tok) == Some(Tok::Pub) {
        public = true;
        j += 1;
        if matches!(trees.get(j), Some(Tt::Delim(Delim::Paren, _, _))) {
            j += 1;
        }
    }
    // `use<..>` is a precise-capturing bound in a signature
    // (`-> impl Send + use<>`), never a `use` item.
    if tok_at(trees, j).map(|t| t.tok) != Some(Tok::Use) || tok_at(trees, j + 1).map(|t| t.tok) == Some(Tok::Lt) {
        return None;
    }
    let end = (j..trees.len()).find(|&k| matches!(&trees[k], Tt::Tok(t) if t.tok == Tok::Semi))? + 1;
    Some((public, j + 1, end))
}

/// Every (glob target path, leading-colon flag) one `use` tree
/// glob-imports, groups included. `prefix` carries the path of an
/// enclosing group, as in `collect_use_sites`.
fn collect_use_globs(trees: &[Tt], prefix: &[Seg], interner: &Interner) -> Vec<(Vec<Seg>, bool)> {
    let mut out = Vec::new();
    let mut segs: Vec<Seg> = prefix.to_vec();
    let mut i = 0;
    let leading_colon = prefix.is_empty() && tok_at(trees, i).map(|t| t.tok) == Some(Tok::PathSep);
    if leading_colon {
        i += 1;
    }
    while i < trees.len() {
        match &trees[i] {
            Tt::Delim(Delim::Brace, group, _) => {
                let mut start = 0;
                for k in 0..=group.len() {
                    if k == group.len() || matches!(&group[k], Tt::Tok(t) if t.tok == Tok::Comma) {
                        if start < k {
                            out.extend(collect_use_globs(&group[start..k], &segs, interner));
                        }
                        start = k + 1;
                    }
                }
                return out;
            }
            Tt::Tok(t) if t.tok == Tok::Star => {
                out.push((segs, leading_colon));
                return out;
            }
            Tt::Tok(t) if is_seg_tok(t.tok) => {
                let (Some(sym), Some(text)) = (seg_sym(t.tok, interner), seg_text(t.tok, interner)) else { return out };
                if text == "self" {
                    return out;
                }
                segs.push(Seg { sym, text, span: t.span });
                i += 1;
            }
            Tt::Tok(t) if t.tok == Tok::PathSep => i += 1,
            _ => return out,
        }
    }
    out
}

/// Every (target path, leading-colon flag, imported name) one `use`
/// tree brings in. `prefix` carries the path of an enclosing group.
fn collect_use_sites(trees: &[Tt], prefix: &[Seg], interner: &Interner) -> Vec<(Vec<Seg>, bool, Sym)> {
    let mut out = Vec::new();
    let mut segs: Vec<Seg> = prefix.to_vec();
    let mut i = 0;
    let mut leading_colon = false;
    if tok_at(trees, i).map(|t| t.tok) == Some(Tok::PathSep) {
        leading_colon = true;
        i += 1;
    }
    while i < trees.len() {
        match &trees[i] {
            Tt::Delim(Delim::Brace, group, _) => {
                let mut start = 0;
                for k in 0..=group.len() {
                    if k == group.len() || matches!(&group[k], Tt::Tok(t) if t.tok == Tok::Comma) {
                        if start < k {
                            out.extend(collect_use_sites(&group[start..k], &segs, interner));
                        }
                        start = k + 1;
                    }
                }
                return out;
            }
            Tt::Tok(t) if t.tok == Tok::As => {
                if let Some(rename) = tok_at(trees, i + 1).and_then(|t| seg_sym(t.tok, interner)) {
                    out.push((segs, leading_colon, rename));
                }
                return out;
            }
            Tt::Tok(t) if is_seg_tok(t.tok) => {
                let (Some(sym), Some(text)) = (seg_sym(t.tok, interner), seg_text(t.tok, interner)) else { return out };
                if text == "self" {
                    // `use a::{self, ..}` imports `a` itself, not a macro here.
                    return out;
                }
                segs.push(Seg { sym, text, span: t.span });
                i += 1;
            }
            Tt::Tok(t) if t.tok == Tok::PathSep => i += 1,
            // A glob import of macros is not tracked (textual macros
            // are not glob-importable in Rust).
            _ => return out,
        }
    }
    if let Some(last) = segs.last().map(|s| s.sym) {
        out.push((segs, leading_colon, last));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::FileId;

    fn expand_src(interner: &Interner, known: &Known, src: &str) -> Result<Vec<String>, Diag> {
        let lexed = crate::lexer::lex(src, FileId(0), 0, interner).expect("test source lexes");
        let ctx = ExpandCtx::for_file(interner, known, std::path::Path::new("test.rs"), src, false);
        let out = expand_lexed(lexed, &ctx)?;
        Ok(out.tokens.iter().map(|t| tok_text(&t.tok, &out.strings, interner)).collect())
    }

    /// A simple call expands, and expanding the same call again in the
    /// same process (what a daemon re-check does) hits the cache.
    #[test]
    fn expansion_cache_evicts_least_recently_used_past_its_cap() {
        let key = |i: u32| CacheKey {
            def_fingerprint: 1,
            input_hash: 2,
            input_span_hash: 3,
            call_file: 0,
            call_lo: i,
            call_hi: i + 1,
            call_ctxt: 0,
            cfg_hash: 4,
            edition: 2024,
            deps_hash: 0,
            layout: 0,
        };
        let exp = || (Vec::new(), vec!["x".repeat(1000)], CtxtId::ROOT);
        let mut c = ExpansionCache::new(20_000);
        for i in 0..15 {
            c.insert(key(i), exp(), 0);
        }
        assert!(c.get(&key(0)).is_some(), "under the cap nothing goes");
        for i in 15..40 {
            c.insert(key(i), exp(), 0);
            assert!(c.bytes <= 20_000, "{} bytes", c.bytes);
            assert_eq!(c.bytes, c.map.values().map(|e| e.1).sum::<usize>());
        }
        assert!(c.get(&key(39)).is_some(), "the newest entry stays");
        assert!(c.get(&key(1)).is_none(), "an old unused entry went");
    }

    #[test]
    fn expansion_cache_hits_on_repeat() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let src = "macro_rules! one { () => { 1 } }\nfn main() { let _x = one!(); }";
        let (hits0, _) = cache_stats();
        let first = expand_src(&interner, &known, src).expect("first expansion");
        let second = expand_src(&interner, &known, src).expect("second expansion");
        assert_eq!(first, second);
        let (hits1, _) = cache_stats();
        assert!(hits1 > hits0, "second identical expansion should hit the cache");
    }

    /// A cache hit in a later run (a daemon re-check after an edit) gets
    /// the strings its tokens name, though that run's string table holds
    /// other strings at those indexes: the edit adds a string literal
    /// before the call, at the same length, so the call's key is the same.
    #[test]
    fn expansion_cache_hit_keeps_its_strings() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let call = "macro_rules! cached_s { ($x:expr) => { ($x, \"tpl\", stringify!(0x10)) } }\nfn main() { let a = ";
        let tail = "; let _v = cached_s!(\"bee\"); }";
        let before = expand_src(&interner, &known, &format!("{call}12345{tail}")).expect("first expansion");
        let (hits0, _) = cache_stats();
        let after = expand_src(&interner, &known, &format!("{call}\"123\"{tail}")).expect("second expansion");
        let (hits1, _) = cache_stats();
        assert!(hits1 > hits0, "the second call should hit the cache");
        for out in [&before, &after] {
            for text in ["\"bee\"", "\"tpl\"", "\"0x10\""] {
                assert!(out.iter().any(|t| t == text), "{text} missing from {out:?}");
            }
        }
    }

    /// A macro body's locals carry a non-root context; an ident the
    /// caller passes in keeps the root context (ARCH 6.3).
    #[test]
    fn hygiene_contexts_on_tokens() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let src = "macro_rules! w { ($e:expr) => {{ let tmp = 1; tmp + $e }} }\nfn main() { let tmp = 2; let _x = w!(tmp); }";
        let lexed = crate::lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ctx = ExpandCtx::for_file(&interner, &known, std::path::Path::new("test.rs"), src, false);
        let out = expand_lexed(lexed, &ctx).expect("expansion");
        let tmps: Vec<CtxtId> =
            out.tokens.iter().filter(|t| matches!(t.tok, Tok::Ident(s) if interner.get(s) == "tmp")).map(|t| t.span.ctxt).collect();
        assert_eq!(tmps.len(), 4, "caller let, macro let, macro use, caller arg");
        assert_eq!(tmps[0], CtxtId::ROOT, "caller's own binding");
        assert_ne!(tmps[1], CtxtId::ROOT, "macro-introduced binding has the expansion context");
        assert_eq!(tmps[1], tmps[2], "macro binding and its use share a context");
        assert_eq!(tmps[3], CtxtId::ROOT, "the passed-in ident keeps the caller's context");
    }

    /// Local ambiguity and follow-set violations are hard errors with
    /// their stable codes, not silent first-match wins.
    #[test]
    fn ambiguity_and_follow_errors() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let amb = expand_src(&interner, &known, "macro_rules! m { ($($i:ident)* $j:ident) => { () } }\nfn main() { m!(x); }");
        assert_eq!(amb.unwrap_err().code, C_AMBIG);
        let follow = expand_src(&interner, &known, "macro_rules! m { ($e:expr +) => { $e } }\nfn main() {}");
        assert_eq!(follow.unwrap_err().code, C_DEF);
    }

    /// A fragment parse that began and failed is a hard error, even
    /// when a later arm token-matches the input (rustc does not fall
    /// through). With the token arm first, the same call expands.
    #[test]
    fn fragment_hard_failure_stops_arm_search() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let hard = expand_src(&interner, &known, "macro_rules! m { ($e:expr ;) => { 1 }; (1 +) => { 2 } }\nfn main() { let _ = m!(1 +); }");
        assert_eq!(hard.unwrap_err().code, C_CALL);
        let first =
            expand_src(&interner, &known, "macro_rules! m { (1 +) => { 2 }; ($e:expr ;) => { 1 } }\nfn main() { let _ = m!(1 +); }");
        assert!(first.expect("token arm first wins").iter().any(|t| t == "2"));
        // A fragment that cannot begin on the first token kills only
        // its own arm, so the next arm still gets its try.
        let soft = expand_src(&interner, &known, "macro_rules! m { ($e:expr) => { 1 }; (+) => { 2 } }\nfn main() { let _ = m!(+); }");
        assert!(soft.expect("soft fragment failure falls through").iter().any(|t| t == "2"));
    }

    /// Edition 2024 follow sets, separator rules, and empty repetitions
    /// are definition errors; an unbound template name is not.
    #[test]
    fn definition_checks_match_rustc() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        for src in [
            "macro_rules! m { ($p:pat |) => { 0 } }\nfn main() {}",
            "macro_rules! m { ($t:ty >=) => { 0 } }\nfn main() {}",
            "macro_rules! m { ($($i:ident),?) => { 1 } }\nfn main() {}",
            "macro_rules! m { ($($i:ident),*) => { $($i),? } }\nfn main() {}",
            "macro_rules! m { ($($v:vis)*) => { 1 } }\nfn main() {}",
        ] {
            assert_eq!(expand_src(&interner, &known, src).unwrap_err().code, C_DEF, "src: {src}");
        }
        let unbound = expand_src(&interner, &known, "macro_rules! m { () => { $y } }\nfn main() {}");
        assert!(unbound.is_ok(), "an uncalled arm's unbound name is not a definition error");
    }

    /// Fragment validation does not care that the template only
    /// stringifies the fragment: token soup inside a group is not an
    /// expr, and byte string patterns distinguish their bytes.
    #[test]
    fn invalid_fragments_do_not_bind() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let soup =
            expand_src(&interner, &known, "macro_rules! m { ($e:expr) => { stringify!($e) } }\nfn main() { let _s = m!((1 2, 3)); }");
        assert_eq!(soup.unwrap_err().code, C_CALL);
        let bytes =
            expand_src(&interner, &known, "macro_rules! m { (b\"a\") => { 1 }; ($t:tt) => { 2 } }\nfn main() { let _ = m!(b\"b\"); }")
                .expect("tt arm takes the other byte string");
        assert!(bytes.iter().any(|t| t == "2"), "tokens: {bytes:?}");
    }

    /// An `include_str!` read records a file dependency whose hash
    /// goes stale when the file changes; an `option_env!` read records
    /// the value it saw (ARCH 6.4). The daemon drops a chunk on stale
    /// deps instead of serving the old expansion.
    #[test]
    fn include_and_env_reads_record_deps() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let dir = std::env::temp_dir().join(format!("lust-deps-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let data = dir.join("data.txt");
        std::fs::write(&data, "one").unwrap();
        let main_rs = dir.join("main.rs");
        let src = "fn main() { let _s = include_str!(\"data.txt\"); let _e = option_env!(\"LUST_DEPS_TEST_UNSET\"); }";
        let lexed = crate::lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ctx = ExpandCtx::for_file(&interner, &known, &main_rs, src, false);
        let (_out, deps) = expand_lexed_with_deps(lexed, &ctx).expect("expansion");
        assert!(deps.iter().any(|d| matches!(d, Dep::File { path, .. } if *path == data)), "deps: {deps:?}");
        assert!(deps.iter().any(|d| matches!(d, Dep::Env { name, value: None } if name == "LUST_DEPS_TEST_UNSET")), "deps: {deps:?}");
        assert!(!deps_stale(&deps, &ClientView::PROCESS), "fresh deps are not stale");
        assert!(deps_stale_with(&deps, &|_: &str| Some("now set".to_string())), "a changed env value is stale");
        std::fs::write(&data, "two").unwrap();
        assert!(deps_stale(&deps, &ClientView::PROCESS), "a changed included file is stale");
        std::fs::remove_dir_all(&dir).ok();
    }

    /// A `use` that binds a parser macro's name needs the expander, so
    /// calls of it reach the imported macro; other uses do not.
    #[test]
    fn parser_macro_imports_need_expansion() {
        let interner = Interner::default();
        let needs = |src: &str| needs_expansion(&crate::lexer::lex(src, crate::diag::FileId(0), 0, &interner).unwrap().tokens, &interner);
        assert!(needs("use util::vec; fn main() { let _v = vec![1]; }"));
        assert!(needs("use util::{helper, panic}; fn main() {}"));
        assert!(needs("use util::mine as format; fn main() {}"));
        assert!(needs("fn main() { use util::assert; assert!(true); }"));
        assert!(!needs("use std::fmt::Write; use std::vec::Vec; fn main() { let v = vec![1]; println!(\"{v:?}\"); }"));
        assert!(!needs("fn main() { let vec = 1; let _ = vec; }"));
    }

    /// stringify! keeps the source's own spacing between tokens.
    #[test]
    fn stringify_keeps_spacing() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let out = expand_src(&interner, &known, "fn main() { let _s = stringify!(a+b); }").expect("expansion");
        assert!(out.iter().any(|t| t == "\"a+b\""), "tokens: {out:?}");
    }

    /// Two calls of one macro whose inputs differ only in spacing are
    /// different expansions for `stringify!`: the cache key reads the
    /// input spans, so the second call does not reuse the first's.
    #[test]
    fn stringify_spacing_not_cached_across_calls() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let src = "macro_rules! s { ($e:expr) => { stringify!($e) }; }\nfn main() { let _a = s!(f(a,b)); let _b = s!(f( a , b )); }";
        let out = expand_src(&interner, &known, src).expect("expansion");
        assert!(out.iter().any(|t| t == "\"f(a,b)\""), "tokens: {out:?}");
        assert!(out.iter().any(|t| t == "\"f(a, b)\""), "tokens: {out:?}");
    }

    /// `n` chained macros after `attrs`: `m0!()` expands to `m1!()`, and
    /// so on, so the last one expands at depth `n`, one token per level.
    fn chain_src(n: usize, attrs: &str) -> String {
        let mut src = attrs.to_string();
        for i in 0..n {
            src.push_str(&format!("macro_rules! m{i} {{ () => {{ m{}!() }} }}\n", i + 1));
        }
        src.push_str(&format!("macro_rules! m{n} {{ () => {{ 0 }} }}\nfn main() {{ let _x = m0!(); }}\n"));
        src
    }

    /// Expands `src` on a thread with a 512 KB stack (a pool thread has
    /// 2 MB), returning the error code and message on failure.
    fn expand_on_small_stack(src: String) -> Result<(), (&'static str, String)> {
        std::thread::Builder::new()
            .stack_size(512 << 10)
            .spawn(move || {
                let interner = Interner::default();
                let known = Known::new(&interner);
                expand_src(&interner, &known, &src).map(|_| ()).map_err(|d| (d.code, d.message))
            })
            .unwrap()
            .join()
            .unwrap()
    }

    /// The default limit allows depth 127 and stops at 128, as rustc.
    /// Deep expansion moves to fresh stacks as it goes, so 2000 levels
    /// fit on a small thread; past lust's cap of 2048 it stops with
    /// L0801 whatever the crate's limit. The first limit attribute wins.
    #[test]
    fn expansion_depth_limits_on_a_small_stack() {
        assert_eq!(expand_on_small_stack(chain_src(127, "")), Ok(()));
        assert_eq!(expand_on_small_stack(chain_src(128, "")).unwrap_err().0, "L0801");
        assert_eq!(expand_on_small_stack(chain_src(2000, "#![recursion_limit = \"2048\"]\n")), Ok(()));
        let capped = expand_on_small_stack(chain_src(2100, "#![recursion_limit = \"5000\"]\n")).unwrap_err();
        assert_eq!(capped.0, "L0801");
        assert!(capped.1.contains("lust's limit of 2048"), "{}", capped.1);
        let first_wins = "#![recursion_limit = \"300\"]\n#![recursion_limit = \"2\"]\n";
        assert_eq!(expand_on_small_stack(chain_src(200, first_wins)), Ok(()));
    }

    /// A macro whose recursion doubles its input stops at a cap in well
    /// under a second: repetition matching is linear in the input. It
    /// used to take minutes, then overflow the stack.
    #[test]
    fn doubling_macro_stops_at_a_cap() {
        let src = "macro_rules! count { () => { 0 }; ($h:tt $($t:tt)*) => { 1 + count!($(pub $t)*) }; }\nfn main() { let _x = count!(a b c); }";
        assert_eq!(expand_on_small_stack(src.to_string()).unwrap_err().0, "L0801");
    }
}
