// Builtin macros (ARCH 6.4) and the cfg evaluator expansion runs on.
// The parser's format macros (`println!`, `format!`, `vec!`, `panic!`,
// `assert!` and friends) stay parser forms and pass through; everything
// here expands at token level before the parser sees it.
use super::*;
use std::hash::Hash as _;

/// Macros the parser owns as `Expr::Macro` forms (`format_args!` is
/// one: its value is an `fmt::Arguments`) and `offset_of!`.
pub fn is_passthrough(name: &str) -> bool {
    matches!(
        name,
        "println"
            | "print"
            | "eprintln"
            | "eprint"
            | "format"
            | "panic"
            | "vec"
            | "assert"
            | "assert_eq"
            | "assert_ne"
            | "todo"
            | "unreachable"
            | "format_args"
            | "offset_of"
    )
}

/// How rustc 1.99 counts recursion depth for the std macro `name!` with
/// arguments `inner`, called at depth `d`: its own expansion reaches
/// `d + extra` (std macros it calls, such as `format_args!`), and macro
/// calls in its arguments expand at `d + args`. The values were measured
/// against rustc. Where the shape of the arguments is not checked here,
/// the larger value applies, so lust never allows a depth rustc rejects.
pub fn rustc_depth(name: &str, inner: &[Tt]) -> (u32, u32) {
    // The argument count `split_args` would give, without copying them.
    let commas = inner.iter().filter(|t| t.is_tok(Tok::Comma)).count();
    let args = if inner.is_empty() { 0 } else { commas + 1 - usize::from(inner.last().is_some_and(|t| t.is_tok(Tok::Comma))) };
    match name {
        "println" | "eprintln" if args == 0 => (2, 2),
        "println" | "eprintln" | "print" | "eprint" | "format" | "write" => (1, 2),
        "writeln" => (2, 2),
        "panic" if args == 0 => (1, 1),
        "panic" => (2, 3),
        "assert" if args <= 1 => (0, 1),
        "assert" => (2, 3),
        "assert_eq" | "assert_ne" if args <= 2 => (0, 1),
        "assert_eq" | "assert_ne" => (1, 2),
        "debug_assert" if args <= 1 => (1, 2),
        "debug_assert" => (3, 4),
        "debug_assert_eq" | "debug_assert_ne" if args <= 2 => (1, 2),
        "debug_assert_eq" | "debug_assert_ne" => (2, 3),
        "todo" | "unimplemented" if args == 0 => (0, 1),
        "todo" | "unimplemented" => (4, 5),
        "unreachable" if args == 0 => (1, 1),
        "unreachable" => (5, 6),
        "dbg" if args <= 1 => (3, 1),
        "dbg" => (4, 2),
        "thread_local" => (2, 3),
        _ => (0, 1),
    }
}

/// True for a macro name std puts in the macro prelude of a std-aware
/// crate (its `#[macro_export]` macros lust expands by name). Macro
/// resolution reads it as the outer binding a glob-brought macro of
/// the same name is ambiguous with (rustc E0659).
pub fn is_std_macro_name(name: &str) -> bool {
    is_token_builtin(name) || is_passthrough(name)
}

/// True when `name` is a bang macro every module sees without an import
/// (std's `#[macro_use]` prelude and the builtins of the std prelude), as
/// rustc 1.99 resolves it. A macro-expanded macro of such a name may not
/// shadow it (E0659). Measured against rustc: `pin` and `offset_of` live
/// in modules, so they are not here.
pub fn is_prelude_macro(name: &str) -> bool {
    let arch_detect = match std::env::consts::ARCH {
        "x86_64" | "x86" => "is_x86_feature_detected",
        "aarch64" => "is_aarch64_feature_detected",
        _ => "",
    };
    (is_std_macro_name(name) && !matches!(name, "pin" | "offset_of"))
        || name == arch_detect
        || matches!(name, "const_format_args" | "log_syntax" | "trace_macros" | "concat_bytes" | "cfg_select" | "type_ascribe" | "deref")
}

/// Macros this file expands at token level.
pub fn is_token_builtin(name: &str) -> bool {
    matches!(
        name,
        "matches"
            | "concat"
            | "stringify"
            | "cfg"
            | "env"
            | "option_env"
            | "line"
            | "column"
            | "file"
            | "module_path"
            | "include"
            | "include_str"
            | "include_bytes"
            | "compile_error"
            | "debug_assert"
            | "debug_assert_eq"
            | "debug_assert_ne"
            | "write"
            | "writeln"
            | "dbg"
            | "unimplemented"
            | "thread_local"
            | "pin"
    )
}

/// True when the written path of a qualified builtin call (`std::println`,
/// `core::prelude::v1::assert`, `alloc::vec`, crate first, macro name
/// last) names that macro in rustc 1.99. Measured against rustc for every
/// name of `is_passthrough` and `is_token_builtin`: core's root and
/// preludes hold the core macros; std's root and preludes add the
/// std-only ones; `pin!` and `offset_of!` live only in `pin` and `mem`.
/// Paths through private modules (`std::macros`) or other modules
/// (`std::vec::vec`, `core::println`) are rustc E0433.
pub fn std_macro_path(path: &[&str]) -> bool {
    let core_macro = |n: &str| {
        matches!(
            n,
            "panic"
                | "assert"
                | "assert_eq"
                | "assert_ne"
                | "debug_assert"
                | "debug_assert_eq"
                | "debug_assert_ne"
                | "todo"
                | "unreachable"
                | "unimplemented"
                | "format_args"
                | "matches"
                | "concat"
                | "stringify"
                | "cfg"
                | "env"
                | "option_env"
                | "line"
                | "column"
                | "file"
                | "module_path"
                | "include"
                | "include_str"
                | "include_bytes"
                | "compile_error"
                | "write"
                | "writeln"
        )
    };
    let std_only = |n: &str| matches!(n, "println" | "print" | "eprintln" | "eprint" | "format" | "vec" | "dbg" | "thread_local");
    let prelude = |p: &str| matches!(p, "v1" | "rust_2015" | "rust_2018" | "rust_2021" | "rust_2024");
    let Some((&name, module)) = path.split_last() else { return false };
    match module {
        ["std"] => core_macro(name) || std_only(name),
        ["std", "prelude", p] if prelude(p) => core_macro(name) || std_only(name),
        ["core"] => core_macro(name),
        ["core", "prelude", p] if prelude(p) => core_macro(name),
        ["alloc"] => matches!(name, "vec" | "format"),
        ["std" | "core", "pin"] => name == "pin",
        ["std" | "core", "mem"] => name == "offset_of",
        _ => false,
    }
}

/// The cfg facts a `cfg!` or `#[cfg]` in this file sees. Lust builds for
/// the host target with debug assertions on; a single file has no Cargo
/// features. Unknown names are false, as in rustc with no `--cfg`.
pub struct CfgEnv {
    pub test: bool,
    pub debug_assertions: bool,
    /// Full resolver facts (W-RESOLVE): flags as (name, None) and pairs
    /// as (name, Some(value)), including `feature` pairs. Consulted
    /// before the host facts below, so a crate session's real cfg
    /// environment (section 1.6) wins where the two disagree. Empty on
    /// the single-file path, which keeps the host facts.
    pub facts: Vec<(String, Option<String>)>,
    /// The panic strategy is unwind (`-C panic=unwind`): `cfg(panic)`
    /// in the host facts below.
    pub panic_unwind: bool,
}

impl CfgEnv {
    fn name_is(&self, name: &str, value: Option<&str>) -> bool {
        if !self.facts.is_empty() {
            return self.facts.iter().any(|(n, v)| n == name && v.as_deref() == value);
        }
        // The host target as `rustc --print cfg` prints it for
        // x86_64/aarch64 Linux with the build's panic strategy: lust builds
        // for the host, so these are the facts a cfg in user code sees.
        match (name, value) {
            ("test", None) => self.test,
            ("debug_assertions", None) => self.debug_assertions,
            ("unix", None) => true,
            ("windows", None) => false,
            ("panic", Some(v)) => v == if self.panic_unwind { "unwind" } else { "abort" },
            ("target_family", Some("unix")) => true,
            ("target_family", Some(_)) => false,
            ("target_os", Some("linux")) => true,
            ("target_os", Some(_)) => false,
            ("target_arch", Some(v)) => v == std::env::consts::ARCH,
            ("target_pointer_width", Some("64")) => true,
            ("target_pointer_width", Some(_)) => false,
            ("target_endian", Some("little")) => true,
            ("target_endian", Some(_)) => false,
            ("target_env", Some("gnu")) => true,
            ("target_env", Some(_)) => false,
            ("target_abi", Some("")) => true,
            ("target_abi", Some(_)) => false,
            ("target_vendor", Some("unknown")) => true,
            ("target_vendor", Some(_)) => false,
            ("target_has_atomic", Some(v)) => matches!(v, "8" | "16" | "32" | "64" | "ptr"),
            ("target_has_atomic_primitive_alignment", Some(v)) => matches!(v, "8" | "16" | "32" | "64" | "ptr"),
            ("target_feature", Some(v)) => std::env::consts::ARCH == "x86_64" && matches!(v, "fxsr" | "sse" | "sse2"),
            ("feature", Some(_)) => false,
            _ => false,
        }
    }

    /// The hash of these facts for the expansion cache key (ARCH 6.5).
    pub fn hash(&self) -> u64 {
        let mut h = crate::intern::FxHasher::default();
        self.test.hash(&mut h);
        self.debug_assertions.hash(&mut h);
        "host-unix-linux".hash(&mut h);
        for (n, v) in &self.facts {
            n.hash(&mut h);
            v.hash(&mut h);
        }
        std::hash::Hasher::finish(&h)
    }
}

/// Evaluates the trees inside `cfg(...)` / `#[cfg(...)]`: `all`, `any`,
/// `not`, `name`, and `name = "value"` forms, comma-separated.
/// A shape this does not understand is an error, never a guess.
pub fn eval_cfg(trees: &[Tt], env: &CfgEnv, st: &impl CfgRead, span: Span) -> Result<bool, Diag> {
    let mut i = 0;
    let value = cfg_expr(trees, &mut i, env, st)?;
    if i != trees.len() {
        return Err(err(C_CALL, span, "invalid cfg expression", "Check the cfg syntax."));
    }
    Ok(value)
}

/// What cfg evaluation needs from the expander: identifier and string
/// text for the atoms it meets.
pub trait CfgRead {
    fn ident_text(&self, tok: Tok) -> Option<String>;
    fn string_text(&self, tok: Tok) -> Option<String>;
}

/// The token of a cfg value: a literal, also one a macro passed in an
/// `expr` or `literal` fragment (`target_has_atomic = $size`, as serde's
/// `atomic_impl!` writes it), which rustc reads as the literal.
fn cfg_value_tok(tree: Option<&Tt>) -> Option<crate::lexer::Token> {
    match tree? {
        Tt::Tok(t) => Some(*t),
        Tt::Frag(FragKind::Expr | FragKind::Expr2021 | FragKind::Literal, inner, _) if inner.len() == 1 => cfg_value_tok(inner.first()),
        _ => None,
    }
}

fn cfg_expr(trees: &[Tt], i: &mut usize, env: &CfgEnv, st: &impl CfgRead) -> Result<bool, Diag> {
    let span = trees.get(*i).map_or(Span::default(), |t| t.span());
    let Some(name_tok) = tok_at(trees, *i) else {
        return Err(err(C_CALL, span, "invalid cfg expression", "Check the cfg syntax."));
    };
    let Some(name) = st.ident_text(name_tok.tok) else {
        return Err(err(C_CALL, span, "invalid cfg expression", "Check the cfg syntax."));
    };
    *i += 1;
    if let Some(d) = crate::resolve::cfg::unstable_cfg(&name, name_tok.span) {
        return Err(d);
    }
    match name.as_str() {
        "all" | "any" | "not" => {
            let Some(Tt::Delim(Delim::Paren, inner, _)) = trees.get(*i) else {
                return Err(err(C_CALL, span, format!("`cfg({name})` needs ( ... )"), "Write the cfg items in parentheses."));
            };
            let inner = inner.clone();
            *i += 1;
            let mut values = Vec::new();
            let mut j = 0;
            while j < inner.len() {
                values.push(cfg_expr(&inner, &mut j, env, st)?);
                if tok_at(&inner, j).map(|t| t.tok) == Some(Tok::Comma) {
                    j += 1;
                } else if j != inner.len() {
                    return Err(err(C_CALL, span, "invalid cfg expression", "Check the cfg syntax."));
                }
            }
            Ok(match name.as_str() {
                // Empty all() is true and empty any() is false, as in rustc.
                "all" => values.iter().all(|v| *v),
                "any" => values.iter().any(|v| *v),
                _ => values.len() == 1 && !values[0],
            })
        }
        _ => {
            if tok_at(trees, *i).map(|t| t.tok) == Some(Tok::Eq) {
                let value = match cfg_value_tok(trees.get(*i + 1)) {
                    Some(t) => st.string_text(t.tok),
                    None => None,
                };
                let Some(value) = value else {
                    return Err(err(C_CALL, span, "cfg values must be string literals", "Write `name = \"value\"`."));
                };
                *i += 2;
                Ok(env.name_is(&name, Some(&value)))
            } else {
                Ok(env.name_is(&name, None))
            }
        }
    }
}

/// Splits call argument trees at top-level commas. A trailing comma's
/// empty final piece is dropped, as in a call's own grammar.
pub fn split_args(trees: &[Tt]) -> Vec<Vec<Tt>> {
    let mut parts: Vec<Vec<Tt>> = vec![Vec::new()];
    for tree in trees {
        if tree.is_tok(Tok::Comma) {
            parts.push(Vec::new());
        } else {
            parts.last_mut().unwrap().push(tree.clone());
        }
    }
    if parts.len() > 1 && parts.last().is_some_and(|p| p.is_empty()) {
        parts.pop();
    }
    if parts.len() == 1 && parts[0].is_empty() {
        return Vec::new();
    }
    parts
}

/// The trees of one argument with fragments unwrapped one level when
/// the whole argument is a single fragment.
fn unwrap_frag(trees: &[Tt]) -> &[Tt] {
    match trees {
        [Tt::Frag(_, inner, _)] => inner,
        _ => trees,
    }
}

/// The string value of an argument that is one string literal, with its
/// span (the span builtins use for errors about the path or value).
fn literal_string(st: &Expander, trees: &[Tt]) -> Option<(String, Span)> {
    match unwrap_frag(trees) {
        [Tt::Tok(t)] => match t.tok {
            Tok::Str(i, _) => st.strings.get(i as usize).map(|s| (s.clone(), t.span)),
            _ => None,
        },
        _ => None,
    }
}

/// Reads a file for an `include` family macro, relative to the
/// directory of the file being expanded (ARCH 6.4): the filesystem
/// path, never the shown `file!` form, which for a Cargo crate is
/// workspace-relative and does not open from an arbitrary cwd. An
/// absolute `rel` (the `concat!(env!("OUT_DIR"), ...)` form) replaces
/// the base, as `Path::join` does. Returns the resolved path and bytes.
fn read_include(st: &mut Expander, rel: &str, span: Span) -> Result<(std::path::PathBuf, Vec<u8>), Diag> {
    let base = st.cur_real.parent().map_or_else(|| std::path::PathBuf::from("."), |p| p.to_path_buf());
    let path = base.join(rel);
    match std::fs::read(&path) {
        Ok(bytes) => {
            st.read_dep_file(&path, &bytes);
            Ok((path, bytes))
        }
        Err(_) => Err(err(
            C_INCLUDE,
            span,
            format!("include file `{}` was not found", path.display()),
            "Check the path. It is read relative to the current file.",
        )),
    }
}

/// The text of one token for `stringify!`. Written tokens print as
/// written. Literals carry their written text (`lexer::lit_text`), in
/// any file. Raw identifiers and lifetimes keep `r#`: the source slice at
/// the token's span holds that text, and the guards keep a slice from a
/// different file (an included file's tokens after the swap back) from
/// leaking in, by checking it against the token's name.
pub(super) fn stringify_tok_text(st: &Expander, t: &Token) -> String {
    let plain = tok_text(&t.tok, &st.strings, st.ctx.interner);
    let span = t.span;
    let slice = st.cur_src.get(span.lo as usize..span.hi as usize);
    match t.tok {
        // `$crate` from a macro body transcribes to one `crate` token
        // whose span starts at the `$`; the text at its span names it.
        Tok::Crate if span.ctxt != crate::diag::CtxtId::ROOT => {
            if st.cur_src.get(span.lo as usize..span.lo as usize + 6) == Some("$crate") {
                return "$crate".to_string();
            }
            plain
        }
        Tok::Ident(_) | Tok::Reserved(_) => match slice {
            Some(s) if s == plain || s.strip_prefix("r#") == Some(plain.as_str()) => s.to_string(),
            _ => plain,
        },
        // A raw lifetime keeps its `r#` (`'r#fn`).
        Tok::Lifetime(_) => match slice {
            Some(s) if s.strip_prefix("'r#") == plain.strip_prefix('\'') => s.to_string(),
            _ => plain,
        },
        _ => plain,
    }
}

/// The value of `name` in this process's env (ARCH 6.4): what `env!` reads when the request
/// carries no client env (`ClientView::PROCESS`: one-shot and front image builds, std loading,
/// tests). Each var is read once and kept: this process never sets its env, so the answers are
/// those of a snapshot at start, and only the vars read are held (a front image save writes
/// every live heap block, so no copy of the whole env may live in the process). The builtin and
/// the stale-deps check both read through `ClientView::env_var`, so a recorded env dependency is
/// judged against the same env it was expanded under.
pub fn compile_env(name: &str) -> Option<String> {
    static READ: std::sync::OnceLock<std::sync::Mutex<crate::intern::FxMap<String, Option<String>>>> = std::sync::OnceLock::new();
    let mut read = READ.get_or_init(Default::default).lock().unwrap_or_else(|e| e.into_inner());
    read.entry(name.to_string()).or_insert_with(|| std::env::var(name).ok()).clone()
}

/// Renders trees the way `stringify!` does. Spacing follows rustc's
/// token stream printer: a space where the source had a gap, except
/// never before `,` `;` `)` `]`, never after `(` `[`, never around
/// `.`, and never before a call or index group. Braces keep their
/// source gaps (`{ a; b }` but `{b}`); an empty brace group is `{}`. A token a macro body produced
/// (non-root context) prints alone, with a space on each side the
/// rules above do not already close: its source gaps were in the
/// definition, not at the call site (`$crate :: x`, `a - b - c`).
pub fn stringify_trees(st: &Expander, trees: &[Tt]) -> String {
    #[derive(Clone, Copy)]
    enum Kind {
        Tok(Tok),
        Open(Delim),
        Close(Delim),
    }
    struct Piece {
        text: String,
        lo: u32,
        hi: u32,
        file: crate::diag::FileId,
        ctxt: crate::diag::CtxtId,
        kind: Kind,
    }
    fn go(st: &Expander, trees: &[Tt], out: &mut Vec<Piece>) {
        for tree in trees {
            match tree {
                Tt::Tok(t) => out.push(Piece {
                    text: stringify_tok_text(st, t),
                    lo: t.span.lo,
                    hi: t.span.hi,
                    file: t.span.file,
                    ctxt: t.span.ctxt,
                    kind: Kind::Tok(t.tok),
                }),
                Tt::Delim(d, inner, span) => {
                    let (open, close) = match d {
                        Delim::Paren => ("(", ")"),
                        Delim::Bracket => ("[", "]"),
                        Delim::Brace => ("{", "}"),
                    };
                    out.push(Piece {
                        text: open.to_string(),
                        lo: span.lo,
                        hi: span.lo + 1,
                        file: span.file,
                        ctxt: span.ctxt,
                        kind: Kind::Open(*d),
                    });
                    go(st, inner, out);
                    // A group's span covers both delimiters; a span
                    // that only names the opener (a synthetic group)
                    // counts the closer as right after the last piece.
                    let (lo, hi) = if span.hi > span.lo + 1 {
                        (span.hi - 1, span.hi)
                    } else {
                        let lo = out.last().map_or(span.hi, |p| p.hi);
                        (lo, lo + 1)
                    };
                    out.push(Piece { text: close.to_string(), lo, hi, file: span.file, ctxt: span.ctxt, kind: Kind::Close(*d) });
                }
                Tt::Frag(_, inner, _) => go(st, inner, out),
            }
        }
    }
    fn space_between(prev: &Piece, cur: &Piece) -> bool {
        match cur.kind {
            // A doc comment's literal always follows its `=` with a
            // space. The lexer tiles the synthetic spans over the
            // comment's bytes, and a very short comment (`///` alone)
            // has no byte left to carry that gap.
            Kind::Tok(Tok::DocStr(_)) if matches!(prev.kind, Kind::Tok(Tok::Eq)) => return true,
            Kind::Tok(Tok::Comma | Tok::Semi | Tok::Dot) => return false,
            Kind::Close(Delim::Paren | Delim::Bracket) => return false,
            // An empty brace group prints `{}`, whatever its source gap.
            Kind::Close(Delim::Brace) if matches!(prev.kind, Kind::Open(Delim::Brace)) => return false,
            Kind::Open(Delim::Paren | Delim::Bracket) => {
                // A call, index, or macro group hugs its head.
                let hugs = matches!(
                    prev.kind,
                    Kind::Close(_)
                        | Kind::Tok(
                            Tok::Ident(_)
                                | Tok::Reserved(_)
                                | Tok::SelfUpper
                                | Tok::SelfLower
                                | Tok::Int(..)
                                | Tok::Float(_)
                                | Tok::Str(..)
                                | Tok::DocStr(_)
                                | Tok::Char(..)
                                | Tok::PathSep
                                | Tok::Bang
                                | Tok::Gt
                        )
                );
                if hugs {
                    return false;
                }
            }
            _ => {}
        }
        match prev.kind {
            Kind::Tok(Tok::Dot) => return false,
            // A `$` glues only to the name it was written against in
            // the same template (`$y` kept as tokens). A `$` a
            // repetition inserts as its separator stands alone
            // (`a $ b`), like every other template token.
            Kind::Tok(Tok::Dollar) if cur.ctxt == prev.ctxt && cur.file == prev.file && cur.lo == prev.hi => return false,
            Kind::Open(Delim::Paren | Delim::Bracket) => return false,
            _ => {}
        }
        if prev.ctxt != crate::diag::CtxtId::ROOT || cur.ctxt != crate::diag::CtxtId::ROOT {
            return true;
        }
        cur.file != prev.file || cur.lo > prev.hi
    }
    let mut pieces = Vec::new();
    go(st, trees, &mut pieces);
    let mut text = String::new();
    let mut prev: Option<&Piece> = None;
    for piece in &pieces {
        if let Some(prev) = prev
            && space_between(prev, piece)
        {
            text.push(' ');
        }
        text.push_str(&piece.text);
        prev = Some(piece);
    }
    text
}

/// The message `assert_message` gives an `assert!(cond)` whose panic text
/// lust cannot print as rustc does (rustc breaks it over lines, or the
/// condition holds an item). In a const context the text is never printed
/// (a true condition passes, a false one is a compile error either way),
/// so only lowering a runtime body rejects it (`lower`, L0809).
pub const ASSERT_TEXT_UNKNOWN: &str = "\u{1}lust: an assert! text rustc prints over lines\u{1}";

/// For `assert!(cond)` with no message: the trees `, "{}", "assertion
/// failed: <cond>"` to append to its expanded arguments, so the panic
/// prints rustc's text (see `assert_msg`). The text goes in as an
/// argument, never as the format string, so braces in it stay literal.
/// Empty when the call has a message of its own. When rustc prints the
/// condition over several lines (`assert_msg::cond_text`), the argument
/// is `ASSERT_TEXT_UNKNOWN`.
pub fn assert_message(st: &mut Expander, inner: &[Tt], span: Span) -> Result<Vec<Tt>, Diag> {
    let args = split_args(inner);
    if args.len() != 1 {
        return Ok(Vec::new());
    }
    let text = match super::assert_msg::assert_cond_text(st, &args[0]) {
        Some(cond) => format!("assertion failed: {cond}"),
        None => ASSERT_TEXT_UNKNOWN.to_string(),
    };
    let comma = Tt::Tok(Token { tok: Tok::Comma, span });
    Ok(vec![comma.clone(), st.str_tree("{}", span), comma, st.str_tree(&text, span)])
}

/// The reject for an `assert!(cond)` whose panic text rustc breaks over
/// several lines (more than 78 bytes, or a block with an item).
pub fn assert_text_too_long(span: Span) -> Diag {
    err(
        C_UNSUPPORTED,
        span,
        "`assert!` with no message on a long or item-holding condition is not supported yet",
        "Add a message: assert!(cond, \"...\"), or split the condition.",
    )
}

/// Expands one builtin macro call. `name` has no `!` and satisfied
/// `is_token_builtin`. The walk re-walks output, so nested macro calls
/// a builtin writes or forwards need no chase here, except where a
/// builtin must read a literal its argument expands to.
pub fn expand_builtin(st: &mut Expander, name: &str, call: &Call, depth: u32) -> Result<Vec<Tt>, Diag> {
    let span = call.span;
    let bad = |msg: String| err(C_CALL, span, msg, format!("Check the arguments to {name}!."));
    match name {
        "stringify" => {
            let text = stringify_trees(st, &call.inner);
            Ok(vec![st.str_tree(&text, span)])
        }
        "cfg" => {
            let on = eval_cfg(&call.inner, &st.ctx.cfg, st, span)?;
            Ok(vec![Tt::Tok(Token { tok: if on { Tok::True } else { Tok::False }, span })])
        }
        "line" | "column" => {
            st.read_dep_position();
            expect_args(name, call, 0)?;
            let site = crate::diag::call_site_span(span);
            let (line, col) = st.line_col(site);
            let value = if name == "line" { line } else { col };
            Ok(vec![Tt::Tok(Token { tok: Tok::Int(value as u128, Some(crate::lexer::IntSuffix::U32), None), span })])
        }
        "file" => {
            expect_args(name, call, 0)?;
            let file = st.read_dep_shown();
            Ok(vec![st.str_tree(&file, span)])
        }
        "module_path" => {
            expect_args(name, call, 0)?;
            let path = st.module_path_text();
            Ok(vec![st.str_tree(&path, span)])
        }
        "env" | "option_env" => {
            let args = split_args(&call.inner);
            if args.len() != 1 {
                return Err(bad(format!("{name}! takes one string literal")));
            }
            let expanded = st.expand_more(args.into_iter().next().unwrap(), depth)?;
            let Some((var, _)) = literal_string(st, &expanded) else {
                return Err(bad(format!("{name}! takes one string literal")));
            };
            let value = st.env_lookup(&var);
            st.read_dep_env(&var, value.as_deref());
            match (name, value) {
                ("env", Some(v)) => Ok(vec![st.str_tree(&v, span)]),
                ("env", None) => Err(err(
                    C_CALL,
                    span,
                    format!("environment variable `{var}` not defined at compile time"),
                    "Set the variable, or use option_env! and handle None.",
                )),
                (_, Some(v)) => {
                    let inner = st.str_tree(&v, span);
                    let some = st.ident_tree("Some", span);
                    Ok(vec![some, Tt::Delim(Delim::Paren, vec![inner], span)])
                }
                // `None::<&str>`, as rustc types it, so `{:?}` of a bare `option_env!` checks.
                (_, None) => {
                    let tok = |tok| Tt::Tok(Token { tok, span });
                    let (none, s) = (st.ident_tree("None", span), st.ident_tree("str", span));
                    Ok(vec![none, tok(Tok::PathSep), tok(Tok::Lt), tok(Tok::Amp), s, tok(Tok::Gt)])
                }
            }
        }
        "concat" => {
            let mut text = String::new();
            for arg in split_args(&call.inner) {
                let expanded = st.expand_more(arg, depth)?;
                let Some(part) = concat_value(st, &expanded) else {
                    return Err(bad("concat! arguments must be literals".to_string()));
                };
                text.push_str(&part);
            }
            Ok(vec![st.str_tree(&text, span)])
        }
        "include_str" | "include_bytes" | "include" => include_macro(st, name, call, depth),
        "compile_error" => {
            let args = split_args(&call.inner);
            let msg = if args.len() == 1 {
                literal_string(st, &args[0]).map(|(s, _)| s).unwrap_or_else(|| "compile_error!".to_string())
            } else {
                "compile_error!".to_string()
            };
            Err(err(C_CALL, span, msg, "This code does not compile on purpose when this cfg holds."))
        }
        "matches" => matches_macro(st, call),
        "debug_assert" | "debug_assert_eq" | "debug_assert_ne" => {
            if !st.ctx.cfg.debug_assertions {
                let _ = call;
                return Ok(vec![Tt::Delim(Delim::Brace, Vec::new(), span)]);
            }
            let plain = name.strip_prefix("debug_").unwrap_or(name).to_string();
            let mut out = vec![st.ident_tree(&plain, span), Tt::Tok(Token { tok: Tok::Bang, span })];
            // The message text comes from the condition as written.
            let msg = if plain == "assert" { assert_message(st, &call.inner, span)? } else { Vec::new() };
            let mut inner = st.expand_more(call.inner.clone(), depth)?;
            inner.extend(msg);
            out.push(Tt::Delim(Delim::Paren, inner, span));
            Ok(out)
        }
        "unimplemented" => {
            // `panic!` with rustc's text: "not implemented", then `: ` and
            // the caller's format string when there is one.
            let mut out = vec![st.ident_tree("panic", span), Tt::Tok(Token { tok: Tok::Bang, span })];
            let expanded = st.expand_more(call.inner.clone(), depth)?;
            let args = split_args(&expanded);
            let mut inner = Vec::new();
            if let Some(first) = args.first() {
                let Some((text, lit)) = literal_string(st, first) else {
                    return Err(bad("unimplemented! takes a format string literal".into()));
                };
                inner.push(st.str_tree(&format!("not implemented: {text}"), lit));
                for a in &args[1..] {
                    inner.push(Tt::Tok(Token { tok: Tok::Comma, span }));
                    inner.extend(a.iter().cloned());
                }
            } else {
                inner.push(st.str_tree("not implemented", span));
            }
            out.push(Tt::Delim(Delim::Paren, inner, span));
            Ok(out)
        }
        "write" | "writeln" => write_macro(st, name == "writeln", call),
        "dbg" => dbg_macro(st, call),
        "thread_local" => thread_local_macro(st, call, depth),
        "pin" => {
            let mut tpl = st.lex_template("::std::pin::Pin::new_unchecked(&mut (__lust_e))", span);
            tpl = splice_placeholders(tpl, "__lust_e", &call.inner, st.ctx.interner);
            Ok(tpl)
        }
        _ => Err(err(C_UNSUPPORTED, span, format!("`{name}!` is not supported yet"), "Rewrite this part with the supported subset.")),
    }
}

fn expect_args(name: &str, call: &Call, n: usize) -> Result<(), Diag> {
    if split_args(&call.inner).len() == n {
        Ok(())
    } else {
        Err(err(C_CALL, call.span, format!("`{name}!` takes {n} argument(s)"), "Check the call."))
    }
}

/// The text one numeric literal stands for in `concat!`: rustc prints the
/// value with no suffix. Integers print in decimal; floats keep their
/// written digits (`1e3` stays `1e3`, `2.0` stays `2.0`) minus the suffix
/// and digit separators.
fn concat_number(st: &Expander, tok: Tok) -> Option<String> {
    match tok {
        Tok::Int(v, ..) => Some(v.to_string()),
        Tok::Float(i) => {
            let text = st.strings.get(i as usize)?;
            let text = text.strip_suffix("f32").or_else(|| text.strip_suffix("f64")).unwrap_or(text);
            Some(text.replace('_', ""))
        }
        _ => None,
    }
}

/// The text one `concat!` argument stands for, when it is a literal.
fn concat_value(st: &Expander, trees: &[Tt]) -> Option<String> {
    let trees = unwrap_frag(trees);
    if let [Tt::Tok(neg), Tt::Tok(num)] = trees
        && neg.tok == Tok::Minus
    {
        return concat_number(st, num.tok).map(|n| format!("-{n}"));
    }
    let [Tt::Tok(t)] = trees else { return None };
    Some(match t.tok {
        Tok::Str(i, _) => st.strings.get(i as usize)?.clone(),
        Tok::Char(c, _) => c.to_string(),
        Tok::Int(..) | Tok::Float(_) => concat_number(st, t.tok)?,
        Tok::True => "true".to_string(),
        Tok::False => "false".to_string(),
        _ => return None,
    })
}

/// The `include!` family (ARCH 6.4): files read at expand time.
fn include_macro(st: &mut Expander, name: &str, call: &Call, depth: u32) -> Result<Vec<Tt>, Diag> {
    let span = call.span;
    let args = split_args(&call.inner);
    if args.len() != 1 {
        return Err(err(C_CALL, span, format!("{name}! takes one path"), "Write one string literal path."));
    }
    let expanded = st.expand_more(args.into_iter().next().unwrap(), depth)?;
    let Some((rel, rel_span)) = literal_string(st, &expanded) else {
        return Err(err(C_CALL, span, format!("{name}! takes one path"), "Write one string literal path."));
    };
    let (path, bytes) = read_include(st, &rel, rel_span)?;
    match name {
        "include_str" => {
            let text = String::from_utf8(bytes).map_err(|_| {
                err(C_CALL, rel_span, format!("`{}` is not valid UTF-8", path.display()), "Use include_bytes! for byte data.")
            })?;
            Ok(vec![st.str_tree(&text, span)])
        }
        // The file's bytes as a byte string literal: `&'static [u8; N]`,
        // as rustc types `include_bytes!`, for any data (W-CHECK-G3).
        "include_bytes" => Ok(vec![st.byte_str_tree(&bytes, span)]),
        _ => {
            let text = String::from_utf8(bytes)
                .map_err(|_| err(C_CALL, rel_span, format!("`{}` is not valid UTF-8", path.display()), "Rust source must be UTF-8."))?;
            let file = crate::diag::FileId(0);
            let trees = st.lex_file_trees(&text, file)?;
            // Outside an item list rustc reads the file as one expression
            // ("include macro expected single expression in source").
            if !st.items_call
                && (super::starts_item(&trees, st.ctx.interner)
                    || super::macro_rules_at(&trees, 0, st.ctx.interner).is_some()
                    || trees.iter().any(|t| t.is_tok(Tok::Semi)))
            {
                return Err(err(
                    C_CALL,
                    span,
                    "include! here takes a file that holds one expression",
                    "Include items at item level, or make the file one expression.",
                ));
            }
            let old_file = std::mem::replace(&mut st.cur_file, path.to_string_lossy().to_string());
            let old_real = std::mem::replace(&mut st.cur_real, path.clone());
            let old_src = std::mem::replace(&mut st.cur_src, text);
            let expanded = st.expand_list(trees, depth + 1, true, false, 0);
            st.cur_file = old_file;
            st.cur_real = old_real;
            st.cur_src = old_src;
            expanded
        }
    }
}

/// `matches!(expr, pat if guard)` in its rustc shape.
fn matches_macro(st: &mut Expander, call: &Call) -> Result<Vec<Tt>, Diag> {
    let span = call.span;
    // Split once, at the first top-level comma: before it the value,
    // after it the pattern (with any `if` guard as written).
    let Some(comma) = call.inner.iter().position(|t| t.is_tok(Tok::Comma)) else {
        return Err(err(C_CALL, span, "matches! takes a value and a pattern", "Write matches!(value, pattern)."));
    };
    let value = call.inner[..comma].to_vec();
    let mut pat = call.inner[comma + 1..].to_vec();
    if matches!(pat.last(), Some(Tt::Tok(t)) if t.tok == Tok::Comma) {
        pat.pop();
    }
    // core's matches! takes `$pattern:pat`, and that fragment cannot
    // begin with `..=` (rustc: "no rules expected `..=`").
    if let Some(Tt::Tok(t)) = pat.first()
        && t.tok == Tok::DotDotEq
    {
        return Err(err(C_CALL, t.span, "no rules expected `..=` in matches!", "Put the pattern in parentheses: `(..=0)`."));
    }
    let mut tpl = st.lex_template("match __lust_v { __lust_p => true, _ => false }", span);
    tpl = splice_placeholders(tpl, "__lust_v", &value, st.ctx.interner);
    tpl = splice_placeholders(tpl, "__lust_p", &pat, st.ctx.interner);
    Ok(tpl)
}

/// `write!` and `writeln!` in their rustc shape:
/// `dst.write_fmt(format_args!(...))`. `format_args!` stays for the
/// parser until its `Arguments` type lands with source std (6.4).
fn write_macro(st: &mut Expander, newline: bool, call: &Call) -> Result<Vec<Tt>, Diag> {
    let span = call.span;
    let Some(comma) = call.inner.iter().position(|t| t.is_tok(Tok::Comma)) else {
        // writeln!(dst) alone writes one newline.
        if newline && !call.inner.is_empty() {
            let dst = call.inner.clone();
            let lit = st.str_tree("\n", span);
            return Ok(write_shape(st, span, dst, vec![lit]));
        }
        return Err(err(C_CALL, span, "write! takes a destination and a format string", "Write write!(dst, \"...\", args...)."));
    };
    let dst = call.inner[..comma].to_vec();
    let mut fmt_args: Vec<Tt> = call.inner[comma + 1..].to_vec();
    if newline {
        // The format literal gains the newline, as writeln! writes it.
        let mut done = false;
        for tree in fmt_args.iter_mut() {
            if let Tt::Tok(t) = tree
                && let Tok::Str(i, _) = t.tok
                && let Some(text) = st.strings.get(i as usize).cloned()
            {
                let i2 = st.push_string(format!("{text}\n"));
                t.tok = Tok::Str(i2, None);
                done = true;
                break;
            }
        }
        if !done {
            return Err(err(
                C_UNSUPPORTED,
                span,
                "writeln! with a non-literal format is not supported yet",
                "Write the format as a string literal.",
            ));
        }
    }
    Ok(write_shape(st, span, dst, fmt_args))
}

/// The destination goes in parentheses: rustc's `$dst:expr` is one
/// expression node, so `write!(&mut v, ..)` calls `(&mut v).write_fmt`,
/// not `&mut (v.write_fmt(..))`.
fn write_shape(st: &mut Expander, span: Span, dst: Vec<Tt>, fmt_args: Vec<Tt>) -> Vec<Tt> {
    let mut tpl = st.lex_template("__lust_d.write_fmt(format_args!(__lust_a))", span);
    let dst = vec![Tt::Delim(Delim::Paren, dst, span)];
    tpl = splice_placeholders(tpl, "__lust_d", &dst, st.ctx.interner);
    tpl = splice_placeholders(tpl, "__lust_a", &fmt_args, st.ctx.interner);
    tpl
}

/// `dbg!` in its rustc shape: print the value with `{:#?}` under its
/// file, line, column, and source text, then give the value back.
fn dbg_macro(st: &mut Expander, call: &Call) -> Result<Vec<Tt>, Diag> {
    let span = call.span;
    let site = crate::diag::call_site_span(span);
    let (line, col) = st.line_col(site);
    let file = st.read_dep_shown();
    let prefix = st.str_tree(&format!("[{file}:{line}:{col}]"), span);
    if call.inner.is_empty() {
        return Ok(vec![
            st.ident_tree("eprintln", span),
            Tt::Tok(Token { tok: Tok::Bang, span }),
            Tt::Delim(Delim::Paren, vec![prefix], span),
        ]);
    }
    let args = split_args(&call.inner);
    if args.len() != 1 {
        return Err(err(
            C_UNSUPPORTED,
            span,
            "dbg! with several values needs tuples, which are not supported yet",
            "Call dbg! once per value.",
        ));
    }
    let value = args.into_iter().next().unwrap();
    let name_text = stringify_trees(st, &value);
    let mut tpl =
        st.lex_template("match __lust_v { __lust_t => { eprintln!(\"{} {} = {:#?}\", __lust_at, __lust_n, &__lust_t); __lust_t } }", span);
    let name_tree = vec![st.str_tree(&name_text, span)];
    tpl = splice_placeholders(tpl, "__lust_v", &value, st.ctx.interner);
    tpl = splice_placeholders(tpl, "__lust_at", &[prefix], st.ctx.interner);
    tpl = splice_placeholders(tpl, "__lust_n", &name_tree, st.ctx.interner);
    Ok(tpl)
}

/// `thread_local!` (ARCH 6.4, 7.3). Each declared static becomes two
/// items, as in rustc's own expansion (a `LocalKey` const holding an
/// init fn), but with no `unsafe`:
///
/// ```text
/// #[attrs] #[thread_local!] vis static NAME: T = NAME#init;
/// #[attrs] fn NAME#init() -> T { init }
/// ```
///
/// The marker attribute and the init fn name are spellings no source
/// text can lex, so only this expansion makes them. Collect types the
/// marked static as `LocalKey<T>` and keeps the init fn as the value's
/// lazy initializer. The `const { e }` form gets `#[thread_local!const]`
/// and the block as the init fn body; the checker proves that body is a
/// const initializer (check/tls.rs). Initializers expand one level below
/// `depth`, where rustc expands them.
fn thread_local_macro(st: &mut Expander, call: &Call, depth: u32) -> Result<Vec<Tt>, Diag> {
    let span = call.span;
    let shape = |what: &str| err(C_CALL, span, format!("thread_local! {what}"), "Write `static NAME: Type = init;` in thread_local!.");
    let mut out = Vec::new();
    let trees = &call.inner;
    let mut i = 0;
    while i < trees.len() {
        // One static: attributes, visibility, `static`, name, `:`, type,
        // `=`, init, then `;` or the end of the input.
        let item_start = i;
        while let Some(attr) = attr_at(trees, i, st.ctx.interner) {
            i = attr.end;
        }
        let attrs: Vec<Tt> = trees[item_start..i].to_vec();
        let vis_start = i;
        if tok_at(trees, i).map(|t| t.tok) == Some(Tok::Pub) {
            i += 1;
            if matches!(trees.get(i), Some(Tt::Delim(Delim::Paren, _, _))) {
                i += 1;
            }
        }
        let vis: Vec<Tt> = trees[vis_start..i].to_vec();
        if tok_at(trees, i).map(|t| t.tok) != Some(Tok::Static) {
            return Err(shape("holds static declarations"));
        }
        i += 1;
        let name_tok = match trees.get(i).map(|t| unwrap_frag(std::slice::from_ref(t))) {
            Some([Tt::Tok(t)]) if matches!(t.tok, Tok::Ident(_)) => *t,
            _ => return Err(shape("holds static declarations")),
        };
        let Tok::Ident(name) = name_tok.tok else { unreachable!() };
        i += 1;
        if tok_at(trees, i).map(|t| t.tok) != Some(Tok::Colon) {
            return Err(shape("statics need a type"));
        }
        i += 1;
        // The type runs to the first `=` outside angle brackets, so an
        // associated type binding (`Iterator<Item = u8>`) stays in it.
        let ty_start = i;
        let mut angle = 0i32;
        while let Some(t) = trees.get(i) {
            match t {
                Tt::Tok(t) if t.tok == Tok::Eq && angle == 0 => break,
                Tt::Tok(t) if t.tok == Tok::Lt => angle += 1,
                Tt::Tok(t) if t.tok == Tok::Gt => angle -= 1,
                Tt::Tok(t) if t.tok == Tok::Shr => angle -= 2,
                _ => {}
            }
            i += 1;
        }
        let ty: Vec<Tt> = trees[ty_start..i].to_vec();
        if i >= trees.len() || ty.is_empty() {
            return Err(shape("statics need a type and an initializer"));
        }
        i += 1; // `=`
        let init_start = i;
        while i < trees.len() && !trees[i].is_tok(Tok::Semi) {
            i += 1;
        }
        let init = st.expand_more(trees[init_start..i].to_vec(), depth)?;
        if i < trees.len() {
            i += 1; // `;`
        }
        // `const { e }` and nothing else is the const form; any other
        // initializer (`const { 1 } + 1` included) is a lazy expression.
        // Its block is the init fn body's one expression, so the checker
        // can hand a block with statements to the const evaluator whole.
        let const_block = match init.as_slice() {
            [c, b] if c.is_tok(Tok::Const) => match unwrap_frag(std::slice::from_ref(b)) {
                [Tt::Delim(Delim::Brace, inner, s)] => Some(Tt::Delim(Delim::Brace, vec![Tt::Delim(Delim::Brace, inner.clone(), *s)], *s)),
                _ => None,
            },
            _ => None,
        };
        if init.is_empty() {
            return Err(shape("statics need an initializer"));
        }
        let marker = if const_block.is_some() { crate::parser::TLS_CONST_ATTR } else { crate::parser::TLS_ATTR };
        let init_name = format!("{}#init", st.ctx.interner.get(name));
        let init_fn = Tt::Tok(Token { tok: Tok::Ident(st.ctx.interner.intern(&init_name)), span: name_tok.span });
        // The lazy init in parens: the body re-parses from tokens, and an
        // expression that starts with a block (`if c { 1 } else { 2 } + 1`)
        // would end at the block in statement position.
        let body = const_block.unwrap_or_else(|| Tt::Delim(Delim::Brace, vec![Tt::Delim(Delim::Paren, init, span)], span));
        let mut tpl = st.lex_template("#[__lust_marker] __lust_vis static __lust_name: __lust_ty = __lust_init;", span);
        tpl = splice_placeholders(tpl, "__lust_marker", &[st.ident_tree(marker, span)], st.ctx.interner);
        tpl = splice_placeholders(tpl, "__lust_vis", &vis, st.ctx.interner);
        tpl = splice_placeholders(tpl, "__lust_name", &[Tt::Tok(name_tok)], st.ctx.interner);
        tpl = splice_placeholders(tpl, "__lust_ty", &ty, st.ctx.interner);
        tpl = splice_placeholders(tpl, "__lust_init", std::slice::from_ref(&init_fn), st.ctx.interner);
        out.extend(attrs.iter().cloned());
        out.extend(tpl);
        let mut tpl = st.lex_template("fn __lust_init() -> __lust_ty __lust_body", span);
        tpl = splice_placeholders(tpl, "__lust_init", &[init_fn], st.ctx.interner);
        tpl = splice_placeholders(tpl, "__lust_ty", &ty, st.ctx.interner);
        tpl = splice_placeholders(tpl, "__lust_body", &[body], st.ctx.interner);
        out.extend(attrs);
        out.extend(tpl);
    }
    Ok(out)
}
