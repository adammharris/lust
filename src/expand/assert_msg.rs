// The text rustc puts after "assertion failed: " for `assert!(cond)` with
// no message: `pprust::expr_to_string` of the parsed condition (rustc
// 1.99, rustc_ast_pretty). This file parses the unexpanded condition
// tokens with the grammar rustc uses and prints each node as pprust
// does, so spacing is normalized, trailing commas go, match arms get
// pprust's commas, and a `$e:expr` fragment gets the parentheses pprust
// adds for precedence. A nested macro call prints its tokens with
// rustc's token-stream printer (`print_tts`): a token written in this
// file keeps its source spacing, a token a `macro_rules!` body wrote is
// `Spacing::Alone`, and `space_between` drops the space in `f(`, `x,`,
// `a.b`, `#[`, `m!`.
//
// Each node writes the token stream pprust writes for it (words, breaks,
// and the boxes `ibox`/`cbox` open), and `layout` runs pp.rs's line
// breaker over it, so a text over the 78-byte margin breaks over lines
// as rustc's does. `cond_text` gives None for a form this printer does
// not model: the caller rejects those with L0809, so lust never prints a
// text that differs from rustc's.
use super::*;
use crate::diag::CtxtId;
use crate::lexer::Tok;

/// rustc's pretty printer margin: a longer text breaks over lines.
const MARGIN: usize = 78;

#[derive(Clone, Copy, PartialEq)]
enum K {
    Tok(Tok),
    Open(Delim),
    Close(Delim),
    /// The invisible group rustc wraps around a `$x:expr` (and every other
    /// non-`tt`, non-`ident`, non-`lifetime`) fragment.
    FragOpen(FragKind),
    FragClose,
}

/// One token of the condition.
struct T {
    text: String,
    k: K,
    span: Span,
    /// rustc's `Spacing::Alone` after this token: a token stream prints a
    /// space here when `space_between` agrees. For a `Close` it is the
    /// group's close spacing, for an `Open` brace its open spacing. None
    /// when lust cannot know it (a macro body in another file).
    alone: Option<bool>,
    /// An identifier or lifetime a macro body substituted for one of its
    /// `$x`: rustc prints an `$x:ident` as an always-`Alone` NtIdent and
    /// an `$x:tt` with its source spacing, and lust's trees do not keep
    /// which one it was.
    subst: bool,
}

/// The pretty-printed condition of `assert!(trees)` (expander side), or
/// None when lust cannot print it as rustc does.
pub fn assert_cond_text(st: &Expander, trees: &[Tt]) -> Option<String> {
    let mut toks = Vec::new();
    flatten(st, trees, None, &mut toks);
    print(toks)
}

/// The pretty-printed condition from flat tokens of one file with no
/// macro_rules (each token's text, kind with delimiters as their own
/// tokens, and span), or None as for `assert_cond_text`. The parser calls
/// this for a file the expander skipped.
pub fn cond_text(flat: Vec<(String, Tok, Span)>) -> Option<String> {
    let spans: Vec<Span> = flat.iter().map(|f| f.2).collect();
    let toks = flat
        .into_iter()
        .enumerate()
        .map(|(i, (text, tok, span))| {
            // A gap before the next token is whitespace or a comment.
            let alone = spans.get(i + 1).is_none_or(|n| n.lo > span.hi || n.file != span.file);
            // The parser's text of a raw identifier has no `r#`.
            let raw = matches!(tok, Tok::Ident(_)) && (span.hi - span.lo) as usize == text.len() + 2;
            let text = if raw { format!("r#{text}") } else { text };
            T { text, k: kind_of(tok), span, alone: Some(alone), subst: false }
        })
        .collect();
    print(toks)
}

fn kind_of(tok: Tok) -> K {
    match tok {
        Tok::LParen => K::Open(Delim::Paren),
        Tok::LBracket => K::Open(Delim::Bracket),
        Tok::LBrace => K::Open(Delim::Brace),
        Tok::RParen => K::Close(Delim::Paren),
        Tok::RBracket => K::Close(Delim::Bracket),
        Tok::RBrace => K::Close(Delim::Brace),
        t => K::Tok(t),
    }
}

/// rustc's lexer: the token ending at `pos` is `Alone` when whitespace, a
/// comment, or the end of the file follows it.
fn src_alone(src: &str, pos: u32) -> bool {
    let rest = src.get(pos as usize..).unwrap_or("");
    match rest.chars().next() {
        None => true,
        Some(c) if is_pattern_ws(c) => true,
        Some('/') => rest.starts_with("//") || rest.starts_with("/*"),
        _ => false,
    }
}

/// Rust's Pattern_White_Space (what the lexer skips between tokens).
fn is_pattern_ws(c: char) -> bool {
    matches!(c, '\t' | '\n' | '\u{b}' | '\u{c}' | '\r' | ' ' | '\u{85}' | '\u{200e}' | '\u{200f}' | '\u{2028}' | '\u{2029}')
}

/// The source spacing at `pos` after a delimiter of the group `span` that
/// a macro body wrote (rustc keeps a body's delimiter spacing), when that
/// body is in the file being expanded.
fn def_alone(st: &Expander, span: Span, pos: u32) -> Option<bool> {
    let src = st.cur_src.as_bytes();
    let here = st.root_file == Some(span.file) && st.cur_file == st.ctx.file_path;
    let delims = matches!(
        (src.get(span.lo as usize), span.hi.checked_sub(1).and_then(|h| src.get(h as usize))),
        (Some(b'(' | b'[' | b'{'), Some(b')' | b']' | b'}'))
    );
    (here && delims).then(|| src_alone(&st.cur_src, pos))
}

fn flatten(st: &Expander, trees: &[Tt], group: Option<CtxtId>, out: &mut Vec<T>) {
    for tree in trees {
        match tree {
            Tt::Tok(t) => {
                // A token this file wrote keeps its source spacing; one a
                // macro body wrote is `Alone` (rustc's transcriber).
                let alone = if t.span.ctxt == CtxtId::ROOT { src_alone(&st.cur_src, t.span.hi) } else { true };
                let subst = group.is_some_and(|c| c != t.span.ctxt) && (ident_like(t.tok) || matches!(t.tok, Tok::Lifetime(_)));
                // `>>` and `>>=` are one tree here; the parser sees `>` first.
                let second = match t.tok {
                    Tok::Shr => Some((">", Tok::Gt)),
                    Tok::ShrEq => Some((">=", Tok::Ge)),
                    _ => None,
                };
                if let Some((text, tok)) = second {
                    let lo = t.span.lo + 1;
                    out.push(T { text: ">".into(), k: K::Tok(Tok::Gt), span: Span { hi: lo, ..t.span }, alone: Some(false), subst: false });
                    out.push(T { text: text.into(), k: K::Tok(tok), span: Span { lo, ..t.span }, alone: Some(alone), subst: false });
                    continue;
                }
                out.push(T { text: builtin::stringify_tok_text(st, t), k: K::Tok(t.tok), span: t.span, alone: Some(alone), subst });
            }
            Tt::Delim(d, inner, span) => {
                let root = span.ctxt == CtxtId::ROOT;
                let at = |pos: u32| if root { Some(src_alone(&st.cur_src, pos)) } else { def_alone(st, *span, pos) };
                let (open, close) = match d {
                    Delim::Paren => ("(", ")"),
                    Delim::Bracket => ("[", "]"),
                    Delim::Brace => ("{", "}"),
                };
                let open_alone = if *d == Delim::Brace { at(span.lo + 1) } else { Some(false) };
                out.push(T { text: open.into(), k: K::Open(*d), span: Span { hi: span.lo + 1, ..*span }, alone: open_alone, subst: false });
                flatten(st, inner, Some(span.ctxt), out);
                // rustc's transcriber forces `Alone` after a body's `]`.
                let close_alone = if !root && *d == Delim::Bracket { Some(true) } else { at(span.hi) };
                let lo = span.hi.saturating_sub(1).max(span.lo + 1);
                out.push(T {
                    text: close.into(),
                    k: K::Close(*d),
                    span: Span { lo, hi: lo + 1, ..*span },
                    alone: close_alone,
                    subst: false,
                });
            }
            Tt::Frag(kind, inner, span) if !kind.transparent() => {
                out.push(T { text: String::new(), k: K::FragOpen(*kind), span: *span, alone: Some(false), subst: false });
                flatten(st, inner, None, out);
                out.push(T { text: String::new(), k: K::FragClose, span: *span, alone: Some(true), subst: false });
            }
            Tt::Frag(_, inner, _) => flatten(st, inner, group, out),
        }
    }
}

fn ident_like(t: Tok) -> bool {
    use Tok::*;
    matches!(
        t,
        Ident(_)
            | Reserved(_)
            | As
            | Break
            | Const
            | Continue
            | Else
            | Enum
            | False
            | Fn
            | For
            | If
            | Impl
            | In
            | Let
            | Loop
            | Match
            | Mod
            | Mut
            | Pub
            | Ref
            | Return
            | SelfLower
            | SelfUpper
            | Static
            | Struct
            | Trait
            | True
            | Type
            | Unsafe
            | Use
            | Where
            | While
            | Async
            | Dyn
            | Move
            | Crate
            | Super
            | Extern
            | Await
            | Underscore
    )
}

fn is_punct(t: Tok) -> bool {
    !ident_like(t)
        && !matches!(
            t,
            Tok::Int(..)
                | Tok::Float(_)
                | Tok::Str(..)
                | Tok::DocStr(_)
                | Tok::ByteStr(_)
                | Tok::ByteChar(_)
                | Tok::Char(..)
                | Tok::Lifetime(_)
        )
}

fn print(toks: Vec<T>) -> Option<String> {
    let mut p = P { t: toks, i: 0 };
    let e = p.expr(R::default())?;
    (p.i == p.t.len()).then(|| layout(&e.d))
}

// ---------- the line breaker (rustc_ast_pretty's pp.rs) ----------

/// One token of pprust's stream (pp.rs `Token`).
#[derive(Clone)]
enum Pp {
    Word(String),
    /// A place the line may break: `blank` spaces when it does not, else
    /// `pre` (a trailing comma), a newline, and the box's indent plus
    /// `off`.
    Brk { blank: isize, off: isize, pre: Option<char> },
    /// A box. Its broken lines indent `off` past the enclosing box's
    /// indent; a consistent box takes all of its breaks or none.
    Begin { off: isize, consistent: bool },
    End,
}

/// What pprust writes for one node: words, breaks, and boxes.
#[derive(Clone, Default)]
struct Doc(Vec<Pp>);

impl Doc {
    fn w(s: impl Into<String>) -> Doc {
        Doc(vec![Pp::Word(s.into())])
    }
    fn word(&mut self, s: impl Into<String>) {
        self.0.push(Pp::Word(s.into()));
    }
    fn brk(&mut self, blank: isize, off: isize) {
        self.0.push(Pp::Brk { blank, off, pre: None });
    }
    fn space(&mut self) {
        self.brk(1, 0);
    }
    fn nbsp(&mut self) {
        self.word(" ");
    }
    fn word_space(&mut self, s: &str) {
        self.word(s);
        self.space();
    }
    fn word_nbsp(&mut self, s: &str) {
        self.word(s);
        self.nbsp();
    }
    fn trailing_comma_or_space(&mut self) {
        self.0.push(Pp::Brk { blank: 1, off: 0, pre: Some(',') });
    }
    /// pp's `offset`: the last break's indent moves by `n`.
    fn offset(&mut self, n: isize) {
        if let Some(Pp::Brk { off, .. }) = self.0.last_mut() {
            *off += n;
        }
    }
    fn begin(&mut self, off: isize, consistent: bool) {
        self.0.push(Pp::Begin { off, consistent });
    }
    fn end(&mut self) {
        self.0.push(Pp::End);
    }
    fn add(&mut self, d: Doc) {
        self.0.extend(d.0);
    }
    /// The text with no break taken.
    fn flat(&self) -> String {
        let mut s = String::new();
        for t in &self.0 {
            match t {
                Pp::Word(w) => s.push_str(w),
                Pp::Brk { blank, .. } => s.extend(std::iter::repeat_n(' ', *blank as usize)),
                Pp::Begin { .. } | Pp::End => {}
            }
        }
        s
    }
}

/// pprust's `INDENT_UNIT`.
const INDENT: isize = 4;

fn boxed(off: isize, consistent: bool, d: Doc) -> Doc {
    let mut o = Doc::default();
    o.begin(off, consistent);
    o.add(d);
    o.end();
    o
}

fn ibox(off: isize, d: Doc) -> Doc {
    boxed(off, false, d)
}

/// pprust's `commasep` (and `commasep_exprs`): `a, b` in an inconsistent
/// box, or a consistent one.
fn commasep(items: Vec<Doc>, consistent: bool) -> Doc {
    let mut d = Doc::default();
    d.begin(0, consistent);
    for (n, it) in items.into_iter().enumerate() {
        if n > 0 {
            d.word(",");
            d.space();
        }
        d.add(it);
    }
    d.end();
    d
}

/// `{`, the statements, and `}` of a block whose boxes the caller opened
/// (`bopen` ends the inner one); pprust's `print_block_maybe_unclosed`.
fn bopen_close(d: &mut Doc, stmts: Vec<Doc>) {
    d.word("{");
    d.end();
    let empty = stmts.is_empty();
    for s in stmts {
        d.space();
        d.add(s);
    }
    if !empty {
        d.brk(1, -INDENT);
    }
    d.word("}");
}

const SIZE_INFINITY: isize = 0xffff;
const MIN_SPACE: isize = 60;

#[derive(Clone, Copy)]
enum Frame {
    Fits,
    Broken { indent: usize, consistent: bool },
}

struct Entry {
    tok: Pp,
    size: isize,
}

/// Oppen's printer as pp.rs writes it, over a whole `Doc`.
struct Layout {
    out: String,
    space: isize,
    buf: std::collections::VecDeque<Entry>,
    /// The ring index of `buf[0]`.
    first: usize,
    left_total: isize,
    right_total: isize,
    scan_stack: std::collections::VecDeque<usize>,
    print_stack: Vec<Frame>,
    indent: usize,
    pending: isize,
}

fn layout(d: &Doc) -> String {
    let mut l = Layout {
        out: String::new(),
        space: MARGIN as isize,
        buf: Default::default(),
        first: 0,
        left_total: 0,
        right_total: 0,
        scan_stack: Default::default(),
        print_stack: Vec::new(),
        indent: 0,
        pending: 0,
    };
    for t in &d.0 {
        match t {
            Pp::Word(s) => l.scan_string(s),
            Pp::Brk { .. } => l.scan_break(t.clone()),
            Pp::Begin { .. } => l.scan_begin(t.clone()),
            Pp::End => l.scan_end(),
        }
    }
    if !l.scan_stack.is_empty() {
        l.check_stack(0);
        l.advance_left();
    }
    l.out
}

impl Layout {
    fn push(&mut self, e: Entry) -> usize {
        self.buf.push_back(e);
        self.first + self.buf.len() - 1
    }
    fn at(&mut self, i: usize) -> &mut Entry {
        let j = i - self.first;
        &mut self.buf[j]
    }
    fn scan_begin(&mut self, t: Pp) {
        if self.scan_stack.is_empty() {
            self.left_total = 1;
            self.right_total = 1;
            self.buf.clear();
        }
        let right = self.push(Entry { tok: t, size: -self.right_total });
        self.scan_stack.push_back(right);
    }
    fn scan_end(&mut self) {
        if self.scan_stack.is_empty() {
            self.print_end();
        } else {
            let right = self.push(Entry { tok: Pp::End, size: -1 });
            self.scan_stack.push_back(right);
        }
    }
    fn scan_break(&mut self, t: Pp) {
        if self.scan_stack.is_empty() {
            self.left_total = 1;
            self.right_total = 1;
            self.buf.clear();
        } else {
            self.check_stack(0);
        }
        let Pp::Brk { blank, .. } = t else { unreachable!() };
        let right = self.push(Entry { tok: t, size: -self.right_total });
        self.scan_stack.push_back(right);
        self.right_total += blank;
    }
    fn scan_string(&mut self, s: &str) {
        if self.scan_stack.is_empty() {
            self.print_string(s);
        } else {
            let len = s.len() as isize;
            self.push(Entry { tok: Pp::Word(s.to_string()), size: len });
            self.right_total += len;
            self.check_stream();
        }
    }
    fn check_stream(&mut self) {
        while self.right_total - self.left_total > self.space {
            if *self.scan_stack.front().unwrap() == self.first {
                self.scan_stack.pop_front().unwrap();
                self.buf.front_mut().unwrap().size = SIZE_INFINITY;
            }
            self.advance_left();
            if self.buf.is_empty() {
                break;
            }
        }
    }
    fn advance_left(&mut self) {
        while self.buf.front().unwrap().size >= 0 {
            let left = self.buf.pop_front().unwrap();
            self.first += 1;
            match &left.tok {
                Pp::Word(s) => {
                    self.left_total += s.len() as isize;
                    self.print_string(s);
                }
                Pp::Brk { blank, off, pre } => {
                    self.left_total += blank;
                    self.print_break(*blank, *off, *pre, left.size);
                }
                Pp::Begin { off, consistent } => self.print_begin(*off, *consistent, left.size),
                Pp::End => self.print_end(),
            }
            if self.buf.is_empty() {
                break;
            }
        }
    }
    fn check_stack(&mut self, mut depth: usize) {
        while let Some(&index) = self.scan_stack.back() {
            let right_total = self.right_total;
            let entry = self.at(index);
            match entry.tok {
                Pp::Begin { .. } => {
                    if depth == 0 {
                        break;
                    }
                    self.scan_stack.pop_back().unwrap();
                    self.at(index).size += right_total;
                    depth -= 1;
                }
                Pp::End => {
                    self.scan_stack.pop_back().unwrap();
                    self.at(index).size = 1;
                    depth += 1;
                }
                _ => {
                    self.scan_stack.pop_back().unwrap();
                    self.at(index).size += right_total;
                    if depth == 0 {
                        break;
                    }
                }
            }
        }
    }
    fn print_begin(&mut self, off: isize, consistent: bool, size: isize) {
        if size > self.space {
            self.print_stack.push(Frame::Broken { indent: self.indent, consistent });
            self.indent = (self.indent as isize + off) as usize;
        } else {
            self.print_stack.push(Frame::Fits);
        }
    }
    fn print_end(&mut self) {
        if let Some(Frame::Broken { indent, .. }) = self.print_stack.pop() {
            self.indent = indent;
        }
    }
    fn print_break(&mut self, blank: isize, off: isize, pre: Option<char>, size: isize) {
        let top = self.print_stack.last().copied().unwrap_or(Frame::Broken { indent: 0, consistent: false });
        let fits = match top {
            Frame::Fits => true,
            Frame::Broken { consistent: true, .. } => false,
            Frame::Broken { consistent: false, .. } => size <= self.space,
        };
        if fits {
            self.pending += blank;
            self.space -= blank;
        } else {
            if let Some(c) = pre {
                self.out.push(c);
            }
            self.out.push('\n');
            let indent = self.indent as isize + off;
            self.pending = indent;
            self.space = (MARGIN as isize - indent).max(MIN_SPACE);
        }
    }
    fn print_string(&mut self, s: &str) {
        self.out.extend(std::iter::repeat_n(' ', self.pending.max(0) as usize));
        self.pending = 0;
        self.out.push_str(s);
        self.space -= s.len() as isize;
    }
}

// ---------- the parser ----------

/// rustc's `ExprPrecedence`, lowest first.
#[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
enum Prec {
    Jump,
    Assign,
    Range,
    LOr,
    LAnd,
    Compare,
    BitOr,
    BitXor,
    BitAnd,
    Shift,
    Sum,
    Product,
    Cast,
    Prefix,
    Unambiguous,
}

impl Prec {
    fn next(self) -> Prec {
        use Prec::*;
        match self {
            Jump => Assign,
            Assign => Range,
            Range => LOr,
            LOr => LAnd,
            LAnd => Compare,
            Compare => BitOr,
            BitOr => BitXor,
            BitXor => BitAnd,
            BitAnd => Shift,
            Shift => Sum,
            Sum => Product,
            Product => Cast,
            Cast => Prefix,
            Prefix | Unambiguous => Unambiguous,
        }
    }
}

/// What the printing rules of an enclosing node look at.
#[derive(Clone, Copy, PartialEq)]
enum EK {
    Other,
    /// A plain or labeled block: a match arm body with no comma.
    Block,
    /// `if`, `match`, loops, `unsafe` blocks: `classify::expr_is_complete`.
    BlockLike,
    Cast,
    Let,
    /// A named field (`(s.f)()` needs parens as a callee).
    Field,
    /// A float literal ending in `.`, which takes a space before `.x`.
    DotLit,
    /// `..x` or `..`.
    PrefixRange,
}

/// A block's parts before pprust lays it out: a match arm prints a block
/// body in boxes of its own.
#[derive(Clone)]
struct Blk {
    label: Option<String>,
    unsafe_: bool,
    stmts: Vec<Doc>,
}

struct Ex {
    d: Doc,
    prec: Prec,
    kind: EK,
    /// A `$x:expr` fragment: its parentheses depend on pprust's precedence
    /// fixups, which this printer follows only for plain operands.
    frag: bool,
    /// The parts of a block expression.
    blk: Option<Blk>,
}

impl Ex {
    /// An expression node: pprust prints each in an `ibox(INDENT_UNIT)`.
    fn new(d: Doc, prec: Prec, kind: EK) -> Ex {
        Ex { d: ibox(INDENT, d), prec, kind, frag: false, blk: None }
    }
    fn block_like(&self) -> bool {
        matches!(self.kind, EK::Block | EK::BlockLike)
    }
}

/// Parser restrictions: no struct literal (an `if` condition), and
/// statement position (a block-like expression ends the statement).
#[derive(Clone, Copy, Default)]
struct R {
    no_struct: bool,
    stmt: bool,
}

/// The precedence pprust's fixup gives `e` as a rightmost operand: a
/// closure, a jump with a value, or `..x` extends to the end there, so
/// it counts as a prefix expression.
fn eff(e: &Ex) -> Prec {
    if e.prec == Prec::Jump || e.kind == EK::PrefixRange { Prec::Prefix } else { e.prec }
}

/// A condition (`if`, `while`, `match`, `for`): pprust parenthesizes a
/// jump or closure there, which the source cannot have written bare.
fn cond(e: Ex) -> Option<Doc> {
    (e.prec != Prec::Jump).then_some(e.d)
}

/// `e`, in parentheses when `paren` holds (`print_expr_cond_paren`). A
/// fragment that pprust would print through a statement or jump fixup is
/// not modeled.
fn wrap(e: Ex, paren: bool) -> Option<Doc> {
    if e.frag && (matches!(e.prec, Prec::Jump) || e.kind == EK::PrefixRange) {
        return None;
    }
    Some(if paren {
        let mut d = Doc::w("(");
        d.add(e.d);
        d.word(")");
        d
    } else {
        e.d
    })
}

/// `a op b` as `print_expr_binary` (and assignments) write it.
fn binary(l: Doc, op: &str, r: Doc) -> Doc {
    let mut d = l;
    d.space();
    d.word_space(op);
    d.add(r);
    d
}

#[derive(Clone, Copy)]
enum Op {
    Bin(&'static str, Prec),
    Assign(&'static str),
    Range(&'static str),
    Cast,
}

struct P {
    t: Vec<T>,
    i: usize,
}

impl P {
    fn kind(&self, i: usize) -> Option<K> {
        self.t.get(i).map(|t| t.k)
    }
    fn peek(&self) -> Option<K> {
        self.kind(self.i)
    }
    fn tok(&self) -> Option<Tok> {
        match self.peek() {
            Some(K::Tok(t)) => Some(t),
            _ => None,
        }
    }
    fn tok_at(&self, i: usize) -> Option<Tok> {
        match self.kind(i) {
            Some(K::Tok(t)) => Some(t),
            _ => None,
        }
    }
    fn is(&self, t: Tok) -> bool {
        self.tok() == Some(t)
    }
    fn eat(&mut self, t: Tok) -> bool {
        let hit = self.is(t);
        if hit {
            self.i += 1;
        }
        hit
    }
    fn expect(&mut self, t: Tok) -> Option<()> {
        self.eat(t).then_some(())
    }
    fn open(&self, d: Delim) -> bool {
        self.peek() == Some(K::Open(d))
    }
    fn close(&self, d: Delim) -> bool {
        self.peek() == Some(K::Close(d))
    }
    fn expect_close(&mut self, d: Delim) -> Option<()> {
        self.close(d).then(|| self.i += 1)
    }
    /// The current token's text, consumed.
    fn bump(&mut self) -> String {
        self.i += 1;
        self.t[self.i - 1].text.clone()
    }
    /// True when the token at `i` touches the one after it (`>` `>`).
    fn joint(&self, i: usize) -> bool {
        match (self.t.get(i), self.t.get(i + 1)) {
            (Some(a), Some(b)) => a.span.hi == b.span.lo && a.span.file == b.span.file && a.span.ctxt == b.span.ctxt,
            _ => false,
        }
    }

    /// `a, b, c` up to the close of `d` (consumed), trailing comma allowed.
    /// Returns the items and whether a trailing comma was written.
    fn list<X>(&mut self, d: Delim, mut item: impl FnMut(&mut P) -> Option<X>) -> Option<(Vec<X>, bool)> {
        let mut out = Vec::new();
        let mut trailing = false;
        while !self.close(d) {
            out.push(item(self)?);
            trailing = self.eat(Tok::Comma);
            if !trailing && !self.close(d) {
                return None;
            }
        }
        self.i += 1;
        Some((out, trailing))
    }

    // ---------- expressions ----------

    fn expr(&mut self, r: R) -> Option<Ex> {
        self.assoc(Prec::Jump, r)
    }

    /// The binary operator at the cursor and its token count.
    fn binop(&self) -> Option<(Op, usize)> {
        use Tok::*;
        let op = match self.tok()? {
            Plus => Op::Bin("+", Prec::Sum),
            Minus => Op::Bin("-", Prec::Sum),
            Star => Op::Bin("*", Prec::Product),
            Slash => Op::Bin("/", Prec::Product),
            Percent => Op::Bin("%", Prec::Product),
            Caret => Op::Bin("^", Prec::BitXor),
            Amp => Op::Bin("&", Prec::BitAnd),
            Pipe => Op::Bin("|", Prec::BitOr),
            AndAnd => Op::Bin("&&", Prec::LAnd),
            OrOr => Op::Bin("||", Prec::LOr),
            Shl => Op::Bin("<<", Prec::Shift),
            EqEq => Op::Bin("==", Prec::Compare),
            Ne => Op::Bin("!=", Prec::Compare),
            Lt => Op::Bin("<", Prec::Compare),
            Le => Op::Bin("<=", Prec::Compare),
            Ge => Op::Bin(">=", Prec::Compare),
            Gt if self.joint(self.i) && self.tok_at(self.i + 1) == Some(Gt) => return Some((Op::Bin(">>", Prec::Shift), 2)),
            Gt if self.joint(self.i) && self.tok_at(self.i + 1) == Some(Ge) => return Some((Op::Assign(">>="), 2)),
            Gt => Op::Bin(">", Prec::Compare),
            Eq => Op::Assign("="),
            PlusEq => Op::Assign("+="),
            MinusEq => Op::Assign("-="),
            StarEq => Op::Assign("*="),
            SlashEq => Op::Assign("/="),
            PercentEq => Op::Assign("%="),
            CaretEq => Op::Assign("^="),
            AmpEq => Op::Assign("&="),
            PipeEq => Op::Assign("|="),
            ShlEq => Op::Assign("<<="),
            DotDot => Op::Range(".."),
            DotDotEq => Op::Range("..="),
            As => Op::Cast,
            _ => return None,
        };
        Some((op, 1))
    }

    /// rustc's `parse_expr_assoc_with`: operators of precedence `min` and up.
    fn assoc(&mut self, min: Prec, r: R) -> Option<Ex> {
        let mut lhs = if self.is(Tok::DotDot) || self.is(Tok::DotDotEq) { self.prefix_range(r)? } else { self.unary(r)? };
        loop {
            if r.stmt && lhs.block_like() {
                return Some(lhs);
            }
            let Some((op, n)) = self.binop() else { return Some(lhs) };
            let prec = match op {
                Op::Bin(_, p) => p,
                Op::Assign(_) => Prec::Assign,
                Op::Range(_) => Prec::Range,
                Op::Cast => Prec::Cast,
            };
            if prec < min {
                return Some(lhs);
            }
            self.i += n;
            let r2 = R { stmt: false, ..r };
            lhs = match op {
                Op::Cast => {
                    let ty = self.ty()?;
                    let lp = lhs.prec < Prec::Cast;
                    let l = wrap(lhs, lp)?;
                    Ex::new(binary(l, "as", ty), Prec::Cast, EK::Cast)
                }
                Op::Assign(o) => {
                    let rhs = self.assoc(Prec::Assign, r2)?;
                    let lp = lhs.prec <= Prec::Range;
                    let rp = eff(&rhs) < Prec::Assign;
                    Ex::new(binary(wrap(lhs, lp)?, o, wrap(rhs, rp)?), Prec::Assign, EK::Other)
                }
                Op::Range(o) => {
                    if lhs.prec < Prec::LOr {
                        return None;
                    }
                    let dot = lhs.kind == EK::DotLit;
                    let mut d = wrap(lhs, false)?;
                    if dot {
                        d.word(" ");
                    }
                    d.word(o);
                    if self.range_rhs(r2) {
                        let e = self.assoc(Prec::LOr, r2)?;
                        let p = eff(&e) < Prec::LOr;
                        d.add(wrap(e, p)?);
                    }
                    Ex::new(d, Prec::Range, EK::Other)
                }
                Op::Bin(o, p) => {
                    let comparison = p == Prec::Compare;
                    let rhs = self.assoc(p.next(), r2)?;
                    let mut lp = if comparison { lhs.prec <= p } else { lhs.prec < p };
                    let rp = eff(&rhs) <= p;
                    if lhs.kind == EK::Cast && (o == "<" || o == "<<") || lhs.kind == EK::Let && p > Prec::LAnd {
                        lp = true;
                    }
                    Ex::new(binary(wrap(lhs, lp)?, o, wrap(rhs, rp)?), p, EK::Other)
                }
            };
        }
    }

    /// rustc's `is_at_start_of_range_notation_rhs`.
    fn range_rhs(&self, r: R) -> bool {
        if self.open(Delim::Brace) {
            return !r.no_struct;
        }
        self.can_begin_expr()
    }

    fn can_begin_expr(&self) -> bool {
        use Tok::*;
        match self.peek() {
            Some(K::Open(_)) => true,
            Some(K::FragOpen(k)) => matches!(k, FragKind::Expr | FragKind::Expr2021 | FragKind::Literal | FragKind::Block | FragKind::Path),
            Some(K::Tok(t)) => matches!(
                t,
                Ident(_)
                    | Int(..)
                    | Float(_)
                    | Str(..)
                    | ByteStr(_)
                    | ByteChar(_)
                    | Char(..)
                    | Lifetime(_)
                    | True
                    | False
                    | SelfLower
                    | SelfUpper
                    | Crate
                    | Super
                    | If
                    | Match
                    | Loop
                    | While
                    | For
                    | Unsafe
                    | Move
                    | Return
                    | Break
                    | Continue
                    | Let
                    | Const
                    | Static
                    | Async
                    | Minus
                    | Bang
                    | Star
                    | Amp
                    | AndAnd
                    | Pipe
                    | OrOr
                    | DotDot
                    | DotDotEq
                    | Lt
                    | Shl
                    | PathSep
                    | Pound
            ),
            _ => false,
        }
    }

    fn prefix_range(&mut self, r: R) -> Option<Ex> {
        let o = if self.eat(Tok::DotDot) {
            ".."
        } else {
            self.expect(Tok::DotDotEq)?;
            "..="
        };
        if !self.range_rhs(r) {
            return Some(Ex::new(Doc::w(o), Prec::Range, EK::PrefixRange));
        }
        let e = self.assoc(Prec::LOr, R { stmt: false, ..r })?;
        let p = eff(&e) < Prec::LOr;
        let mut d = Doc::w(o);
        d.add(wrap(e, p)?);
        Some(Ex::new(d, Prec::Range, EK::PrefixRange))
    }

    fn unary(&mut self, r: R) -> Option<Ex> {
        let r2 = R { stmt: false, ..r };
        let op = match self.tok() {
            Some(Tok::Minus) => "-",
            Some(Tok::Bang) => "!",
            Some(Tok::Star) => "*",
            Some(Tok::Amp) => return self.addr_of(r2, false),
            Some(Tok::AndAnd) => return self.addr_of(r2, true),
            _ => {
                let base = self.primary(r)?;
                return self.postfix(base, r);
            }
        };
        self.i += 1;
        let e = self.unary(r2)?;
        let p = eff(&e) < Prec::Prefix;
        let mut d = Doc::w(op);
        d.add(wrap(e, p)?);
        Some(Ex::new(d, Prec::Prefix, EK::Other))
    }

    /// `&x`, `&mut x`, `&raw const x`, `&raw mut x`; `double` for the
    /// `&&` token, two borrows.
    fn addr_of(&mut self, r: R, double: bool) -> Option<Ex> {
        self.i += 1;
        let raw = matches!(self.peek(), Some(K::Tok(Tok::Ident(_))))
            && self.t[self.i].text == "raw"
            && matches!(self.tok_at(self.i + 1), Some(Tok::Const | Tok::Mut));
        let mut d = Doc::w("&");
        if raw {
            self.i += 1;
            d.word_nbsp("raw");
            if self.eat(Tok::Const) {
                d.word_nbsp("const");
            } else {
                self.bump();
                d.word_nbsp("mut");
            }
        } else if self.eat(Tok::Mut) {
            d.word_nbsp("mut");
        }
        let e = self.unary(r)?;
        let p = eff(&e) < Prec::Prefix;
        d.add(wrap(e, p)?);
        let inner = Ex::new(d, Prec::Prefix, EK::Other);
        if !double {
            return Some(inner);
        }
        let mut d = Doc::w("&");
        d.add(inner.d);
        Some(Ex::new(d, Prec::Prefix, EK::Other))
    }

    fn postfix(&mut self, mut e: Ex, r: R) -> Option<Ex> {
        loop {
            if self.eat(Tok::Question) {
                let p = e.prec < Prec::Unambiguous;
                let mut d = wrap(e, p)?;
                d.word("?");
                e = Ex::new(d, Prec::Unambiguous, EK::Other);
            } else if self.is(Tok::Dot) {
                self.i += 1;
                let p = e.prec < Prec::Unambiguous;
                let dot_lit = !p && e.kind == EK::DotLit;
                let mut d = wrap(e, p)?;
                if dot_lit {
                    d.word(" ");
                }
                d.word(".");
                match self.tok()? {
                    Tok::Ident(_) | Tok::Reserved(_) => {
                        if matches!(self.tok(), Some(Tok::Reserved(_))) {
                            return None;
                        }
                        d.word(self.bump());
                        let generics = if self.is(Tok::PathSep) {
                            self.i += 1;
                            let mut g = Doc::w("::");
                            g.add(self.generic_args()?);
                            Some(g)
                        } else {
                            None
                        };
                        if self.open(Delim::Paren) {
                            if let Some(g) = generics {
                                d.add(g);
                            }
                            d.add(self.call_args()?);
                            e = Ex::new(d, Prec::Unambiguous, EK::Other);
                        } else if generics.is_none() {
                            e = Ex::new(d, Prec::Unambiguous, EK::Field);
                        } else {
                            return None;
                        }
                    }
                    Tok::Int(..) | Tok::Float(_) => {
                        d.word(self.bump());
                        e = Ex::new(d, Prec::Unambiguous, EK::Other);
                    }
                    _ => return None,
                }
            } else if self.open(Delim::Paren) && !(r.stmt && e.block_like()) {
                let p = e.kind == EK::Field || e.prec < Prec::Unambiguous || e.block_like();
                let mut d = wrap(e, p)?;
                d.add(self.call_args()?);
                e = Ex::new(d, Prec::Unambiguous, EK::Other);
            } else if self.open(Delim::Bracket) && !(r.stmt && e.block_like()) {
                let p = e.prec < Prec::Unambiguous || e.block_like();
                let mut d = wrap(e, p)?;
                self.i += 1;
                let idx = self.expr(R::default())?;
                self.expect_close(Delim::Bracket)?;
                d.word("[");
                d.add(idx.d);
                d.word("]");
                e = Ex::new(d, Prec::Unambiguous, EK::Other);
            } else {
                return Some(e);
            }
        }
    }

    /// `(a, b)` of a call (`print_call_post`).
    fn call_args(&mut self) -> Option<Doc> {
        self.i += 1;
        let (args, _) = self.list(Delim::Paren, |p| p.expr(R::default()).map(|e| e.d))?;
        let mut d = Doc::w("(");
        d.add(commasep(args, false));
        d.word(")");
        Some(d)
    }

    fn primary(&mut self, r: R) -> Option<Ex> {
        use Tok::*;
        let lit = |s: String| {
            let kind = if s.ends_with('.') { EK::DotLit } else { EK::Other };
            Some(Ex::new(Doc::w(s), Prec::Unambiguous, kind))
        };
        match self.peek()? {
            K::FragOpen(FragKind::Expr | FragKind::Expr2021 | FragKind::Literal) => {
                self.i += 1;
                let mut e = self.expr(R::default())?;
                (self.peek() == Some(K::FragClose)).then_some(())?;
                self.i += 1;
                e.frag = true;
                Some(e)
            }
            K::FragOpen(FragKind::Block) => {
                self.i += 1;
                let b = self.block_expr(None, false)?;
                (self.peek() == Some(K::FragClose)).then_some(())?;
                self.i += 1;
                Some(b)
            }
            K::FragOpen(FragKind::Path) => self.path_like(r),
            K::FragOpen(_) | K::FragClose | K::Close(_) => None,
            K::Open(Delim::Paren) => {
                self.i += 1;
                let (mut items, trailing) = self.list(Delim::Paren, |p| p.expr(R::default()).map(|e| e.d))?;
                let mut d = Doc::w("(");
                if items.len() == 1 && !trailing {
                    d.add(items.pop().unwrap());
                } else {
                    let one = items.len() == 1;
                    d.add(commasep(items, false));
                    if one {
                        d.word(",");
                    }
                }
                d.word(")");
                Some(Ex::new(d, Prec::Unambiguous, EK::Other))
            }
            K::Open(Delim::Bracket) => {
                self.i += 1;
                let mut d = Doc::w("[");
                if self.close(Delim::Bracket) {
                    self.i += 1;
                    d.add(commasep(Vec::new(), false));
                    d.word("]");
                    return Some(Ex::new(ibox(INDENT, d), Prec::Unambiguous, EK::Other));
                }
                let first = self.expr(R::default())?;
                if self.eat(Semi) {
                    let n = self.expr(R::default())?;
                    self.expect_close(Delim::Bracket)?;
                    d.add(first.d);
                    d.word_space(";");
                    d.add(n.d);
                    d.word("]");
                    return Some(Ex::new(ibox(INDENT, d), Prec::Unambiguous, EK::Other));
                }
                let mut items = vec![first.d];
                if self.eat(Comma) {
                    let (rest, _) = self.list(Delim::Bracket, |p| p.expr(R::default()).map(|e| e.d))?;
                    items.extend(rest);
                } else {
                    self.expect_close(Delim::Bracket)?;
                }
                d.add(commasep(items, false));
                d.word("]");
                Some(Ex::new(ibox(INDENT, d), Prec::Unambiguous, EK::Other))
            }
            K::Open(Delim::Brace) => self.block_expr(None, false),
            K::Tok(t) => match t {
                Int(..) | Float(_) | Str(..) | ByteStr(_) | ByteChar(_) | Char(..) | True | False => lit(self.bump()),
                Unsafe if self.kind(self.i + 1) == Some(K::Open(Delim::Brace)) => {
                    self.i += 1;
                    self.block_expr(None, true)
                }
                Lifetime(_) if self.tok_at(self.i + 1) == Some(Colon) => {
                    let label = self.bump();
                    self.i += 1;
                    match self.peek()? {
                        K::Open(Delim::Brace) => self.block_expr(Some(label), false),
                        K::Tok(Loop) => self.loop_expr(Some(label)),
                        K::Tok(While) => self.while_expr(Some(label)),
                        K::Tok(For) => self.for_expr(Some(label)),
                        _ => None,
                    }
                }
                If => self.if_expr(),
                Match => {
                    self.i += 1;
                    let scrut = cond(self.expr(R { no_struct: true, stmt: false })?)?;
                    if !self.open(Delim::Brace) {
                        return None;
                    }
                    self.i += 1;
                    let mut arms = Vec::new();
                    while !self.close(Delim::Brace) {
                        arms.push(self.arm()?);
                    }
                    self.i += 1;
                    let mut d = Doc::default();
                    d.begin(0, true);
                    d.begin(0, false);
                    d.word_nbsp("match");
                    d.add(scrut);
                    d.space();
                    d.word("{");
                    d.end();
                    let empty = arms.is_empty();
                    for a in arms {
                        d.space();
                        d.add(a);
                    }
                    if !empty {
                        d.brk(1, -INDENT);
                    }
                    d.word("}");
                    d.end();
                    Some(Ex::new(d, Prec::Unambiguous, EK::BlockLike))
                }
                Loop => self.loop_expr(None),
                While => self.while_expr(None),
                For => self.for_expr(None),
                Pipe | OrOr | Move => self.closure(r),
                Break => {
                    self.i += 1;
                    let mut d = Doc::w("break");
                    let mut label = false;
                    if matches!(self.tok(), Some(Lifetime(_))) {
                        d.space();
                        d.word(self.bump());
                        label = true;
                    }
                    if self.range_rhs(r) {
                        // `break 'a: loop {}` needs parens rustc would add.
                        if !label && matches!(self.tok(), Some(Lifetime(_))) {
                            return None;
                        }
                        let v = self.expr(R { stmt: false, ..r })?;
                        d.space();
                        d.add(wrap(v, false)?);
                        return Some(Ex::new(d, Prec::Jump, EK::Other));
                    }
                    Some(Ex::new(d, Prec::Unambiguous, EK::Other))
                }
                Continue => {
                    self.i += 1;
                    let mut d = Doc::w("continue");
                    if matches!(self.tok(), Some(Lifetime(_))) {
                        d.space();
                        d.word(self.bump());
                    }
                    Some(Ex::new(d, Prec::Unambiguous, EK::Other))
                }
                Return => {
                    self.i += 1;
                    if self.range_rhs(r) {
                        let v = self.expr(R { stmt: false, ..r })?;
                        let mut d = Doc::w("return");
                        d.word(" ");
                        d.add(wrap(v, false)?);
                        return Some(Ex::new(d, Prec::Jump, EK::Other));
                    }
                    Some(Ex::new(Doc::w("return"), Prec::Unambiguous, EK::Other))
                }
                Let => {
                    self.i += 1;
                    let pat = self.pat(true)?;
                    self.expect(Eq)?;
                    let e = self.assoc(Prec::Compare, R { stmt: false, ..r })?;
                    let p = eff(&e) <= Prec::LAnd;
                    let mut d = Doc::w("let ");
                    d.add(pat);
                    d.space();
                    d.word_space("=");
                    d.add(wrap(e, p)?);
                    Some(Ex::new(d, Prec::Prefix, EK::Let))
                }
                Underscore => {
                    self.i += 1;
                    Some(Ex::new(Doc::w("_"), Prec::Unambiguous, EK::Other))
                }
                Ident(_) | SelfLower | SelfUpper | Super | Crate | PathSep | Lt | Shl => self.path_like(r),
                _ => None,
            },
        }
    }

    /// A block expression at the cursor (`{`), with its label or `unsafe`.
    fn block_expr(&mut self, label: Option<String>, unsafe_: bool) -> Option<Ex> {
        let stmts = self.block()?;
        let blk = Blk { label, unsafe_, stmts };
        let mut d = Doc::default();
        if let Some(l) = &blk.label {
            d.word(l.clone());
            d.word_space(":");
        }
        d.begin(0, true);
        d.begin(0, false);
        if unsafe_ {
            d.word_space("unsafe");
        }
        bopen_close(&mut d, blk.stmts.clone());
        d.end();
        let mut e = Ex::new(d, Prec::Unambiguous, if unsafe_ { EK::BlockLike } else { EK::Block });
        e.blk = Some(blk);
        Some(e)
    }

    fn loop_expr(&mut self, label: Option<String>) -> Option<Ex> {
        self.expect(Tok::Loop)?;
        let stmts = self.block()?;
        let mut d = Doc::default();
        d.begin(0, true);
        d.begin(0, false);
        if let Some(l) = label {
            d.word(l);
            d.word_space(":");
        }
        d.word_nbsp("loop");
        bopen_close(&mut d, stmts);
        d.end();
        Some(Ex::new(d, Prec::Unambiguous, EK::BlockLike))
    }

    fn while_expr(&mut self, label: Option<String>) -> Option<Ex> {
        self.expect(Tok::While)?;
        let c = cond(self.expr(R { no_struct: true, stmt: false })?)?;
        let stmts = self.block()?;
        let mut d = Doc::default();
        if let Some(l) = label {
            d.word(l);
            d.word_space(":");
        }
        d.begin(0, true);
        d.begin(0, false);
        d.word_nbsp("while");
        d.add(c);
        d.space();
        bopen_close(&mut d, stmts);
        d.end();
        Some(Ex::new(d, Prec::Unambiguous, EK::BlockLike))
    }

    fn for_expr(&mut self, label: Option<String>) -> Option<Ex> {
        self.expect(Tok::For)?;
        let pat = self.pat(true)?;
        self.expect(Tok::In)?;
        let iter = cond(self.expr(R { no_struct: true, stmt: false })?)?;
        let stmts = self.block()?;
        let mut d = Doc::default();
        if let Some(l) = label {
            d.word(l);
            d.word_space(":");
        }
        d.begin(0, true);
        d.begin(0, false);
        d.word_nbsp("for");
        d.add(pat);
        d.space();
        d.word_space("in");
        d.add(iter);
        d.space();
        bopen_close(&mut d, stmts);
        d.end();
        Some(Ex::new(d, Prec::Unambiguous, EK::BlockLike))
    }

    /// A path expression, a struct literal, or a macro call.
    fn path_like(&mut self, r: R) -> Option<Ex> {
        let start = self.i;
        let (path, generics) = self.path(true)?;
        if self.is(Tok::Bang) && !generics && matches!(self.kind(self.i + 1), Some(K::Open(_))) {
            self.i += 1;
            return Some(Ex::new(self.mac(path)?, Prec::Unambiguous, EK::Other));
        }
        if self.open(Delim::Brace) && !r.no_struct && self.kind(start) != Some(K::Tok(Tok::Lt)) {
            return Some(Ex::new(self.struct_lit(path)?, Prec::Unambiguous, EK::Other));
        }
        Some(Ex::new(path, Prec::Unambiguous, EK::Other))
    }

    /// `Path { a: 1, b, ..base }` after the path (`print_expr_struct`).
    fn struct_lit(&mut self, path: Doc) -> Option<Doc> {
        self.i += 1;
        let mut fields = Vec::new();
        let mut rest = None;
        while !self.close(Delim::Brace) {
            if self.eat(Tok::DotDot) {
                rest = Some(if self.close(Delim::Brace) { return None } else { self.expr(R::default())?.d });
                break;
            }
            let name = match self.tok()? {
                Tok::Ident(_) | Tok::Int(..) => self.bump(),
                _ => return None,
            };
            let mut f = Doc::default();
            if self.eat(Tok::Colon) {
                f.word(name);
                f.word_nbsp(":");
                f.add(self.expr(R::default())?.d);
            } else {
                // A shorthand field prints its expression, a path.
                f.add(Ex::new(Doc::w(name), Prec::Unambiguous, EK::Other).d);
            }
            fields.push(f);
            if !self.eat(Tok::Comma) && !self.close(Delim::Brace) {
                return None;
            }
        }
        self.expect_close(Delim::Brace)?;
        let mut d = path;
        d.nbsp();
        d.word("{");
        let has_rest = rest.is_some();
        if fields.is_empty() && !has_rest {
            d.word("}");
            return Some(d);
        }
        d.begin(0, true);
        let n = fields.len();
        let empty = fields.is_empty();
        for (i, f) in fields.into_iter().enumerate() {
            if i == 0 {
                d.space();
            }
            d.add(f);
            if i + 1 < n || has_rest {
                d.word_space(",");
            } else {
                d.trailing_comma_or_space();
            }
        }
        if let Some(b) = rest {
            if empty {
                d.space();
            }
            d.word("..");
            d.add(b);
            d.space();
        }
        d.offset(-INDENT);
        d.end();
        d.word("}");
        Some(d)
    }

    fn if_expr(&mut self) -> Option<Ex> {
        self.expect(Tok::If)?;
        let c = cond(self.expr(R { no_struct: true, stmt: false })?)?;
        let stmts = self.block()?;
        let mut d = Doc::default();
        d.begin(0, true);
        d.begin(0, false);
        d.word_nbsp("if");
        d.add(c);
        d.space();
        bopen_close(&mut d, stmts);
        d.end();
        while self.eat(Tok::Else) {
            d.begin(0, true);
            d.begin(0, false);
            let last = !self.is(Tok::If);
            if last {
                d.word(" else ");
            } else {
                self.i += 1;
                let c = cond(self.expr(R { no_struct: true, stmt: false })?)?;
                d.word(" else if ");
                d.add(c);
                d.space();
            }
            bopen_close(&mut d, self.block()?);
            d.end();
            if last {
                break;
            }
        }
        Some(Ex::new(d, Prec::Unambiguous, EK::BlockLike))
    }

    /// One match arm with pprust's comma (`print_arm`).
    fn arm(&mut self) -> Option<Doc> {
        let pat = self.pat(true)?;
        let guard = if self.eat(Tok::If) { Some(self.expr(R::default())?.d) } else { None };
        self.expect(Tok::FatArrow)?;
        let body = self.expr(R { no_struct: false, stmt: true })?;
        if !self.eat(Tok::Comma) && !body.block_like() && !self.close(Delim::Brace) {
            return None;
        }
        let mut d = Doc::default();
        d.begin(INDENT, true);
        d.begin(0, false);
        d.add(pat);
        d.space();
        if let Some(g) = guard {
            d.word_space("if");
            d.add(g);
            d.space();
        }
        d.word_space("=>");
        match body.blk {
            Some(blk) => {
                if let Some(l) = blk.label {
                    d.word(l);
                    d.word_space(":");
                }
                if blk.unsafe_ {
                    d.word_space("unsafe");
                }
                bopen_close(&mut d, blk.stmts);
                if blk.unsafe_ {
                    d.word(",");
                }
            }
            None => {
                d.end();
                d.add(body.d);
                d.word(",");
            }
        }
        d.end();
        Some(d)
    }

    fn closure(&mut self, r: R) -> Option<Ex> {
        let mut d = Doc::default();
        if self.eat(Tok::Move) {
            d.word_space("move");
        }
        let params = if self.eat(Tok::OrOr) {
            Vec::new()
        } else {
            self.expect(Tok::Pipe)?;
            let mut ps = Vec::new();
            while !self.is(Tok::Pipe) {
                let mut pd = self.pat(false)?;
                if self.eat(Tok::Colon) {
                    pd.word(":");
                    pd.space();
                    pd.add(self.ty()?);
                }
                ps.push(ibox(INDENT, pd));
                if !self.eat(Tok::Comma) && !self.is(Tok::Pipe) {
                    return None;
                }
            }
            self.i += 1;
            ps
        };
        d.word("|");
        d.add(commasep(params, false));
        d.word("|");
        if self.eat(Tok::Arrow) {
            let ty = self.ty()?;
            if !self.open(Delim::Brace) {
                return None;
            }
            d.add(ret_ty(ty));
            let b = self.block_expr(None, false)?;
            d.space();
            d.add(b.d);
            return Some(Ex::new(d, Prec::Unambiguous, EK::Other));
        }
        let body = self.expr(R { stmt: false, ..r })?;
        d.space();
        d.add(body.d);
        Some(Ex::new(d, Prec::Jump, EK::Other))
    }

    /// The statements of `{ stmts }` at the cursor.
    fn block(&mut self) -> Option<Vec<Doc>> {
        if !self.open(Delim::Brace) {
            return None;
        }
        self.i += 1;
        let mut stmts = Vec::new();
        while !self.close(Delim::Brace) {
            stmts.push(self.stmt()?);
        }
        self.i += 1;
        Some(stmts)
    }

    /// One statement as `print_stmt` writes it, after its leading break.
    fn stmt(&mut self) -> Option<Doc> {
        use Tok::*;
        match self.peek()? {
            K::Tok(Semi) => {
                self.i += 1;
                return Some(Doc::w(";"));
            }
            K::Tok(Let) => {
                self.i += 1;
                let mut d = Doc::default();
                d.begin(INDENT, false);
                d.word_nbsp("let");
                d.begin(INDENT, false);
                d.add(self.pat(true)?);
                if self.eat(Colon) {
                    d.word_space(":");
                    d.add(self.ty()?);
                }
                d.end();
                if self.eat(Eq) {
                    let init = self.expr(R::default())?;
                    let brace = init.d.flat().ends_with('}');
                    d.nbsp();
                    d.word_space("=");
                    d.add(init.d);
                    if self.eat(Else) {
                        if brace {
                            return None;
                        }
                        d.begin(INDENT, true);
                        d.begin(INDENT, false);
                        d.word(" else ");
                        bopen_close(&mut d, self.block()?);
                        d.end();
                    }
                }
                self.expect(Semi)?;
                d.word(";");
                d.end();
                return Some(d);
            }
            // Items break the line in rustc's printer; attributes are not modeled.
            K::Tok(Fn | Struct | Enum | Impl | Trait | Use | Static | Mod | Type | Extern | Pub | Pound) => return None,
            K::Tok(Const) if self.kind(self.i + 1) != Some(K::Open(Delim::Brace)) => return None,
            _ => {}
        }
        // A macro call statement: `m! { .. }` and `m!(..);` stay statements,
        // which pprust prints with no expression box.
        let start = self.i;
        if matches!(self.tok(), Some(Ident(_) | SelfLower | Super | Crate | PathSep)) {
            let (path, generics) = self.path(true)?;
            if !generics && self.is(Bang) && matches!(self.kind(self.i + 1), Some(K::Open(_))) {
                let brace = self.kind(self.i + 1) == Some(K::Open(Delim::Brace));
                self.i += 1;
                let mut mac = self.mac(path)?;
                if self.eat(Semi) {
                    mac.word(";");
                    return Some(mac);
                }
                if brace && !self.is(Dot) && !self.is(Question) {
                    return Some(mac);
                }
            }
            self.i = start;
        }
        let e = self.expr(R { no_struct: false, stmt: true })?;
        if self.eat(Semi) {
            let mut d = e.d;
            d.word(";");
            return Some(d);
        }
        (self.close(Delim::Brace) || e.block_like()).then_some(e.d)
    }

    // ---------- paths ----------

    /// A path in expression or pattern position (`colons` true: generic
    /// args print as `::<..>`), or in a type (false). Also `<T as Tr>::x`.
    /// Returns the path and whether it holds generic args.
    fn path(&mut self, colons: bool) -> Option<(Doc, bool)> {
        let mut d = Doc::default();
        let mut generics = false;
        if self.peek() == Some(K::FragOpen(FragKind::Path)) {
            self.i += 1;
            let (p, g) = self.path(colons)?;
            (self.peek() == Some(K::FragClose)).then_some(())?;
            self.i += 1;
            d = p;
            generics = g;
        } else if self.eat(Tok::Lt) {
            let ty = self.ty()?;
            d.word("<");
            d.add(ty);
            if self.eat(Tok::As) {
                let (tr, _) = self.path(false)?;
                d.space();
                d.word_space("as");
                d.add(tr);
            }
            self.gt()?;
            d.word(">");
            self.expect(Tok::PathSep)?;
            d.word("::");
            generics |= self.segment(colons, &mut d)?;
        } else {
            if self.eat(Tok::PathSep) {
                d.word("::");
            }
            generics |= self.segment(colons, &mut d)?;
        }
        while self.is(Tok::PathSep) && !matches!(self.kind(self.i + 1), Some(K::Tok(Tok::Lt))) {
            self.i += 1;
            d.word("::");
            generics |= self.segment(colons, &mut d)?;
        }
        Some((d, generics))
    }

    /// One path segment and its generic args: `x::<T>` (expressions) or
    /// `X<T>` / `Fn(A) -> B` (types).
    fn segment(&mut self, colons: bool, d: &mut Doc) -> Option<bool> {
        match self.tok()? {
            Tok::Ident(_) | Tok::SelfLower | Tok::SelfUpper | Tok::Super | Tok::Crate => {
                let name = self.bump();
                if name.ends_with("$crate") {
                    return None;
                }
                d.word(name);
            }
            _ => return None,
        }
        let turbofish = self.is(Tok::PathSep) && self.tok_at(self.i + 1) == Some(Tok::Lt);
        if colons {
            if turbofish {
                self.i += 1;
                d.word("::");
                d.add(self.generic_args()?);
                return Some(true);
            }
            return Some(false);
        }
        if turbofish {
            self.i += 1;
        }
        if self.is(Tok::Lt) {
            d.add(self.generic_args()?);
            return Some(true);
        }
        if self.open(Delim::Paren) {
            // `Fn(A, B) -> C`.
            self.i += 1;
            let (args, _) = self.list(Delim::Paren, |p| p.ty().map(|t| ibox(INDENT, t)))?;
            d.word("(");
            d.add(commasep(args, false));
            d.word(")");
            if self.eat(Tok::Arrow) {
                d.add(ret_ty(self.ty()?));
            }
            return Some(true);
        }
        Some(false)
    }

    /// Consumes one `>` closing generic args (half of a `>>`).
    fn gt(&mut self) -> Option<()> {
        self.expect(Tok::Gt)
    }

    /// `<A, B, Item = C>` at the cursor.
    fn generic_args(&mut self) -> Option<Doc> {
        self.expect(Tok::Lt)?;
        let mut args = Vec::new();
        while !self.is(Tok::Gt) {
            let arg = match self.tok() {
                Some(Tok::Lifetime(_)) => Doc::w(self.bump()),
                Some(Tok::Ident(_)) if self.tok_at(self.i + 1) == Some(Tok::Eq) => {
                    let mut a = Doc::w(self.bump());
                    self.i += 1;
                    a.space();
                    a.word_space("=");
                    a.add(self.ty()?);
                    a
                }
                Some(Tok::Ident(_)) if self.tok_at(self.i + 1) == Some(Tok::Colon) => return None,
                Some(Tok::Int(..) | Tok::Minus | Tok::True | Tok::False | Tok::Char(..) | Tok::Str(..)) => self.unary(R::default())?.d,
                _ if self.open(Delim::Brace) => self.block_expr(None, false)?.d,
                _ => self.ty()?,
            };
            args.push(arg);
            if !self.eat(Tok::Comma) && !self.is(Tok::Gt) {
                return None;
            }
        }
        self.gt()?;
        let mut d = Doc::w("<");
        d.add(commasep(args, false));
        d.word(">");
        Some(d)
    }

    // ---------- types ----------

    /// A type as `print_type` writes it, in its `ibox(0)`.
    fn ty(&mut self) -> Option<Doc> {
        use Tok::*;
        let d = match self.peek()? {
            K::FragOpen(FragKind::Ty) => {
                self.i += 1;
                let t = self.ty()?;
                (self.peek() == Some(K::FragClose)).then_some(())?;
                self.i += 1;
                return Some(t);
            }
            K::Open(Delim::Paren) => {
                self.i += 1;
                let (mut items, trailing) = self.list(Delim::Paren, |p| p.ty())?;
                let mut d = Doc::w("(");
                if items.len() == 1 && !trailing {
                    d.add(items.pop().unwrap());
                } else {
                    let one = items.len() == 1;
                    d.add(commasep(items, false));
                    if one {
                        d.word(",");
                    }
                }
                d.word(")");
                d
            }
            K::Open(Delim::Bracket) => {
                self.i += 1;
                let mut d = Doc::w("[");
                d.add(self.ty()?);
                if self.eat(Semi) {
                    d.word("; ");
                    d.add(self.expr(R::default())?.d);
                }
                self.expect_close(Delim::Bracket)?;
                d.word("]");
                d
            }
            K::Tok(Amp | AndAnd) => {
                let double = self.is(AndAnd);
                self.i += 1;
                let mut d = Doc::w("&");
                if matches!(self.tok(), Some(Lifetime(_))) {
                    d.word(self.bump());
                    d.nbsp();
                }
                if self.eat(Mut) {
                    d.word_nbsp("mut");
                }
                d.add(self.ty()?);
                if double {
                    let mut o = Doc::w("&");
                    o.add(ibox(0, d));
                    o
                } else {
                    d
                }
            }
            K::Tok(Star) => {
                self.i += 1;
                let mut d = Doc::w("*");
                if self.eat(Const) {
                    d.word_nbsp("const");
                } else {
                    self.expect(Mut)?;
                    d.word_nbsp("mut");
                }
                d.add(self.ty()?);
                d
            }
            K::Tok(Underscore) => {
                self.i += 1;
                Doc::w("_")
            }
            K::Tok(Bang) => {
                self.i += 1;
                Doc::w("!")
            }
            K::Tok(Fn) => {
                self.i += 1;
                if !self.open(Delim::Paren) {
                    return None;
                }
                self.i += 1;
                let (params, _) = self.list(Delim::Paren, |p| {
                    let named = matches!(p.tok(), Some(Ident(_) | Underscore)) && p.tok_at(p.i + 1) == Some(Colon);
                    let mut d = Doc::default();
                    if named {
                        d.word(p.bump());
                        p.i += 1;
                        d.word(":");
                        d.space();
                    }
                    d.add(p.ty()?);
                    Some(ibox(INDENT, d))
                })?;
                let mut d = Doc::w("fn");
                d.word("(");
                d.add(commasep(params, false));
                d.word(")");
                if self.eat(Arrow) {
                    d.add(ret_ty(self.ty()?));
                }
                ibox(INDENT, d)
            }
            K::Tok(Dyn) => {
                self.i += 1;
                let mut d = Doc::default();
                d.word_nbsp("dyn");
                d.add(self.bounds()?);
                d
            }
            K::Tok(Impl) => {
                self.i += 1;
                let mut d = Doc::default();
                d.word_nbsp("impl");
                d.add(self.bounds()?);
                d
            }
            K::Tok(Ident(_) | SelfUpper | SelfLower | Super | Crate | PathSep | Lt) => {
                let (p, generics) = self.path(false)?;
                if self.is(Bang) && !generics && matches!(self.kind(self.i + 1), Some(K::Open(_))) {
                    self.i += 1;
                    self.mac(p)?
                } else {
                    p
                }
            }
            _ => return None,
        };
        Some(ibox(0, d))
    }

    /// `A + B + 'a` after `dyn` or `impl` (`print_type_bounds`).
    fn bounds(&mut self) -> Option<Doc> {
        let mut d = Doc::default();
        let mut first = true;
        loop {
            if !first {
                d.nbsp();
                d.word_space("+");
            }
            first = false;
            match self.tok()? {
                Tok::Lifetime(_) => d.word(self.bump()),
                Tok::Question => {
                    self.i += 1;
                    d.word("?");
                    d.add(self.path(false)?.0);
                }
                _ => d.add(self.path(false)?.0),
            }
            if !self.eat(Tok::Plus) {
                return Some(d);
            }
        }
    }

    // ---------- patterns ----------

    /// A pattern; `alt` allows a top-level `a | b` (and a leading `|`).
    fn pat(&mut self, alt: bool) -> Option<Doc> {
        if !alt {
            return self.pat1();
        }
        self.eat(Tok::Pipe);
        let first = self.pat1()?;
        if !self.is(Tok::Pipe) {
            return Some(first);
        }
        // `strsep("|", true, ..)`.
        let mut d = Doc::default();
        d.begin(0, false);
        d.add(first);
        while self.eat(Tok::Pipe) {
            d.space();
            d.word_space("|");
            d.add(self.pat1()?);
        }
        d.end();
        Some(d)
    }

    /// A literal or path the pattern holds as an expression (a range end,
    /// a literal): `print_expr`'s box around it.
    fn pat_expr(d: Doc) -> Doc {
        ibox(INDENT, d)
    }

    fn pat1(&mut self) -> Option<Doc> {
        use Tok::*;
        let k = self.peek()?;
        let s = match k {
            K::FragOpen(FragKind::Pat | FragKind::PatParam) => {
                self.i += 1;
                let p = self.pat(true)?;
                (self.peek() == Some(K::FragClose)).then_some(())?;
                self.i += 1;
                return Some(p);
            }
            K::Open(Delim::Paren) => {
                self.i += 1;
                let (mut items, trailing) = self.list(Delim::Paren, |p| p.pat(true))?;
                let mut d = Doc::w("(");
                if items.len() == 1 && !trailing && items[0].flat() != ".." {
                    d.add(items.pop().unwrap());
                } else {
                    let one = items.len() == 1;
                    d.add(commasep(items, false));
                    if one {
                        d.word(",");
                    }
                }
                d.word(")");
                return Some(d);
            }
            K::Open(Delim::Bracket) => {
                self.i += 1;
                let (items, _) = self.list(Delim::Bracket, |p| p.pat(true))?;
                let mut d = Doc::w("[");
                d.add(commasep(items, false));
                d.word("]");
                return Some(d);
            }
            K::Tok(Underscore) => {
                self.i += 1;
                return Some(Doc::w("_"));
            }
            K::Tok(DotDot) if matches!(self.kind(self.i + 1), Some(K::Tok(Comma) | K::Close(_) | K::Tok(Pipe) | K::Tok(FatArrow))) => {
                self.i += 1;
                return Some(Doc::w(".."));
            }
            K::Tok(DotDotEq | DotDot) => {
                let mut d = Doc::w(self.bump());
                d.add(self.range_end()?);
                return Some(d);
            }
            K::Tok(Amp | AndAnd) => {
                let double = self.is(AndAnd);
                self.i += 1;
                let mut d = Doc::w("&");
                if self.eat(Mut) {
                    d.word("mut ");
                }
                d.add(self.pat1()?);
                if double {
                    let mut o = Doc::w("&");
                    o.add(d);
                    return Some(o);
                }
                return Some(d);
            }
            K::Tok(Ref | Mut) => {
                let mut d = Doc::default();
                let r = self.eat(Ref);
                let m = self.eat(Mut);
                if !r && m && self.is(Ref) {
                    return None;
                }
                // `print_pat`: `mut` of the binding first, then `ref`/`ref mut`.
                if r {
                    d.word_nbsp("ref");
                }
                if m {
                    d.word_nbsp("mut");
                }
                match self.tok()? {
                    Ident(_) => d.word(self.bump()),
                    _ => return None,
                }
                return self.binding_tail(d);
            }
            K::Tok(Ident(_))
                if !matches!(
                    self.kind(self.i + 1),
                    Some(K::Tok(PathSep | Bang | DotDot | DotDotEq | Ellipsis)) | Some(K::Open(Delim::Paren | Delim::Brace))
                ) =>
            {
                let name = Doc::w(self.bump());
                return self.binding_tail(name);
            }
            K::Tok(Int(..) | Float(_) | Str(..) | ByteStr(_) | ByteChar(_) | Char(..) | True | False) => Self::pat_expr(Doc::w(self.bump())),
            K::Tok(Minus) if matches!(self.tok_at(self.i + 1), Some(Int(..) | Float(_))) => {
                self.i += 1;
                let mut d = Doc::w("-");
                d.add(Self::pat_expr(Doc::w(self.bump())));
                Self::pat_expr(d)
            }
            K::Tok(Ident(_) | SelfLower | SelfUpper | Super | Crate | PathSep | Lt) => {
                let (path, generics) = self.path(true)?;
                if self.is(Bang) && !generics && matches!(self.kind(self.i + 1), Some(K::Open(_))) {
                    self.i += 1;
                    return self.mac(path);
                }
                if self.open(Delim::Paren) {
                    self.i += 1;
                    let (items, _) = self.list(Delim::Paren, |p| p.pat(true))?;
                    let mut d = path;
                    d.word("(");
                    d.add(commasep(items, false));
                    d.word(")");
                    return Some(d);
                }
                if self.open(Delim::Brace) {
                    return self.struct_pat(path);
                }
                path
            }
            _ => return None,
        };
        // A literal or path may start a range pattern.
        if self.is(DotDotEq) || self.is(Ellipsis) {
            let mut d = s;
            d.word(self.bump());
            d.add(self.range_end()?);
            return Some(d);
        }
        if self.is(DotDot) {
            self.i += 1;
            let mut d = s;
            d.word("..");
            if !matches!(self.peek(), Some(K::Tok(Comma | Pipe | FatArrow | If | Eq | Colon)) | Some(K::Close(_)) | None) {
                d.add(self.range_end()?);
            }
            return Some(d);
        }
        Some(s)
    }

    fn range_end(&mut self) -> Option<Doc> {
        use Tok::*;
        match self.tok()? {
            Int(..) | Float(_) | Char(..) | ByteChar(_) => Some(Self::pat_expr(Doc::w(self.bump()))),
            Minus => {
                self.i += 1;
                match self.tok()? {
                    Int(..) | Float(_) => {
                        let mut d = Doc::w("-");
                        d.add(Self::pat_expr(Doc::w(self.bump())));
                        Some(Self::pat_expr(d))
                    }
                    _ => None,
                }
            }
            Ident(_) | SelfUpper | PathSep | Lt | Crate | Super | SelfLower => Some(Self::pat_expr(self.path(true)?.0)),
            _ => None,
        }
    }

    /// `name @ sub` after a binding name.
    fn binding_tail(&mut self, name: Doc) -> Option<Doc> {
        if !self.eat(Tok::At) {
            return Some(name);
        }
        let sub = self.pat1()?;
        let mut d = name;
        d.space();
        d.word_space("@");
        d.add(sub);
        Some(d)
    }

    fn struct_pat(&mut self, path: Doc) -> Option<Doc> {
        self.i += 1;
        let mut fields = Vec::new();
        let mut rest = false;
        while !self.close(Delim::Brace) {
            if self.eat(Tok::DotDot) {
                rest = true;
                break;
            }
            let mut f = Doc::default();
            match self.tok()? {
                Tok::Ident(_) | Tok::Int(..) if self.tok_at(self.i + 1) == Some(Tok::Colon) => {
                    f.word(self.bump());
                    self.i += 1;
                    f.word_nbsp(":");
                    f.add(self.pat(true)?);
                }
                Tok::Ref | Tok::Mut | Tok::Ident(_) => f.add(self.pat1()?),
                _ => return None,
            }
            fields.push(boxed(INDENT, true, f));
            if !self.eat(Tok::Comma) && !self.close(Delim::Brace) {
                return None;
            }
        }
        self.expect_close(Delim::Brace)?;
        let empty = fields.is_empty() && !rest;
        let has_fields = !fields.is_empty();
        let mut d = path;
        d.nbsp();
        d.word("{");
        if !empty {
            d.space();
        }
        d.add(commasep(fields, true));
        if rest {
            if has_fields {
                d.word_space(",");
            }
            d.word("..");
        }
        if !empty {
            d.space();
        }
        d.word("}");
        Some(d)
    }

    // ---------- macro calls ----------

    /// `path!(..)` with the delimited group at the cursor, as `print_mac`
    /// writes it.
    fn mac(&mut self, path: Doc) -> Option<Doc> {
        let open = self.i;
        let close = self.group_end(open)?;
        self.i = close + 1;
        let K::Open(delim) = self.t[open].k else { return None };
        let inner = self.tts(open + 1, close)?;
        let mut d = Doc::default();
        if delim == Delim::Brace {
            d.begin(INDENT, true);
            d.add(path);
            d.word("!");
            d.nbsp();
            d.word("{");
            let open_space = !inner.0.is_empty();
            if open_space {
                d.space();
            }
            d.add(ibox(0, inner));
            if open_space {
                d.brk(1, -INDENT);
            }
            d.word("}");
            d.end();
        } else {
            let (o, c) = if delim == Delim::Paren { ("(", ")") } else { ("[", "]") };
            d.add(path);
            d.word("!");
            d.word(o);
            d.add(ibox(0, inner));
            d.word(c);
        }
        Some(d)
    }

    /// The index of the token that closes the group opened at `open`.
    fn group_end(&self, open: usize) -> Option<usize> {
        let mut depth = 0i32;
        for j in open..self.t.len() {
            match self.t[j].k {
                K::Open(_) | K::FragOpen(_) => depth += 1,
                K::Close(_) | K::FragClose => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(j);
                    }
                }
                K::Tok(_) => {}
            }
        }
        None
    }

    /// rustc's `print_tts` over the token trees in `lo..hi`.
    fn tts(&self, lo: usize, hi: usize) -> Option<Doc> {
        // Each tree: its first and last token index.
        let mut trees = Vec::new();
        let mut j = lo;
        while j < hi {
            let end = match self.t[j].k {
                K::Open(_) | K::FragOpen(_) => self.group_end(j)?,
                K::Tok(Tok::DocStr(_)) => return None,
                K::Tok(_) => j,
                K::Close(_) | K::FragClose => return None,
            };
            trees.push((j, end));
            j = end + 1;
        }
        let mut d = Doc::default();
        for (n, &(a, b)) in trees.iter().enumerate() {
            d.add(self.tree(a, b)?);
            if let Some(&(c, _)) = trees.get(n + 1)
                && self.space_after(a, b, c)?
            {
                d.space();
            }
        }
        Some(d)
    }

    /// One token tree (`print_tt`); a group as `print_mac_common` writes
    /// it with no header.
    fn tree(&self, a: usize, b: usize) -> Option<Doc> {
        let t = &self.t[a];
        Some(match t.k {
            K::Tok(_) if t.text.starts_with("$crate") => return None,
            K::Tok(_) => Doc::w(t.text.clone()),
            K::FragOpen(_) => ibox(0, self.tts(a + 1, b)?),
            K::Open(Delim::Brace) => {
                let inner = self.tts(a + 1, b)?;
                let open_space = !inner.0.is_empty() && t.alone?;
                let mut d = Doc::default();
                d.begin(INDENT, true);
                d.word("{");
                if open_space {
                    d.space();
                }
                d.add(ibox(0, inner));
                if open_space {
                    d.brk(1, -INDENT);
                }
                d.word("}");
                d.end();
                d
            }
            K::Open(dl) => {
                let (o, c) = if dl == Delim::Paren { ("(", ")") } else { ("[", "]") };
                let mut d = Doc::w(o);
                d.add(ibox(0, self.tts(a + 1, b)?));
                d.word(c);
                d
            }
            K::Close(_) | K::FragClose => return None,
        })
    }

    /// Whether `print_tts` puts a space between the tree `a..=b` and the
    /// tree starting at `c`. None when it depends on what lust lost.
    fn space_after(&self, a: usize, b: usize, c: usize) -> Option<bool> {
        let one = |nt: bool, alone: bool, next_nt: bool| {
            if alone { self.space_between(a, b, c, nt, next_nt) } else { a == b && self.ident_tok(a) && self.ident_tok(c) }
        };
        let alone = self.t[b].alone;
        let (sa, sc) = (self.t[a].subst && a == b, self.t[c].subst);
        // A substituted name: an `$x:ident` (NtIdent, `Alone`) or an `$x:tt`.
        let mut answers = Vec::new();
        for nt in if sa { vec![true, false] } else { vec![false] } {
            for next_nt in if sc { vec![true, false] } else { vec![false] } {
                let al = if nt { true } else { alone? };
                answers.push(one(nt, al, next_nt));
            }
        }
        answers.iter().all(|&x| x == answers[0]).then(|| answers[0])
    }

    fn ident_tok(&self, i: usize) -> bool {
        matches!(self.t[i].k, K::Tok(t) if ident_like(t))
    }

    /// rustc's `space_between` for the trees `a..=b` and the one at `c`.
    /// `nt`: the first tree is an NtIdent, which the ident rules skip.
    fn space_between(&self, a: usize, b: usize, c: usize, nt: bool, next_nt: bool) -> bool {
        let first = if a == b { self.tok_at(a) } else { None };
        let next = match self.t[c].k {
            K::Tok(t) => Some(t),
            _ => None,
        };
        let punct = |t: Option<Tok>| t.is_some_and(is_punct);
        let raw = self.t[a].text.starts_with("r#");
        // A non-reserved identifier: a plain name or a raw one.
        let plain_ident = !nt && matches!(first, Some(Tok::Ident(_))) || !nt && raw;
        match (first, next) {
            (Some(Tok::Dot), _) if !punct(next) => false,
            (Some(Tok::Dollar), Some(t)) if ident_like(t) && !next_nt => false,
            (_, Some(Tok::Comma | Tok::Semi | Tok::Dot)) if !punct(first) => false,
            (_, Some(Tok::Bang)) if plain_ident => false,
            (_, None)
                if self.t[c].k == K::Open(Delim::Paren)
                    && (plain_ident || !nt && matches!(first, Some(Tok::Fn | Tok::SelfUpper | Tok::Pub))) =>
            {
                false
            }
            (Some(Tok::Pound), None) if self.t[c].k == K::Open(Delim::Bracket) => false,
            _ => true,
        }
    }
}

/// ` -> T` (`print_fn_ret_ty`).
fn ret_ty(ty: Doc) -> Doc {
    let mut d = Doc::default();
    d.space();
    let mut a = Doc::default();
    a.word_space("->");
    a.add(ty);
    d.add(ibox(INDENT, a));
    d
}
