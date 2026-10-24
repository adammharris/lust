//! Explicit `for<'a, ..>` binders on fn pointer types and `Fn*` sugar
//! (W-BORROW3, ARCH 5.5). Lust's region model reads a fn pointer type or
//! `Fn(..)` sugar as elided: each input lifetime its own late-bound
//! region, an elided output the one input lifetime's. A binder whose
//! lifetimes say exactly that (each binder lifetime once in the inputs;
//! in the output only when it is the one input lifetime) is rewritten
//! here to the elided form: `for<'a> fn(&'a N) -> Option<L<'a>>` becomes
//! `fn(&N) -> Option<L<'_>>`. Any other binder on a plain fn pointer type
//! stays written, and check records which region slots share a binder
//! (`FnSig::binders`); on `Fn` sugar it is L0203. The binder list
//! stays in the AST so check can reject a name that shadows a lifetime
//! in scope (rustc E0496); a binder lifetime used where this rewrite does
//! not look (a nested fn pointer or `dyn` type) stays written and
//! resolves as undeclared (L0203).

use super::{PResult, Parser};
use crate::ast::{GenericArg, GenericArgs, Lifetime, TyExpr, TyId};
use crate::diag::Diag;
use crate::intern::Sym;

/// A place in a type that writes a lifetime: a reference, or lifetime arg
/// `arg` of path segment `seg`.
enum Site {
    Ref(TyId),
    Arg(TyId, usize, usize),
}

/// What `scan` finds in the inputs or the output.
#[derive(Default)]
struct Scan {
    /// The binder lifetimes written in plain places, by binder index.
    uses: Vec<(usize, Site)>,
    /// The lifetimes elision counts there (a reference, written or
    /// elided, and each written lifetime arg).
    lts: u32,
    /// The binder index of the last counted lifetime, if it is one.
    last_binder: Option<usize>,
    /// A part elision does not see into the same way (`dyn`, nested fn
    /// pointers and `Fn` sugar, `impl Trait`, qualified paths).
    opaque: bool,
}

impl Parser<'_> {
    /// Rewrites the uses of `binder` in a signature (`inputs`, `output`)
    /// to elided lifetimes, or fails when the binder means more than
    /// elision does. With `keep`, a binder that means more (a lifetime
    /// used in two inputs, or an output lifetime that is not the one
    /// input's: `for<'s> fn(&mut Ctx<'s>, &'s [u8]) -> &'s [u8]`) stays
    /// written instead, every binder lifetime of it; check reads which
    /// slots share a binder (`FnSig::binders`). Only a plain fn pointer
    /// type keeps one: `Fn` sugar and `dyn Fn` bound their binders
    /// elsewhere.
    pub(super) fn canon_binder(&mut self, binder: &[Lifetime], inputs: &[TyId], output: Option<TyId>, keep: bool) -> PResult<()> {
        if binder.is_empty() {
            return Ok(());
        }
        let names: Vec<Sym> = binder.iter().map(|l| l.name).collect();
        for (i, l) in binder.iter().enumerate() {
            let n = self.interner.get(l.name);
            if n == "_" || n == "static" || names[..i].contains(&l.name) {
                return Err(Diag::new(
                    "L0203",
                    l.span,
                    format!("`'{n}` cannot be declared in a `for<..>` binder here"),
                    "Declare each binder lifetime once, with a name other than `'_` and `'static`.",
                ));
            }
        }
        let mut ins = Scan::default();
        for &t in inputs {
            self.scan_binder(t, &names, &mut ins);
        }
        let mut outs = Scan::default();
        if let Some(t) = output {
            self.scan_binder(t, &names, &mut outs);
        }
        let mut seen = vec![false; names.len()];
        let mut cut: Option<Diag> = None;
        for &(i, _) in &ins.uses {
            if seen[i] {
                cut = cut.or(Some(binder_cut(binder[i].span, "it is used in two places of the inputs")));
            }
            seen[i] = true;
        }
        for &(i, _) in &outs.uses {
            let elided = !ins.opaque && ins.lts == 1 && ins.last_binder == Some(i);
            if !elided {
                cut = cut.or(Some(binder_cut(binder[i].span, "the output uses it, but it is not the one input lifetime")));
            }
        }
        if let Some(d) = cut {
            return if keep { Ok(()) } else { Err(d) };
        }
        let anon = self.interner.intern("_");
        for (_, site) in ins.uses.into_iter().chain(outs.uses) {
            match site {
                Site::Ref(t) => {
                    if let TyExpr::Ref { lifetime, .. } = &mut self.ast.tys[t.0 as usize] {
                        *lifetime = None;
                    }
                }
                Site::Arg(t, si, ai) => {
                    if let TyExpr::Path(segs) = &mut self.ast.tys[t.0 as usize]
                        && let GenericArgs::Angle(args) = &mut segs[si].args
                        && let GenericArg::Lifetime(lt) = &mut args[ai]
                    {
                        lt.name = anon;
                    }
                }
            }
        }
        Ok(())
    }

    /// Records in `s` the lifetimes of type `t` that elision counts and
    /// the plain places that write a binder lifetime (`names`).
    fn scan_binder(&self, t: TyId, names: &[Sym], s: &mut Scan) {
        match &self.ast.tys[t.0 as usize] {
            TyExpr::Ref { lifetime, inner, .. } => {
                let b = lifetime.and_then(|l| names.iter().position(|&n| n == l.name));
                if let Some(i) = b {
                    s.uses.push((i, Site::Ref(t)));
                }
                s.lts += 1;
                s.last_binder = b;
                self.scan_binder(*inner, names, s);
            }
            TyExpr::Paren(i) | TyExpr::Slice(i) | TyExpr::Array { inner: i, .. } | TyExpr::Ptr { inner: i, .. } => {
                self.scan_binder(*i, names, s)
            }
            TyExpr::Tuple(elems) => {
                for &e in elems {
                    self.scan_binder(e, names, s);
                }
            }
            TyExpr::Path(segs) => {
                for (si, seg) in segs.iter().enumerate() {
                    match &seg.args {
                        GenericArgs::Angle(args) => {
                            for (ai, g) in args.iter().enumerate() {
                                match g {
                                    GenericArg::Lifetime(l) => {
                                        let b = names.iter().position(|&n| n == l.name);
                                        if let Some(i) = b {
                                            s.uses.push((i, Site::Arg(t, si, ai)));
                                        }
                                        s.lts += 1;
                                        s.last_binder = b;
                                    }
                                    GenericArg::Type(e) => self.scan_binder(*e, names, s),
                                    GenericArg::Const(_) => {}
                                    GenericArg::Binding { .. } => s.opaque = true,
                                }
                            }
                        }
                        GenericArgs::Parenthesized { .. } => s.opaque = true,
                        _ => {}
                    }
                }
            }
            TyExpr::FnPtr { .. } | TyExpr::Dyn { .. } | TyExpr::ImplTrait { .. } | TyExpr::QPath { .. } | TyExpr::MacroCall(_) => {
                s.opaque = true
            }
            _ => {}
        }
    }
}

/// L0203 for a binder lust does not read as elision.
fn binder_cut(span: crate::diag::Span, why: &str) -> Diag {
    Diag::new(
        "L0203",
        span,
        format!("this `for<..>` lifetime is not supported yet: {why}"),
        "Write the type with elided lifetimes (`fn(&T) -> &U`), or use each binder lifetime once in the inputs.",
    )
}
