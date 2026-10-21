//! `{:?}` of a range (`1..5`, `'a'..='c'`, `..`): core 1.99's Debug for
//! the six `core::ops` range kinds formats each bound with the caller's
//! formatter (its flags and width), with the separators written plain:
//! `start.fmt(f)?; write!(f, "..")?; end.fmt(f)`, and `RangeInclusive`
//! adds " (exhausted)" when its flag is set. Lowering spells that out
//! as format parts at the format site (`fmt_parts`) for a range a
//! format argument names through plain references (`range_fmt_kind`);
//! a range inside another type uses Debug glue (cgen/fmt.rs `dbg_cty`).

use super::*;
use crate::ty::iter::IterKind;

impl<'p> Lower<'p> {
    /// The format parts for `{:?}` of the range at `*value` (type `ty`,
    /// a range kind under plain references), or None for another type.
    pub(super) fn range_debug_parts(&mut self, value: &Operand, ty: Ty, spec: FmtSpec, width: Option<Operand>, prec: Option<Operand>) -> Option<Vec<FmtPart>> {
        let (k, elem, refs) = crate::check::fmt::range_fmt_kind(&self.body.tys, ty)?;
        let (Operand::Copy(base) | Operand::Move(base)) = value else { return None };
        let mut pl = base.clone().deref();
        for _ in 0..refs {
            pl = pl.deref();
        }
        let span = Span::default();
        let mut field = |this: &mut Self, i: u32| -> FmtPart {
            let rt = this.ref_ty(false, elem);
            let r = this.temp(rt);
            this.assign(Place::local(r), Rvalue::Ref(false, pl.clone().project(Proj::Field(i))), span);
            FmtPart::Arg { value: Operand::Copy(Place::local(r)), ty: elem, debug: true, spec, width: width.clone(), prec: prec.clone() }
        };
        let lit = |s: &str| FmtPart::Lit(s.to_string());
        Some(match k {
            IterKind::Range => vec![field(self, 0), lit(".."), field(self, 1)],
            IterKind::RangeFrom => vec![field(self, 0), lit("..")],
            IterKind::RangeTo => vec![lit(".."), field(self, 0)],
            IterKind::RangeToInclusive => vec![lit("..="), field(self, 0)],
            IterKind::RangeFull => vec![lit("..")],
            IterKind::RangeInclusive => {
                let (a, b) = (field(self, 0), field(self, 1));
                // The suffix as a `&str` argument with no spec: written
                // plain, as core's `write!(fmt, " (exhausted)")`.
                let st = self.ref_ty(false, STR);
                let s = self.temp(st);
                let blob = |t: &str| Operand::Const(Const::StrBytes(crate::ast::ByteBlob::new(t.as_bytes().to_vec())));
                let flag = Operand::Copy(pl.clone().project(Proj::Field(2)));
                let (ex, live) = (self.new_block(), self.new_block());
                let join = self.new_block();
                let blk = &mut self.body.blocks[self.cur.0 as usize];
                blk.term = Terminator::If(flag, ex, live);
                blk.term_span = span;
                self.cur = ex;
                self.assign(Place::local(s), Rvalue::Use(blob(" (exhausted)")), span);
                self.goto(join, span);
                self.cur = live;
                self.assign(Place::local(s), Rvalue::Use(blob("")), span);
                self.goto(join, span);
                self.cur = join;
                let r = self.ref_ty(false, st);
                let sr = self.temp(r);
                self.assign(Place::local(sr), Rvalue::Ref(false, Place::local(s)), span);
                let suffix = FmtPart::Arg { value: Operand::Copy(Place::local(sr)), ty: st, debug: false, spec: FmtSpec::default(), width: None, prec: None };
                vec![a, lit("..="), b, suffix]
            }
            _ => return None,
        })
    }
}
