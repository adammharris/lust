// Slice inherent methods in body checking (tf-slice, TRIAGE T3):
// `starts_with`, `ends_with`, `fill`, `copy_from_slice`, and
// `copy_within` on `[T]`, `[T; N]`, and `Vec<T>` (through its
// `Deref<Target = [T]>`, like `swap`). The element bounds are the
// core ones (`PartialEq` for the needle tests, `Clone` for `fill`,
// `Copy` for the copies), deferred like the Vec table's. Codegen
// emits each builtin in cgen.rs; `copy_within`'s range argument is
// a `RangeBounds<usize>` read by drain's form machinery
// (check/iter.rs `drain_range_form`, lower.rs `drain_bounds`), so
// its panics are core's slice-index ones (runtime/core.c
// `lust_range_bounds_check`).
//
// Rule zero: a receiver form or argument shape outside this list
// falls through to the normal dispatch and rejects there.
use super::*;

impl<'p> Ctx<'p> {
    /// The slice methods above. Returns None when the call is none
    /// of these, so the caller's other dispatch runs.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn slice_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        derefs: u8,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
    ) -> Option<Ty> {
        use Builtin as B;
        // `str::get` with a range (on `str` and, through its deref,
        // `String`): its own builtin, with char boundary checks.
        if (base == STR || base == STRING) && self.name(name) == "get" {
            return Some(self.str_get_method(e, recv, derefs, name_span, args));
        }
        let elem = match self.kind(base) {
            TyKind::Slice(el) | TyKind::Array(el, _) => el,
            _ => self.tys.vec_elem(base)?,
        };
        // Compare the borrowed name before anything allocates, as
        // in `iter_method`.
        let n = match self.name(name) {
            "starts_with" => "starts_with",
            "ends_with" => "ends_with",
            "fill" => "fill",
            "copy_from_slice" => "copy_from_slice",
            "clone_from_slice" => "clone_from_slice",
            "copy_within" => "copy_within",
            "get" => "get",
            "get_mut" => "get_mut",
            "join" => "join",
            "concat" => "concat",
            "eq_ignore_ascii_case" => "eq_ignore_ascii_case",
            "is_ascii" => "is_ascii",
            "to_ascii_lowercase" => "to_ascii_lowercase",
            "to_ascii_uppercase" => "to_ascii_uppercase",
            "make_ascii_lowercase" => "make_ascii_lowercase",
            "make_ascii_uppercase" => "make_ascii_uppercase",
            "repeat" => "repeat",
            "rotate_left" => "rotate_left",
            "rotate_right" => "rotate_right",
            "partition_point" => "partition_point",
            "extend_from_within" => "extend_from_within",
            "resize_with" => "resize_with",
            "dedup_by" => "dedup_by",
            "dedup_by_key" => "dedup_by_key",
            "splice" => "splice",
            "strip_prefix" => "strip_prefix",
            "strip_suffix" => "strip_suffix",
            "trim_ascii_start" => "trim_ascii_start",
            "trim_ascii_end" => "trim_ascii_end",
            "trim_ascii" => "trim_ascii",
            "map" => "map",
            "as_chunks" => "as_chunks",
            "as_chunks_mut" => "as_chunks_mut",
            "as_rchunks" => "as_rchunks",
            "as_rchunks_mut" => "as_rchunks_mut",
            _ => return None,
        };
        if n.starts_with("as_") {
            return Some(self.slice_as_chunks(e, recv, elem, derefs, n, name_span, args, turbofish));
        }
        if n == "map" {
            let TyKind::Array(_, len) = self.kind(base) else { return None };
            return Some(self.array_map_method(e, elem, len, derefs, name_span, args, turbofish));
        }
        if n == "strip_prefix" || n == "strip_suffix" {
            return Some(self.slice_strip_method(e, recv, elem, derefs, name_span, args, turbofish, n == "strip_suffix"));
        }
        if n.starts_with("trim_ascii") {
            // `[u8]` only; other element types fall through to the
            // normal dispatch and reject there.
            if self.resolve(elem) != int(IntTy::U8) {
                return None;
            }
            if !turbofish.is_empty() {
                self.errs.push(not_yet("L0721", name_span, "turbofish on this slice method"));
                return Some(self.slice_bail(args));
            }
            let which = match n {
                "trim_ascii_start" => 0,
                "trim_ascii_end" => 1,
                _ => 2,
            };
            self.check_packed_borrow(recv, name_span);
            self.set_res(e, Res::BuiltinMethod { b: B::SliceTrimAscii(which), derefs, autoref: Autoref::Ref });
            self.check_args(&[], args, name_span);
            let sl = self.tys.intern(TyKind::Slice(elem));
            return Some(self.tys.mk_ref(false, sl));
        }
        if matches!(
            n,
            "eq_ignore_ascii_case"
                | "is_ascii"
                | "to_ascii_lowercase"
                | "to_ascii_uppercase"
                | "make_ascii_lowercase"
                | "make_ascii_uppercase"
                | "repeat"
                | "rotate_left"
                | "rotate_right"
                | "partition_point"
                | "extend_from_within"
                | "resize_with"
                | "dedup_by"
                | "dedup_by_key"
        ) {
            return self.slice_method_r4(e, recv, base, elem, derefs, n, name_span, args, turbofish);
        }
        if n == "splice" {
            if self.tys.vec_elem(base).is_none() {
                return None;
            }
            return Some(self.splice_method(e, recv, elem, derefs, name_span, args, turbofish));
        }
        if n == "join" || n == "concat" {
            return self.slice_join_concat(e, recv, elem, derefs, name_span, args, n == "join");
        }
        if n == "copy_within" {
            return Some(self.copy_within_method(e, recv, elem, derefs, name_span, args, turbofish));
        }
        if n == "get" || n == "get_mut" {
            return Some(self.slice_get_method(e, recv, elem, derefs, name_span, args, n == "get_mut"));
        }
        let needle = |this: &mut Self| {
            let sl = this.tys.intern(TyKind::Slice(elem));
            this.tys.mk_ref(false, sl)
        };
        let (b, autoref, params, ret): (B, Autoref, Vec<Ty>, Ty) = match n {
            "starts_with" | "ends_with" => {
                self.deferred_eq.push((elem, name_span));
                let r = needle(self);
                (if n == "starts_with" { B::SliceStartsWith } else { B::SliceEndsWith }, Autoref::Ref, vec![r], BOOL)
            }
            "fill" => {
                // `fill` runs `clone_from` per element; a hash
                // table's own clone_from reuse is the same precise
                // reject as a direct `clone_from` call.
                if crate::check::collect::mentions_hash_table(self.p, &self.tys, elem) {
                    self.errs.push(not_yet("L0640", name_span, "`fill` on a slice of a type holding a hash table"));
                    return Some(self.slice_bail(args));
                }
                self.deferred_clone.push((elem, name_span));
                (B::SliceFill, Autoref::RefMut, vec![elem], UNIT)
            }
            // core specializes `clone_from_slice` on `TrivialClone` (a Copy
            // type whose Clone is core's or derived): that runs
            // `copy_from_slice`, panic message included. Any other
            // `T: Clone` runs `clone_from` per element after its own
            // length assert. The glue does not call a Copy type's written
            // Clone (see `glue_methods`): its `clone_from` (or `clone`)
            // fn goes in `index_recv`, and lowering calls it
            // (`SliceCloneFromWritten`, lower/iter.rs).
            "clone_from_slice" => {
                let el = self.deep(elem);
                let r = needle(self);
                if crate::check::collect::is_copy(self.p, &self.tys, el) {
                    if !trivial_clone(self.p, &self.tys, el) {
                        if self.written_clone_fn(e, el, name_span).is_none() {
                            self.errs.push(not_yet("L0640", name_span, "`clone_from_slice` on a Copy type with a written `Clone` impl"));
                            return Some(self.slice_bail(args));
                        }
                        (B::SliceCloneFromWritten, Autoref::RefMut, vec![r], UNIT)
                    } else {
                        (B::SliceCopyFromSlice, Autoref::RefMut, vec![r], UNIT)
                    }
                } else {
                    if crate::check::collect::mentions_hash_table(self.p, &self.tys, el) {
                        self.errs.push(not_yet("L0640", name_span, "`clone_from_slice` on a slice of a type holding a hash table"));
                        return Some(self.slice_bail(args));
                    }
                    self.deferred_clone.push((elem, name_span));
                    (B::SliceCloneFromSlice, Autoref::RefMut, vec![r], UNIT)
                }
            }
            _ => {
                self.deferred_copy.push((elem, name_span));
                let r = needle(self);
                (B::SliceCopyFromSlice, Autoref::RefMut, vec![r], UNIT)
            }
        };
        if !turbofish.is_empty() {
            self.errs.push(not_yet("L0721", name_span, "turbofish on this slice method"));
            return Some(self.slice_bail(args));
        }
        self.check_packed_borrow(recv, name_span);
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
        self.check_args(&params, args, name_span);
        Some(ret)
    }

    /// `[T]::as_chunks::<N>()` and `as_rchunks`, and their `_mut` forms
    /// (R13): `(&[[T; N]], &[T])` (the rest first for `as_rchunks`). `N`
    /// comes from the turbofish, else from later uses; a known 0 is
    /// rustc's deny-by-default `unconditional_panic` (L0541).
    #[allow(clippy::too_many_arguments)]
    fn slice_as_chunks(&mut self, e: ExprId, recv: ExprId, elem: Ty, derefs: u8, n: &str, name_span: Span, args: &[ExprId], turbofish: &[ast::GenericArg]) -> Ty {
        let mutable = n.ends_with("_mut");
        let rev = n.starts_with("as_r");
        let mut len_c = None;
        // rustc's lint sees a literal 0, not a const parameter's value:
        // that one panics at run time (cgen/slices.rs).
        let mut from_param = false;
        match turbofish {
            [] => {}
            [ast::GenericArg::Const(c)] => {
                let scope = self.body_scope.clone();
                match generics::resolve_const_arg(&self.p.ast, &self.p.interner, &self.p.known, &mut self.tys, &scope, *c, name_span) {
                    Ok(c) => len_c = Some(c),
                    Err(d) => {
                        self.errs.push(d);
                        return self.slice_bail(args);
                    }
                }
            }
            // `_` at the const slot parses as a type: inferred.
            [ast::GenericArg::Type(t)] if matches!(self.p.ast.ty(*t), ast::TyExpr::Infer) => {}
            // A const parameter parses as a type path.
            [ast::GenericArg::Type(t)] if let Some(c) = self.const_param_path(*t) => {
                len_c = Some(c);
                from_param = true;
            }
            _ => {
                self.errs.push(not_yet("L0721", name_span, "this turbofish on `as_chunks`"));
                return self.slice_bail(args);
            }
        }
        let len_c = len_c.unwrap_or_else(|| self.fresh_const_var());
        if !from_param && let ConstKind::Int(0) = self.tys.const_kind(len_c) {
            self.err("L0541", name_span, format!("const parameter `N` of `{n}` is zero: this operation will panic at runtime"), "Use a chunk size of 1 or more.");
            return self.slice_bail(args);
        }
        let arr = self.tys.intern(TyKind::Array(elem, len_c));
        let (sa, se) = (self.tys.intern(TyKind::Slice(arr)), self.tys.intern(TyKind::Slice(elem)));
        let (ra, re) = (self.tys.mk_ref(mutable, sa), self.tys.mk_ref(mutable, se));
        let parts = if rev { [re, ra] } else { [ra, re] };
        let ts = self.tys.intern_tys(&parts);
        let ret = self.tys.intern(TyKind::Tuple(ts));
        self.check_packed_borrow(recv, name_span);
        let autoref = if mutable { Autoref::RefMut } else { Autoref::Ref };
        self.set_res(e, Res::BuiltinMethod { b: Builtin::SliceAsChunks(rev), derefs, autoref });
        self.check_args(&[], args, name_span);
        ret
    }

    /// `[T; N]::map(self, f: impl FnMut(T) -> U) -> [U; N]` (R22). Through
    /// a reference the array is copied out, so `T: Copy` (rustc E0507
    /// otherwise).
    #[allow(clippy::too_many_arguments)]
    fn array_map_method(&mut self, e: ExprId, elem: Ty, len: ConstId, derefs: u8, name_span: Span, args: &[ExprId], turbofish: &[ast::GenericArg]) -> Ty {
        if !turbofish.is_empty() {
            self.errs.push(not_yet("L0721", name_span, "turbofish on `map`"));
            return self.slice_bail(args);
        }
        if derefs > 0 {
            self.deferred_copy.push((elem, name_span));
        }
        let out = self.new_var(false);
        let f = self.fn_mut_param(&[elem], out, name_span);
        self.set_res(e, Res::BuiltinMethod { b: Builtin::ArrayMap, derefs, autoref: Autoref::None });
        self.check_args(&[f], args, name_span);
        if self.adapter_callable_gap(args, &[f], false) {
            return ERROR;
        }
        self.tys.intern(TyKind::Array(out, len))
    }

    /// `[T]::strip_prefix` and `strip_suffix` (R13): `prefix: &P` with
    /// `P: SlicePattern<Item = T>`, which core implements for `[T]`
    /// and `[T; N]` only. `P` is generic, so the argument takes no
    /// unsizing or deref coercion: `&Vec<T>` and `&&[T]` reject, as
    /// rustc's E0277 does. `&mut` reborrows as `&`.
    #[allow(clippy::too_many_arguments)]
    fn slice_strip_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        elem: Ty,
        derefs: u8,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        suffix: bool,
    ) -> Ty {
        let n = if suffix { "strip_suffix" } else { "strip_prefix" };
        if !turbofish.is_empty() {
            self.errs.push(not_yet("L0721", name_span, "turbofish on this slice method"));
            return self.slice_bail(args);
        }
        let [a] = args else {
            self.err("L0105", name_span, format!("`{n}` takes 1 argument"), "Pass the pattern slice.");
            return self.slice_bail(args);
        };
        let at = self.expr(*a, None);
        let at = self.deep(at);
        if at == ERROR {
            return ERROR;
        }
        let pat = match self.kind(at) {
            TyKind::Ref(_, _, inner) => match self.kind(inner) {
                TyKind::Slice(x) | TyKind::Array(x, _) => Some((inner, x)),
                _ => None,
            },
            _ => None,
        };
        let Some((inner, pe)) = pat else {
            let tn = self.tn(at);
            self.err(
                "L0612",
                self.span(*a),
                format!("the trait bound `SlicePattern` is not satisfied by the pattern `{tn}` of `{n}`"),
                "Pass a `&[T]` or a `&[T; N]`, such as `&v[..]`.",
            );
            return ERROR;
        };
        if !self.unify(pe, elem) {
            self.mismatch(self.span(*a), elem, pe);
            return ERROR;
        }
        let want = self.tys.mk_ref(false, inner);
        self.coerce_expr(*a, at, want);
        self.deferred_eq.push((elem, name_span));
        self.check_packed_borrow(recv, name_span);
        self.set_res(e, Res::BuiltinMethod { b: Builtin::SliceStrip(suffix), derefs, autoref: Autoref::Ref });
        let sl = self.tys.intern(TyKind::Slice(elem));
        let r = self.tys.mk_ref(false, sl);
        self.tys.mk_option(r)
    }

    /// `[T]::copy_within(src, dest)`: `src` is any
    /// `RangeBounds<usize>`, read by drain's form machinery, and
    /// `dest` a plain index. The form is recorded for lowering
    /// (`Checked::drain_range`), like a drain call.
    fn copy_within_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        elem: Ty,
        derefs: u8,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
    ) -> Ty {
        if !turbofish.is_empty() {
            self.errs.push(not_yet("L0721", name_span, "turbofish on `copy_within`"));
            return self.slice_bail(args);
        }
        if args.len() != 2 {
            self.err("L0105", name_span, "`copy_within` takes 2 arguments", "Pass the source range and the destination index.");
            return self.slice_bail(args);
        }
        self.deferred_copy.push((elem, name_span));
        let Some(form) = self.drain_range_form(e, args[0], name_span) else {
            self.expr(args[1], None);
            return ERROR;
        };
        self.expect_expr(args[1], USIZE);
        self.check_packed_borrow(recv, name_span);
        self.out.drain_ranges.push((e, form));
        self.set_res(e, Res::BuiltinMethod { b: Builtin::SliceCopyWithin, derefs, autoref: Autoref::RefMut });
        UNIT
    }

    /// `[T]::get` and `get_mut`: a `usize` index (the Vec table's
    /// form, kept here so the argument is checked once) or any
    /// `SliceIndex` range form: a syntactic range, a range value,
    /// or a `(Bound, Bound)` pair. Range forms record like drain
    /// and answer `Option<&[T]>`.
    fn slice_get_method(&mut self, e: ExprId, recv: ExprId, elem: Ty, derefs: u8, name_span: Span, args: &[ExprId], mutable: bool) -> Ty {
        use Builtin as B;
        let autoref = if mutable { Autoref::RefMut } else { Autoref::Ref };
        if args.len() != 1 {
            // The table's arity error shape.
            self.check_args(&[USIZE], args, name_span);
            return ERROR;
        }
        let arg = args[0];
        let form = if matches!(self.p.ast.expr(arg), Expr::Range { .. }) {
            self.drain_range_form(e, arg, name_span)
        } else {
            let t = self.expr(arg, None);
            let t = self.deep(t);
            match self.drain_form_of(t, name_span) {
                Some(f) => Some(DrainRange::Value(f)),
                None => {
                    // A plain index: the Vec table's builtin and
                    // coercion, on the argument as already checked.
                    self.coerce_expr(arg, t, USIZE);
                    let r = self.tys.mk_ref(mutable, elem);
                    let ret = self.tys.mk_option(r);
                    self.check_packed_borrow(recv, name_span);
                    let b = if mutable { B::VecGetMut } else { B::VecGet };
                    self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
                    return ret;
                }
            }
        };
        let Some(form) = form else { return ERROR };
        self.check_packed_borrow(recv, name_span);
        self.out.drain_ranges.push((e, form));
        let b = if mutable { B::SliceGetRangeMut } else { B::SliceGetRange };
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
        let sl = self.tys.intern(TyKind::Slice(elem));
        let r = self.tys.mk_ref(mutable, sl);
        self.tys.mk_option(r)
    }

    /// `str::get` (TRIAGE R26): any `SliceIndex<str>` range form, as
    /// for `[T]::get`, answering `Option<&str>`: `None` when a bound is
    /// out of range or not on a char boundary. A `usize` is no
    /// `SliceIndex<str>`, as in rustc.
    fn str_get_method(&mut self, e: ExprId, recv: ExprId, derefs: u8, name_span: Span, args: &[ExprId]) -> Ty {
        if args.len() != 1 {
            self.err("L0105", name_span, "`get` takes 1 argument", "Pass a range, such as `s.get(1..3)`.");
            return self.slice_bail(args);
        }
        let arg = args[0];
        let form = if matches!(self.p.ast.expr(arg), Expr::Range { .. }) {
            self.drain_range_form(e, arg, name_span)
        } else {
            let t = self.expr(arg, None);
            let t = self.deep(t);
            match self.drain_form_of(t, name_span) {
                Some(f) => Some(DrainRange::Value(f)),
                None if t == ERROR => return ERROR,
                None => {
                    let tn = self.tn(t);
                    self.err("L0612", name_span, format!("the type `str` cannot be indexed by `{tn}`"), "Pass a range, such as `s.get(1..3)`.");
                    return ERROR;
                }
            }
        };
        let Some(form) = form else { return ERROR };
        self.check_packed_borrow(recv, name_span);
        self.out.drain_ranges.push((e, form));
        self.set_res(e, Res::BuiltinMethod { b: Builtin::StrGetRange, derefs, autoref: Autoref::Ref });
        self.tys.mk_option(REF_STR)
    }

    /// An index expression `base[index]` whose index is a range
    /// value (not a syntactic range): the same slice place, with
    /// the form recorded for lowering (`Checked::index_range`).
    /// Returns the sliced type for a range form; None when the
    /// index is no range form. The index is checked (and coerced
    /// to `usize` for the plain form) in every case, so the caller
    /// must not expect it again.
    pub(super) fn range_value_index(&mut self, e: ExprId, index: ExprId, inner: Ty, derefs: u8, span: Span) -> Option<Ty> {
        let t = self.expr(index, None);
        let t = self.deep(t);
        let form = self.drain_form_of(t, span);
        match form {
            // A `(Bound, Bound)` index panics at core's own sites,
            // not the call's: not yet, as a plain mismatch.
            Some(DrainForm::Bounds | DrainForm::BoundsRef) => {
                self.coerce_expr(index, t, USIZE);
                None
            }
            Some(f) => {
                self.out.index_ranges.push((e, f));
                self.set_res(e, Res::SliceIndex { derefs });
                if self.kind(inner) == TyKind::Str || self.tys.is_string_ty(inner) {
                    return Some(STR);
                }
                let elem = match self.kind(inner) {
                    TyKind::Array(elem, _) | TyKind::Slice(elem) => Some(elem),
                    _ => self.tys.vec_elem(inner),
                };
                Some(match elem {
                    Some(elem) => self.tys.intern(TyKind::Slice(elem)),
                    None => ERROR,
                })
            }
            None => {
                self.coerce_expr(index, t, USIZE);
                None
            }
        }
    }

    /// `[S]::join` and `concat`: core's two families, over the
    /// element shapes lust takes. The `Borrow<str>` family (String
    /// and `&str` elements) answers a String and takes a `&str`
    /// separator; the `Borrow<[T]>` family (Vec, array, slice, and
    /// boxed-slice elements, `T: Clone`) answers a `Vec<T>` and
    /// takes a `&T` or `&[T]` separator. Any other element shape
    /// falls through to the normal dispatch (a user `Borrow` type
    /// or a plain no-method error, as rustc decides).
    #[allow(clippy::too_many_arguments)]
    fn slice_join_concat(
        &mut self,
        e: ExprId,
        recv: ExprId,
        elem: Ty,
        derefs: u8,
        name_span: Span,
        args: &[ExprId],
        is_join: bool,
    ) -> Option<Ty> {
        use Builtin as B;
        let str_family = elem == STRING
            || matches!(self.kind(elem), TyKind::Ref(_, Mut::Shared, i) if self.kind(i) == TyKind::Str)
            || self.param_borrows_only_str(elem);
        if str_family {
            let b = if is_join { B::SliceJoinStr } else { B::SliceConcatStr };
            self.check_packed_borrow(recv, name_span);
            self.set_res(e, Res::BuiltinMethod { b, derefs, autoref: Autoref::Ref });
            if is_join {
                self.check_args(&[REF_STR], args, name_span);
            } else {
                self.check_args(&[], args, name_span);
            }
            return Some(STRING);
        }
        // Another `Borrow<str>` element (also an instance of a `S:
        // Borrow<str>` template, which `check` accepted): std's
        // `Box<str>`, `Rc<str>`, `Arc<str>`, `Cow<str>`, and `&mut str`
        // take the str builtin (their `borrow` is a plain view); a
        // written impl's `borrow` fn goes in `index_recv` for lowering,
        // which calls it as core's join does (lower/iter.rs
        // `join_borrow`).
        let borrow_str = TraitRef { def: self.p.gx.lang.borrow, args: self.tys.intern_args(&[GenericArg::Ty(elem), GenericArg::Ty(STR)]), bindings: EMPTY_BINDINGS };
        if !matches!(self.kind(elem), TyKind::Param(_) | TyKind::Infer(_))
            && let Selection::Impl { id, args: impl_args, .. } = self.select_obligation(borrow_str)
        {
            let rec = self.p.gx.index.get(id).clone();
            let (b, ok) = if rec.synthetic != crate::traits::index::Synthetic::None {
                let b = if is_join { B::SliceJoinStr } else { B::SliceConcatStr };
                (b, self.std_borrow_str_elem(elem))
            } else {
                let b = if is_join { B::SliceJoinBorrow } else { B::SliceConcatBorrow };
                let p = self.p;
                let f = rec.items.iter().copied().find_map(|d| p.local_def(d.hash).filter(|&l| p.name(p.fn_info(l).name) == "borrow"));
                if let Some(f) = f {
                    let idx = self.out.index_recv.len();
                    self.out.index_recv.push((e, IndexRecv { f, args: Vec::new(), f_mut: None, args_mut: Vec::new() }));
                    if self.p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
                        self.deref_sites.push((DerefTable::Index, idx, false, f, impl_args));
                    }
                }
                (b, f.is_some())
            };
            // `concat` has no separator to pick the form: an element that
            // is also `Borrow<[T]>` fits both of core's `Concat` impls
            // (rustc E0284). An instance of a `S: Borrow<str>` template
            // keeps the `str` form its template chose.
            if !is_join && !self.is_instance_check() && self.borrows_a_slice(elem) {
                let tn = self.tn(elem);
                self.err(
                    "L0610",
                    name_span,
                    format!("type annotations needed: `concat` over `{tn}` fits both `Concat<str>` and `Concat<T>` (`{tn}` is `Borrow<str>` and `Borrow<[T]>`)"),
                    "Call `join(\"\")`: its `&str` separator picks the `str` form.",
                );
                return Some(self.slice_bail(args));
            }
            if !ok {
                let (tn, m) = (self.tn(elem), if is_join { "join" } else { "concat" });
                self.err("L0640", name_span, format!("`{m}` over `{tn}` elements is not implemented yet"), "Map the parts to `&str` first, as in `parts.iter().map(|p| p.borrow()).collect::<Vec<&str>>()`.");
                return Some(self.slice_bail(args));
            }
            self.check_packed_borrow(recv, name_span);
            self.set_res(e, Res::BuiltinMethod { b, derefs, autoref: Autoref::Ref });
            if is_join {
                self.check_args(&[REF_STR], args, name_span);
            } else {
                self.check_args(&[], args, name_span);
            }
            return Some(STRING);
        }
        let inner = match self.kind(elem) {
            TyKind::Array(el, _) => Some(el),
            TyKind::Ref(_, _, i) => match self.kind(i) {
                TyKind::Slice(el) => Some(el),
                _ => None,
            },
            _ => self.tys.vec_elem(elem).or_else(|| self.tys.boxed_slice_elem(elem)),
        }?;
        self.deferred_clone.push((inner, name_span));
        let ret = self.tys.mk_vec(inner);
        self.check_packed_borrow(recv, name_span);
        if !is_join {
            self.set_res(e, Res::BuiltinMethod { b: B::SliceConcatVec, derefs, autoref: Autoref::Ref });
            self.check_args(&[], args, name_span);
            return Some(ret);
        }
        if args.len() != 1 {
            let p0 = self.tys.mk_ref(false, inner);
            self.check_args(&[p0], args, name_span);
            return Some(ERROR);
        }
        let arg = args[0];
        let t = self.expr(arg, None);
        let t = self.deep(t);
        let slice_of_inner = |this: &mut Self, u: Ty| this.unify(u, inner);
        let (b, param): (B, Ty) = match self.kind(t) {
            TyKind::Ref(_, _, u) if matches!(self.kind(u), TyKind::Slice(_) | TyKind::Array(..)) => {
                let uel = match self.kind(u) {
                    TyKind::Slice(el) | TyKind::Array(el, _) => el,
                    _ => unreachable!(),
                };
                if slice_of_inner(self, uel) {
                    let sl = self.tys.intern(TyKind::Slice(inner));
                    (B::SliceJoinVecSlice, self.tys.mk_ref(false, sl))
                } else {
                    (B::SliceJoinVecElem, self.tys.mk_ref(false, inner))
                }
            }
            TyKind::Ref(_, _, u) if self.tys.vec_elem(u).is_some_and(|el| el == inner) => {
                let sl = self.tys.intern(TyKind::Slice(inner));
                (B::SliceJoinVecSlice, self.tys.mk_ref(false, sl))
            }
            _ => (B::SliceJoinVecElem, self.tys.mk_ref(false, inner)),
        };
        self.coerce_expr(arg, t, param);
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref: Autoref::Ref });
        Some(ret)
    }

    /// The written `Clone` impl's `clone_from` fn of a Copy type `el`
    /// (its `clone` when it has no `clone_from`), recorded in
    /// `index_recv` for the call `e`. None when the impl is not a
    /// written one.
    fn written_clone_fn(&mut self, e: ExprId, el: Ty, span: Span) -> Option<LocalDefId> {
        let tr = TraitRef { def: self.p.gx.lang.clone, args: self.tys.intern_args(&[GenericArg::Ty(el)]), bindings: EMPTY_BINDINGS };
        let Selection::Impl { id, args: impl_args, .. } = self.select_obligation_at(tr, span, 0) else { return None };
        let rec = self.p.gx.index.get(id).clone();
        if rec.synthetic != crate::traits::index::Synthetic::None {
            return None;
        }
        let p = self.p;
        let named = |n: &str| rec.items.iter().copied().find_map(|d| p.local_def(d.hash).filter(|&l| p.name(p.fn_info(l).name) == n));
        let f = named("clone_from").or_else(|| named("clone"))?;
        let idx = self.out.index_recv.len();
        self.out.index_recv.push((e, IndexRecv { f, args: Vec::new(), f_mut: None, args_mut: Vec::new() }));
        if self.p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
            self.deref_sites.push((DerefTable::Index, idx, false, f, impl_args));
        }
        Some(f)
    }

    /// True when `elem: Borrow<[T]>` holds for some `T` (or may hold):
    /// core's `Concat<T>` for `[V: Borrow<[T]>]` then fits too.
    fn borrows_a_slice(&mut self, elem: Ty) -> bool {
        let snap = self.snapshot_vars();
        let obl_len = self.obl_len();
        let v = self.new_var(false);
        let sl = self.tys.intern(TyKind::Slice(v));
        let tr = TraitRef { def: self.p.gx.lang.borrow, args: self.tys.intern_args(&[GenericArg::Ty(elem), GenericArg::Ty(sl)]), bindings: EMPTY_BINDINGS };
        let fits = matches!(self.select_obligation(tr), Selection::Impl { .. } | Selection::Ambiguous | Selection::ParamEvidence(_));
        self.rollback_vars(snap);
        self.obl_truncate(obl_len);
        fits
    }

    /// True for the std `Borrow<str>` elements whose C value cgen's
    /// str join reads as a `&str` view: `&mut str`, `Box<str>`,
    /// `Rc<str>`, `Arc<str>`, and `Cow<str>`.
    fn std_borrow_str_elem(&self, elem: Ty) -> bool {
        let arc = |t: Ty| (self.tys.builtin_of(t) == Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::Arc))).then(|| self.tys.adt_first_ty_arg(t)).flatten();
        matches!(self.kind(elem), TyKind::Ref(_, Mut::Mut, i) if i == STR)
            || self.tys.boxed_elem(elem) == Some(STR)
            || self.tys.rc_elem(elem) == Some(STR)
            || arc(elem) == Some(STR)
            || crate::check::collect::cow_arg(&self.tys, elem) == Some(STR)
    }

    /// A type parameter whose `Borrow` bounds all name `str` (`S:
    /// Borrow<str>`, ts-rust's `joined_parts`): the template takes the
    /// str family, and each instance checks again at its concrete
    /// element (String and `&str` take the builtin; any other shape
    /// rejects there). A second `Borrow<X>` bound makes rustc's
    /// `Concat` item ambiguous, so it stays out.
    fn param_borrows_only_str(&self, elem: Ty) -> bool {
        if !matches!(self.kind(elem), TyKind::Param(_)) {
            return false;
        }
        let borrow = self.p.gx.lang.borrow;
        let mut targets = self.env().iter().filter_map(|pred| match pred {
            Predicate::Trait(b) if b.value.def == borrow => match self.tys.args(b.value.args) {
                [GenericArg::Ty(s), GenericArg::Ty(t)] if *s == elem => Some(*t),
                _ => None,
            },
            _ => None,
        });
        let mut any = false;
        targets.all(|t| {
            any = true;
            t == STR
        }) && any
    }

    /// A comparison across sequence forms (slice, array, Vec) as
    /// core's asymmetric `PartialEq` impls allow them (and the
    /// slice `PartialOrd` coercions at equal reference depth):
    /// recorded as a slice comparison for lowering. None when the
    /// pair is not one of core's, so the caller's normal path
    /// answers (the same-type path, a written impl, or its error).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn seq_cmp(
        &mut self,
        e: ExprId,
        op: BinOp,
        lt: Ty,
        rt: Ty,
        ld: u8,
        lb: Ty,
        rd: u8,
        rb: Ty,
        span: Span,
    ) -> Option<Ty> {
        use BinOp::*;
        /// One side's sequence form.
        #[derive(Clone, Copy, PartialEq)]
        enum Form {
            Slice,
            Array,
            Vec,
        }
        let form = |this: &Self, b: Ty| -> Option<(Form, Ty, Option<crate::ty::ConstId>)> {
            match this.kind(b) {
                TyKind::Slice(el) => Some((Form::Slice, el, None)),
                TyKind::Array(el, c) => Some((Form::Array, el, Some(c))),
                _ => this.tys.vec_elem(b).map(|el| (Form::Vec, el, None)),
            }
        };
        let (lf, le, lc) = form(self, lb)?;
        let (rf, re, rc) = form(self, rb)?;
        // The same-type path already answers these.
        if ld == rd && self.deep(lb) == self.deep(rb) {
            return None;
        }
        if lf == Form::Array && rf == Form::Array {
            let same_n = match (lc, rc) {
                (Some(a), Some(b)) if a == b => true,
                (Some(a), Some(b)) => match (self.tys.const_kind(a), self.tys.const_kind(b)) {
                    (crate::ty::ConstKind::Int(x), crate::ty::ConstKind::Int(y)) => x == y,
                    _ => false,
                },
                _ => false,
            };
            if !same_n {
                return None;
            }
        }
        let eq_op = matches!(op, Eq | Ne);
        let last_mut = |this: &Self, t: Ty| this.ref_layers(t).last().copied().unwrap_or(false);
        let allowed = if eq_op {
            if ld == rd {
                matches!(
                    (lf, rf),
                    (Form::Slice, Form::Slice)
                        | (Form::Array, Form::Array)
                        | (Form::Vec, Form::Vec)
                        | (Form::Array, Form::Slice)
                        | (Form::Slice, Form::Array)
                        | (Form::Vec, Form::Slice)
                        | (Form::Slice, Form::Vec)
                        | (Form::Vec, Form::Array)
                )
            } else if rd == ld + 1 {
                match (lf, rf) {
                    (Form::Array, Form::Slice) | (Form::Vec, Form::Slice) => true,
                    // `Vec<T>: PartialEq<&[U; N]>` exists; the
                    // `&mut [U; N]` form is the omitted one.
                    (Form::Vec, Form::Array) => !last_mut(self, rt),
                    _ => false,
                }
            } else if ld == rd + 1 {
                matches!((lf, rf), (Form::Slice, Form::Array) | (Form::Slice, Form::Vec))
            } else {
                false
            }
        } else {
            // Ordering needs the same mutability layers, as the
            // caller's own check has it.
            ld == rd
                && self.ref_layers(lt) == self.ref_layers(rt)
                && (matches!((lf, rf), (Form::Slice, Form::Slice) | (Form::Array, Form::Array) | (Form::Vec, Form::Vec))
                    || (ld >= 1 && lf == Form::Slice && rf != Form::Slice))
        };
        if !allowed {
            return None;
        }
        let snap = self.snapshot_vars();
        if !self.unify(le, re) {
            self.rollback_vars(snap);
            // Elements of two string types (`["a"] == &[String]`): core's
            // sequence impls take `T: PartialEq<U>`, and the string pairs
            // are the ones `==` takes. Lowering compares them one by one.
            let (eld, elb) = self.autoderef(le);
            let (erd, erb) = self.autoderef(re);
            let strings = match (self.str_kind(elb, true), self.str_kind(erb, true)) {
                (Some(a), Some(b)) => elb != erb && string_eq_ok(eld, a, erd, b),
                _ => false,
            };
            if !eq_op || !strings {
                return None;
            }
            self.out.seq_cmps.push(e);
            self.set_res(e, Res::Bin { ld, rd });
            return Some(BOOL);
        }
        let lbd = self.deep(lb);
        let ok = if eq_op {
            crate::check::collect::has_eq(self.p, &self.tys, lbd)
        } else {
            crate::check::collect::has_ord(self.p, &self.tys, lbd)
        };
        if !ok {
            let tn = self.tn(lbd);
            let fix = if eq_op {
                "Add #[derive(PartialEq)] to the type."
            } else {
                "Add #[derive(PartialOrd)] to the type, or implement `PartialOrd` for it."
            };
            self.err("L0112", span, format!("type `{tn}` cannot be compared with `{}`", op.symbol()), fix);
            self.set_res(e, Res::Bin { ld, rd });
            return Some(BOOL);
        }
        let le = self.deep(le);
        let sl = self.tys.intern(TyKind::Slice(le));
        self.record_glue_reads(self.p.gx.lang.partial_eq, sl);
        self.out.seq_cmps.push(e);
        self.set_res(e, Res::Bin { ld, rd });
        Some(BOOL)
    }

    /// Checks the arguments with no expectations and answers the
    /// error type: the bail-out of a slice method already reported.
    /// The R4 slice and Vec methods (tf-small-a): `[u8]::eq_ignore_ascii_case`
    /// and `is_ascii`, `[T]::rotate_left`/`rotate_right` and
    /// `partition_point`, and on `Vec<T>` only `extend_from_within`,
    /// `resize_with`, `dedup_by`, and `dedup_by_key`. None for a name
    /// outside the list or a receiver the method does not take (a byte
    /// method on a non-`u8` element, a Vec method on a slice), so the
    /// normal dispatch rejects it.
    #[allow(clippy::too_many_arguments)]
    fn slice_method_r4(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        elem: Ty,
        derefs: u8,
        n: &str,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
    ) -> Option<Ty> {
        use Builtin as B;
        let bytes = self.resolve(elem) == int(IntTy::U8);
        let is_vec = self.tys.vec_elem(base).is_some();
        let (b, autoref, params, ret): (B, Autoref, Vec<Ty>, Ty) = match n {
            "eq_ignore_ascii_case" if bytes => {
                let sl = self.tys.intern(TyKind::Slice(elem));
                let r = self.tys.mk_ref(false, sl);
                (B::SliceEqIgnoreAsciiCase, Autoref::Ref, vec![r], BOOL)
            }
            "is_ascii" if bytes => (B::SliceIsAscii, Autoref::Ref, vec![], BOOL),
            // `[u8]`'s ASCII case maps: a copy, or in place.
            "to_ascii_lowercase" | "to_ascii_uppercase" if bytes => {
                let v = self.tys.mk_vec(elem);
                (B::SliceToAsciiCase(n == "to_ascii_uppercase"), Autoref::Ref, vec![], v)
            }
            "make_ascii_lowercase" | "make_ascii_uppercase" if bytes => (B::SliceMakeAsciiCase(n == "make_ascii_uppercase"), Autoref::RefMut, vec![], UNIT),
            // `<[T]>::repeat(n)`, `T: Copy` (alloc's slice.rs).
            "repeat" => {
                let el = self.deep(elem);
                if self.tys.flags(el).contains_infer() {
                    self.deferred_copy.push((el, name_span));
                } else if !crate::check::collect::is_copy(self.p, &self.tys, el) {
                    let tn = self.tn(el);
                    self.err(
                        "L0110",
                        name_span,
                        format!("the trait `Copy` is not implemented for `{tn}`"),
                        "`repeat` copies the elements: use a Copy element type, or clone them in a loop.",
                    );
                    return Some(self.slice_bail(args));
                }
                let v = self.tys.mk_vec(elem);
                (B::SliceRepeat, Autoref::Ref, vec![USIZE], v)
            }
            "rotate_left" => (B::SliceRotateLeft, Autoref::RefMut, vec![USIZE], UNIT),
            "rotate_right" => (B::SliceRotateRight, Autoref::RefMut, vec![USIZE], UNIT),
            "partition_point" => {
                // `P: FnMut(&T) -> bool`, the reference higher-ranked.
                let r = self.tys.mk_ref(false, elem);
                let f = self.fn_mut_param_ref(&[r], BOOL, name_span);
                (B::SlicePartitionPoint, Autoref::Ref, vec![f], USIZE)
            }
            "extend_from_within" if is_vec => {
                if !turbofish.is_empty() {
                    self.errs.push(not_yet("L0721", name_span, "turbofish on `extend_from_within`"));
                    return Some(self.slice_bail(args));
                }
                if args.len() != 1 {
                    self.err("L0105", name_span, "`extend_from_within` takes 1 argument", "Pass the source range.");
                    return Some(self.slice_bail(args));
                }
                self.deferred_clone.push((elem, name_span));
                let Some(form) = self.drain_range_form(e, args[0], name_span) else { return Some(ERROR) };
                self.check_packed_borrow(recv, name_span);
                self.out.drain_ranges.push((e, form));
                self.set_res(e, Res::BuiltinMethod { b: B::VecExtendFromWithin, derefs, autoref: Autoref::RefMut });
                return Some(UNIT);
            }
            "resize_with" if is_vec => {
                let f = self.fn_mut_param(&[], elem, name_span);
                (B::VecResizeWith, Autoref::RefMut, vec![USIZE, f], UNIT)
            }
            "dedup_by" if is_vec => {
                // `F: FnMut(&mut T, &mut T) -> bool`, both higher-ranked.
                let r = self.tys.mk_ref(true, elem);
                let f = self.fn_mut_param_ref(&[r, r], BOOL, name_span);
                (B::VecDedupBy, Autoref::RefMut, vec![f], UNIT)
            }
            "dedup_by_key" if is_vec => {
                // `F: FnMut(&mut T) -> K`, `K: PartialEq`.
                let key = self.new_var(false);
                let r = self.tys.mk_ref(true, elem);
                let f = self.fn_mut_param_ref(&[r], key, name_span);
                self.deferred_eq.push((key, name_span));
                (B::VecDedupByKey, Autoref::RefMut, vec![f], UNIT)
            }
            _ => return None,
        };
        if !turbofish.is_empty() {
            self.errs.push(not_yet("L0721", name_span, "turbofish on this slice method"));
            return Some(self.slice_bail(args));
        }
        self.check_packed_borrow(recv, name_span);
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
        self.check_args(&params, args, name_span);
        // A `dyn FnMut` callable has no adapter call (cgen/slices.rs,
        // lower/iter.rs `call_fn`).
        if matches!(b, B::SlicePartitionPoint | B::VecDedupBy | B::VecDedupByKey | B::VecResizeWith) && self.adapter_callable_gap(args, &params, false) {
            return Some(ERROR);
        }
        Some(ret)
    }

    /// `Vec::splice(range, replace_with)` (R4). Taken as an expression
    /// statement only: its `Splice` then drops at once, and the call is
    /// core's drain plus `Splice::drop`. The replacement is a builtin
    /// `TrustedLen` iterator (or a collection that turns into one), so
    /// its size hint is exact and nothing is left to collect. The range
    /// records like drain's.
    #[allow(clippy::too_many_arguments)]
    fn splice_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        elem: Ty,
        derefs: u8,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
    ) -> Ty {
        if !turbofish.is_empty() {
            self.errs.push(not_yet("L0721", name_span, "turbofish on `splice`"));
            return self.slice_bail(args);
        }
        if args.len() != 2 {
            self.err("L0105", name_span, "`splice` takes 2 arguments", "Pass the range and the replacement items.");
            return self.slice_bail(args);
        }
        if self.stmt_expr != Some(e) {
            self.errs.push(not_yet("L0641", name_span, "`splice` whose `Splice` value is used (lust takes `v.splice(range, items);` as a statement)"));
            return self.slice_bail(args);
        }
        let Some(form) = self.drain_range_form(e, args[0], name_span) else {
            self.expr(args[1], None);
            return ERROR;
        };
        let at = self.expr(args[1], None);
        let at = self.deep(at);
        let it = match self.into_iter_ty(at) {
            Some(it) if self.splice_trusted(it) => it,
            Some(_) => {
                self.errs.push(not_yet("L0641", self.span(args[1]), "`splice` with this replacement (lust takes slices, Vecs, arrays, and their std iterators)"));
                return ERROR;
            }
            None => {
                let tn = self.tn(at);
                self.err("L0612", self.span(args[1]), format!("`{tn}` is not an iterator lust can splice in"), "Pass an iterator, a slice, an array, or a Vec.");
                return ERROR;
            }
        };
        let item = self.iter_item(it);
        if !self.unify(item, elem) {
            self.mismatch(self.span(args[1]), elem, item);
            return ERROR;
        }
        self.check_packed_borrow(recv, name_span);
        self.out.drain_ranges.push((e, form));
        self.set_res(e, Res::BuiltinMethod { b: Builtin::VecSplice, derefs, autoref: Autoref::RefMut });
        UNIT
    }

    /// True for the replacement iterators `splice` takes: std
    /// `TrustedLen` kinds with an exact size hint.
    fn splice_trusted(&mut self, t: Ty) -> bool {
        use crate::ty::iter::IterKind as K;
        let t = self.deep(t);
        match crate::ty::iter::iter_parts(&self.tys, t) {
            Some((K::SliceIter | K::SliceIterMut | K::VecIntoIter | K::ArrayIntoIter, _)) => true,
            Some((K::Copied | K::Cloned | K::Map | K::Rev | K::Enumerate, a)) => self.splice_trusted(a[0]),
            _ => false,
        }
    }

    fn slice_bail(&mut self, args: &[ExprId]) -> Ty {
        for &a in args {
            self.expr(a, None);
        }
        ERROR
    }
}

/// True when `t` is a Copy type whose `Clone` is core's or derived all the
/// way down (core's `TrivialClone`): primitives, references, raw and fn
/// pointers, tuples, arrays and `Option` of such, and local Adts that
/// derive both `Clone` and `Copy` with such fields. A written `Clone` impl
/// anywhere makes it false; so does any type this walk does not know.
fn trivial_clone(p: &crate::check::collect::Program, tys: &impl TyIntern, t: Ty) -> bool {
    fn go(p: &crate::check::collect::Program, tys: &impl TyIntern, t: Ty, depth: u32) -> bool {
        if depth > 32 {
            return false;
        }
        match tys.kind(t) {
            TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Never => true,
            TyKind::Ref(_, m, _) => !m.is_mut(),
            TyKind::RawPtr(..) | TyKind::FnPtr(_) | TyKind::FnDef(..) => true,
            TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| go(p, tys, e, depth + 1)),
            TyKind::Array(e, _) => go(p, tys, e, depth + 1),
            _ => {
                if let Some(e) = tys.option_elem(t) {
                    return go(p, tys, e, depth + 1);
                }
                let Some(a) = tys.local_adt(t) else { return false };
                let d = p.derives_of(a);
                if !(d.clone && d.copy) {
                    return false;
                }
                let args: Vec<GenericArg> = match tys.kind(t) {
                    TyKind::Adt(_, a) => tys.args(a).to_vec(),
                    _ => Vec::new(),
                };
                if !args.is_empty() {
                    return false;
                }
                p.adt(a).variants.iter().all(|v| v.fields.iter().all(|f| go(p, tys, f.ty, depth + 1)))
            }
        }
    }
    go(p, tys, t, 0)
}
