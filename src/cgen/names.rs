// Release C names (`LUST_RELEASE_C=1` one-shot builds, driver/release_c.rs): the C a
// unit gets depends only on its own fns, so a content-keyed object cache can reuse it
// across commits, machines and CI runs. Dev builds and the daemon never set the context
// and print numbered names, as before:
//   fn bodies     f<slot>               -> f_<id>, extern, called directly
//   trampolines   tramp<slot>           -> tramp_<id>, extern
//   table calls   (CAST lust_fns[slot]) -> (CAST f_<id>), with the callee's prototype
//   fn pointers   lust_tramps[slot]     -> tramp_<id>
//   Adts          A<id> (rank by hash)  -> A<def hash> or A<instance key hash>
//   panic sites   slot << 40 | ...      -> lust_so_<id> | ..., the slot (shifted) from
//                                          the location unit's side table
//   vtables       vt<slot>_<vtable id>  -> vt_<id>_<n>, n counted in the fn
// `<id>` is 16 hex digits of a hash of the fn's `DiskDefId` (def path plus instance
// args). Every name that leaves its fn (a callee, a fn pointer, a location slot) is
// recorded as an extern declaration the unit prints (`FnOut::externs`).
use super::*;
use std::cell::RefCell;
use std::sync::Arc;

/// The stable names of one program's release C.
pub struct Names {
    /// By slot: the fn's id (16 hex digits), None for a slot with no fn.
    pub fns: Vec<Option<String>>,
    /// By Adt id: the name after `A`/`N` (`d<def hash>` or `i<instance key hash>`).
    pub adts: Vec<String>,
    /// The slot of each fn id, built on first use (`slot_of_id`).
    pub by_id: std::sync::OnceLock<crate::intern::FxMap<String, u32>>,
}

/// The slot whose fn has id `id` (16 hex digits), in release C.
pub(crate) fn slot_of_id(id: &str) -> Option<u32> {
    CUR.with(|c| {
        let n = c.borrow();
        let n = n.as_ref()?;
        let map = n.by_id.get_or_init(|| n.fns.iter().enumerate().filter_map(|(s, id)| Some((id.clone()?, s as u32))).collect());
        map.get(id).copied()
    })
}

thread_local! {
    static CUR: RefCell<Option<Arc<Names>>> = const { RefCell::new(None) };
}

/// Runs `f` with `names` as this thread's naming context (None: numbered names).
pub fn with<R>(names: Option<&Arc<Names>>, f: impl FnOnce() -> R) -> R {
    let old = CUR.with(|c| c.replace(names.cloned()));
    let r = f();
    CUR.with(|c| *c.borrow_mut() = old);
    r
}

/// This thread's naming context (`with`), for work it hands to other threads.
pub(crate) fn current() -> Option<Arc<Names>> {
    CUR.with(|c| c.borrow().clone())
}

/// True while this thread emits release C.
pub(crate) fn release() -> bool {
    CUR.with(|c| c.borrow().is_some())
}

fn fn_id(slot: u32) -> Option<String> {
    CUR.with(|c| c.borrow().as_ref().map(|n| n.fns.get(slot as usize).cloned().flatten().unwrap_or_else(|| format!("dead{slot}"))))
}

/// `A<id>` for Adt `a`.
pub(crate) fn adt(a: AdtId) -> String {
    CUR.with(|c| match c.borrow().as_ref() {
        Some(n) => format!("A{}", n.adts.get(a.0 as usize).map_or("x", String::as_str)),
        None => format!("A{}", a.0),
    })
}

/// `N<id>` for the unsized Adt `a`.
pub(crate) fn unsized_adt(a: AdtId) -> String {
    CUR.with(|c| match c.borrow().as_ref() {
        Some(n) => format!("N{}", n.adts.get(a.0 as usize).map_or("x", String::as_str)),
        None => format!("N{}", a.0),
    })
}

/// The C name of the body of the fn in `slot`.
pub(crate) fn body(slot: u32) -> String {
    fn_id(slot).map_or_else(|| format!("f{slot}"), |id| format!("f_{id}"))
}

/// The fn id of `slot` in release C (None: numbered names or no fn). The slot's own
/// entry decides: an id is 16 hex digits and may start with `dead` like `fn_id`'s
/// placeholder for an empty slot.
pub(crate) fn fn_tag_opt(slot: u32) -> Option<String> {
    CUR.with(|c| c.borrow().as_ref().and_then(|n| n.fns.get(slot as usize).cloned().flatten()))
}

/// The C name of the trampoline of the fn in `slot`.
pub(crate) fn tramp(slot: u32) -> String {
    fn_id(slot).map_or_else(|| format!("tramp{slot}"), |id| format!("tramp_{id}"))
}

/// The part of a per-fn C name that names the fn in `slot`: the slot number, or its id
/// in release C (`lust_splitp_<tag>_<n>`, `stramp<tag>`, `vt<tag>_<n>`).
pub(crate) fn fn_tag(slot: u32) -> String {
    fn_id(slot).unwrap_or_else(|| slot.to_string())
}

/// The callee text for a call of fn `f` (in `slot`) through `cast` (`fn_ptr_cast`):
/// `(CAST lust_fns[slot])` numbered, `(CAST f_<id>)` in release C, which records the
/// callee's prototype in `externs`.
pub(crate) fn callee(p: &Program, f: LocalDefId, slot: u32, externs: &mut BTreeSet<String>) -> String {
    let cast = fn_ptr_cast(p, f);
    match fn_id(slot) {
        None => format!("({cast}lust_fns[{slot}])"),
        Some(id) => {
            externs.insert(format!("{};\n", fn_sig_named(p, f, &format!("f_{id}"))));
            format!("({cast}f_{id})")
        }
    }
}

/// A fn pointer value for fn `f`: `lust_tramps[slot]` numbered, its trampoline in release
/// C (prototype recorded in `externs`).
pub(crate) fn fn_value(p: &Program, f: LocalDefId, slot: u32, externs: &mut BTreeSet<String>) -> String {
    match fn_id(slot) {
        None => format!("lust_tramps[{slot}]"),
        Some(id) => {
            let t = trampoline(p, f, slot);
            if let Some(head) = t.split(" {").next() {
                externs.insert(format!("{};\n", head.strip_prefix("static ").unwrap_or(head)));
            }
            format!("(lust_fnptr)tramp_{id}")
        }
    }
}

/// A panic location of the fn in `slot`: the packed number numbered; in release C the
/// slot comes from the location unit's `lust_so_<id>` (recorded in `externs`), already
/// shifted to its bits (`slot << 40`), so the text holds only the line within the fn and
/// the column and the word is one load and one or. The slot is read through `LUST_SO`
/// (runtime.h), a volatile read: a panic site is cold, and a plain read of the extern
/// constant was hoisted into the fn's hot path (0.28 G loads on the pgo-train set). A
/// `#[track_caller]` call's argument takes `hot_loc` of this text.
pub(crate) fn loc(slot: u32, rel: u64, col: u64, externs: &mut BTreeSet<String>) -> String {
    match fn_id(slot) {
        None => format!("{}u", ((slot as u64) << 40) | (rel << 20) | col),
        Some(id) => {
            externs.insert(format!("extern const uint64_t lust_so_{id};\n"));
            format!("(LUST_SO(lust_so_{id}) | {}ull)", (rel << 20) | col)
        }
    }
}

/// A `#[track_caller]` fn's location word, built where one of its panics reports it from
/// the two parameters its caller passes (`ltc_so`, `ltc_low`; `cgen::fn_sig`): read volatile,
/// so each panic path keeps its own read, as `loc`'s.
pub(crate) const LTC_WORD: &str = "(LUST_SO(*ltc_so) | ltc_low)";

/// The two arguments that pass `loc`'s location to a `#[track_caller]` callee: the address
/// of the slot constant and the line and column bits. Both are constants of the call site,
/// so where the C compiler inlines the callee they cost nothing until a panic path uses
/// them (a loaded word was built at the site and held in a register for the whole fn). A
/// fn that is itself `#[track_caller]` passes its own on; a constant word goes with
/// `lust_so_none` (runtime.h, 0).
pub(crate) fn hot_loc(loc: &str) -> String {
    if loc == LTC_WORD {
        return "ltc_so, ltc_low".to_string();
    }
    match loc.strip_prefix("(LUST_SO(").and_then(|r| r.split_once(") | ")) {
        Some((sym, low)) => format!("&{sym}, {}", low.strip_suffix(')').unwrap_or(low)),
        None => format!("&lust_so_none, {loc}"),
    }
}

/// The location unit of release C: `loc_unit`'s line and file tables plus a
/// `lust_so_<id>` per live fn (the slot its panic sites pack). The tables are indexed
/// canonically, a live fn by its rank by id and a file by its rank by path, so the unit
/// is a function of the program: the slot numbers and file ids a disk cache or a front
/// image carried over from earlier builds do not reach the binary. With `elf` (an ELF
/// target) the words are one array, `lust_so_tab`, and each `lust_so_<id>` an assembler
/// alias of its element: the same symbols, addresses and values as the constants (so the
/// same binary), and a unit that compiles about 3x faster than one C constant per fn
/// (tsgo's 78k: 1.8 s -> 0.55 s).
pub(crate) fn loc_unit(live: &[u32], files: &SlotFiles, slot_lines: &[u32], elf: bool) -> String {
    let mut fns: Vec<(String, u32)> = live.iter().filter_map(|&s| fn_id(s).map(|id| (id, s))).collect();
    fns.sort_unstable();
    let file_of = |s: u32| files.of_slot.get(s as usize).copied().unwrap_or(0) as usize;
    let mut paths: Vec<&str> = fns.iter().map(|&(_, s)| files.paths.get(file_of(s)).copied().unwrap_or("")).collect();
    paths.sort_unstable();
    paths.dedup();
    let of_slot: Vec<u32> = fns
        .iter()
        .map(|&(_, s)| paths.binary_search(&files.paths.get(file_of(s)).copied().unwrap_or("")).unwrap_or(0) as u32)
        .collect();
    let lines: Vec<u32> = fns.iter().map(|&(_, s)| slot_lines.get(s as usize).copied().unwrap_or(0)).collect();
    let mut c = super::loc_unit(&SlotFiles { paths: &paths, of_slot: &of_slot }, &lines);
    if elf && !fns.is_empty() {
        let words: Vec<String> = (0..fns.len()).map(|k| format!("{}ull", (k as u64) << 40)).collect();
        // 8-aligned as each constant is: a C compiler aligns a large array to 16, which moved
        // every word 8 bytes when the line tables before it ended at 4 or 8 mod 16.
        c.push_str(&format!("const uint64_t lust_so_tab[{}] __attribute__((aligned(8))) = {{{}}};\n__asm__(\n", fns.len(), words.join(",")));
        for (k, (id, _)) in fns.iter().enumerate() {
            c.push_str(&format!("\".globl lust_so_{id}\\n.set lust_so_{id}, lust_so_tab+{}\\n\"\n", 8 * k));
        }
        c.push_str(");\n");
    } else {
        for (k, (id, _)) in fns.iter().enumerate() {
            c.push_str(&format!("const uint64_t lust_so_{id} = {}ull;\n", (k as u64) << 40));
        }
    }
    c
}

/// The glue in other shards that a shard's `keys` call, as inline definitions in the shard:
/// small plain glue (`INLINE_BYTES`, no statics, attributes or macros, as `fn_unit_parts`
/// picks for fn units), level by level in prototype order within `inline_glue_budget`.
/// A struct's drop glue then inlines its fields' drops (an `Option<Rc<dyn>>`'s test), and
/// a hash table's equality glue its key's `eq`, instead of calling across shards.
fn shard_inline_glue<'g>(g: &'g GlueSet, keys: &[&'g (Glue, CTy)]) -> Vec<&'g (Glue, CTy)> {
    if !inline_on() {
        return Vec::new();
    }
    let plain = |k: &(Glue, CTy)| {
        g.def_map.get(k).is_some_and(|d| d.len() <= INLINE_BYTES && !d.contains("static ") && !d.contains("__attribute__") && !d.contains("#define"))
    };
    let mut seen: crate::intern::FxSet<&(Glue, CTy)> = keys.iter().copied().collect();
    let mut out = Vec::new();
    let mut budget = inline_glue_budget();
    let mut level: Vec<&(Glue, CTy)> = keys.to_vec();
    while !level.is_empty() {
        let mut next: Vec<&(Glue, CTy)> = level.iter().flat_map(|k| g.deps.get(*k).into_iter().flatten()).filter(|d| seen.insert(*d)).collect();
        next.sort_by(|a, b| g.protos[*a].cmp(&g.protos[*b]));
        next.retain(|d| {
            let n = g.def_map.get(*d).map_or(usize::MAX, |s| s.len());
            plain(d) && n <= budget && {
                budget -= n;
                true
            }
        });
        out.extend(next.iter().copied());
        level = next;
    }
    // B1 (`record`): the pick read the entry of every key it looked at.
    if record::on() {
        seen.iter().for_each(|k| record::read(record::Read::Glue(k.0, k.1.clone())));
    }
    out
}

/// Release C glue: every glue definition lives in exactly one shard, and fn units hold
/// only prototypes (`GlueSet::shared` holds every key). Shards are content-defined
/// chunks of the keys in prototype order, cut by each key's prototype and definition size
/// (`cut_after`), so new glue changes only the shard it lands in. Each shard declares the
/// types its definitions read (by value with blocks, one step deep only for glue that reads
/// through pointers, as fn units declare their inline glue), prototypes (its keys' and their callees') and
/// externs its definitions need, and holds inline definitions of the small glue its keys
/// call from other shards (`shard_inline_glue`). Only the keys the fns in `out` reach (a dead slot's `FnOut`
/// is empty), as a cold build has them: a session's set also keeps keys no fn reaches now
/// (stale since a refresh, or left by a removed fn).
pub fn glue_shards(p: &Program, g: &GlueSet, out: &[FnOut], target: usize) -> Vec<String> {
    glue_shard_texts(p, g, &glue_shard_keys(g, out, target), &[], false).into_iter().map(|(c, _)| c).collect()
}

/// The keys of each of `glue_shards`' shards, in order: the cut, cheap next to the texts
/// (`glue_shard_texts`), so a caller knows how many shards there are before it makes them.
pub fn glue_shard_keys<'a>(g: &'a GlueSet, out: &'a [FnOut], target: usize) -> Vec<Vec<&'a (Glue, CTy)>> {
    let live = g.closure(out.iter().flat_map(|o| o.glue.iter()));
    // Each key with a definition, with its prototype and definition size, looked up once: the
    // sort compares strings (tsgo: 23k keys, a lookup hashes a CTy tree).
    let mut keys: Vec<(&str, usize, &(Glue, CTy))> = live
        .into_iter()
        .filter_map(|k| {
            let len = g.def_map.get(k)?.len();
            Some((g.protos[k].as_str(), len, k))
        })
        .collect();
    keys.sort_by(|a, b| a.0.cmp(b.0));
    let mut shards: Vec<Vec<&(Glue, CTy)>> = Vec::new();
    let mut cur = Vec::new();
    for (proto, len, k) in keys {
        cur.push(k);
        if cut_after(proto, len, target.max(1) as u64) {
            shards.push(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() {
        shards.push(cur);
    }
    shards
}

/// A shard's B1 record (`record::close`): one hash of its pieces, and its reads.
pub type ShardRecord = Option<((u64, u64), Vec<record::Read>)>;

/// The texts of `glue_shards`' shards, from their keys (`glue_shard_keys`). A shard that `skip`
/// marks is not made (its text is empty: B1 found it clean). With `rec`, each shard made comes
/// with its record (B1, `record`): every byte of its text is a piece, and every glue entry and
/// type it read a read, so the next build can tell it is the same without making it.
pub fn glue_shard_texts(p: &Program, g: &GlueSet, shards: &[Vec<&(Glue, CTy)>], skip: &[bool], rec: bool) -> Vec<(String, ShardRecord)> {
    // Each shard is its own unit: built in parallel (in order), each worker
    // under this thread's naming context, in one layout phase (the program is
    // frozen: a worker keeps its `c_layout` answers across its shards).
    let names = CUR.with(|c| c.borrow().clone());
    let tag = super::layout_phase();
    // One definition of each type for all of them (`DeclCache`).
    let decls = std::sync::Arc::new(super::DeclCache::default());
    crate::pool::par_map(&(0..shards.len()).collect::<Vec<_>>(), |&j| {
        if skip.get(j).copied().unwrap_or(false) {
            return (String::new(), None);
        }
        let keys = &shards[j];
        if rec {
            record::open();
        }
        let c = super::in_layout_phase(tag, || with(names.as_ref(), || super::with_decl_cache(&decls, || {
            let mut c = unit_header();
            record::piece(record::Kind::Fixed, 0, &c);
            if p.unwind_tables {
                c.push_str(noreturn_decls());
                record::piece(record::Kind::Fixed, 1, noreturn_decls());
            }
            // What each definition reads, as a fn unit's inline copy of it does (`fn_unit_parts`):
            // glue that passes its fields on holds its types by value and only names the rest; a
            // pointer's drop or clone holds the block it reads in place; other glue (Debug, hash)
            // reads through pointers, one step deep. A dep's prototype takes its type by pointer.
            let (mut types, mut named, mut deep) = (HashSet::new(), HashSet::new(), HashSet::new());
            let mut protos: BTreeSet<&str> = BTreeSet::new();
            let mut externs: BTreeSet<&str> = BTreeSet::new();
            let inl = shard_inline_glue(g, keys);
            let read = |k: &(Glue, CTy)| {
                if record::on() {
                    record::read(record::Read::Glue(k.0, k.1.clone()));
                }
            };
            for k in keys.iter().chain(&inl) {
                read(k);
                if GlueSet::passes_fields(k) {
                    g.held_types(k, &mut types, &mut named);
                } else if let Some(blocks) = GlueSet::pointer_block(k) {
                    types.extend(blocks);
                    g.held_types(k, &mut types, &mut named);
                } else {
                    g.def_types(k, &mut deep);
                }
                protos.insert(&g.protos[*k]);
                for d in g.deps.get(*k).into_iter().flatten() {
                    read(d);
                    collect_types(&d.1, &mut named);
                    protos.insert(&g.protos[d]);
                }
                externs.extend(g.externs.get(*k).into_iter().flatten().map(String::as_str));
            }
            // Every declaration of an inline definition says `inline` (C99: one that does
            // not makes it a second external definition).
            for k in &inl {
                protos.remove(g.protos[*k].as_str());
            }
            named.retain(|t| !types.contains(t) && !deep.contains(t));
            type_decls_with(p, &mut c, &types, &named, Decls::ByValue { blocks: super::blocks_on() }, &deep);
            let m = c.len();
            externs.into_iter().for_each(|e| c.push_str(e));
            record::piece(record::Kind::Externs, 0, &c[m..]);
            for x in protos {
                let m = c.len();
                c.push_str(x);
                record::piece(record::Kind::GlueProto, record::key(x), &c[m..]);
            }
            for k in &inl {
                let m = c.len();
                c.push_str("inline ");
                c.push_str(&g.protos[*k]);
                record::piece(record::Kind::GlueProto, record::key(&g.protos[*k]), &c[m..]);
            }
            for k in &inl {
                let m = c.len();
                c.push_str("inline ");
                c.push_str(&g.def_map[*k]);
                record::piece(record::Kind::GlueDef, record::key(&g.protos[*k]), &c[m..]);
            }
            for k in keys {
                let m = c.len();
                c.push_str(&g.def_map[*k]);
                record::piece(record::Kind::GlueDef, record::key(&g.protos[*k]), &c[m..]);
            }
            c
        })));
        let r = if rec { record::close(&c) } else { None };
        (c, r)
    })
}

/// Release C statics: the data of every static, with the types it names (the glue lives
/// in `glue_shards`).
pub fn statics_unit(p: &Program, g: &GlueSet) -> String {
    let mut c = unit_header();
    // Defined: what the data holds by value, and the promoted values it points at (each
    // has its own definition here). Another static, a fn or glue it points at needs only
    // a forward typedef, so the unit does not change when a type behind a pointer does.
    let mut held = Vec::new();
    let mut types = HashSet::new();
    let mut pointed = HashSet::new();
    let mut fns = Vec::new();
    for (i, st) in p.statics.iter().enumerate().filter(|&(i, _)| p.static_live(i)) {
        let t = cty(&p.tys, st.ty);
        by_value_deps(&t, &mut held);
        collect_types(&t, &mut pointed);
        collect_promoted(p, &st.value, &t, &mut types);
        const_fns(&st.value, &mut fns);
        // A thread_local's native cell is defined here, by value.
        if let Some(cell) = super::native_tls_cell(p, i) {
            by_value_deps(&cell, &mut held);
        }
    }
    types.extend(held);
    // The data's fn pointers point at this unit's own copies of their trampolines
    // (`const_init`), which take and return the fns' values by value.
    for f in fns {
        let info = p.fn_info(LocalDefId(f));
        for &t in info.params.iter().chain([&info.ret]) {
            collect_types(&cty(&p.tys, t), &mut types);
        }
    }
    let data = static_defs(p, &g.slots);
    // Only the glue the data names (a vtable's drop entry, say): the unit must not
    // change when unrelated glue comes or goes.
    let named = names_in(&data, g.protos.values().map(|proto| proto_name(proto)));
    let mut protos: Vec<&String> = Vec::new();
    for (k, proto) in &g.protos {
        if named.contains(proto_name(proto)) {
            collect_types(&k.1, &mut pointed);
            protos.push(proto);
        }
    }
    protos.sort();
    pointed.retain(|t| !types.contains(t));
    // No blocks: an initializer names the fields of every type its value holds.
    type_decls_with(p, &mut c, &types, &pointed, Decls::ByValue { blocks: false }, &HashSet::new());
    protos.into_iter().for_each(|x| c.push_str(x));
    c.push_str(&data);
    c
}

/// The C types the data of `statics` reads: what it holds by value and the promoted values it
/// points at (`held`), and what it only points at (`pointed`), with the types of the
/// trampolines of its fn pointers (their bodies' parameters and results).
fn statics_types(p: &Program, statics: impl Iterator<Item = usize>) -> (HashSet<CTy>, HashSet<CTy>) {
    let (mut by_value, mut held, mut pointed, mut fns) = (Vec::new(), HashSet::new(), HashSet::new(), Vec::new());
    for i in statics {
        let st = &p.statics[i];
        let t = cty(&p.tys, st.ty);
        by_value_deps(&t, &mut by_value);
        collect_types(&t, &mut pointed);
        collect_promoted(p, &st.value, &t, &mut held);
        const_fns(&st.value, &mut fns);
        // A thread_local's native cell is defined in its part, by value.
        if let Some(cell) = super::native_tls_cell(p, i) {
            by_value_deps(&cell, &mut by_value);
        }
    }
    held.extend(by_value);
    for f in fns {
        let info = p.fn_info(LocalDefId(f));
        for &t in info.params.iter().chain([&info.ret]) {
            collect_types(&cty(&p.tys, t), &mut held);
        }
    }
    (held, pointed)
}

/// What B1 reads of the release statics (`record::Read::Statics`): what `statics_outs` makes
/// each static's C from, in its order. A static's symbol and C type, its `thread_local!` native
/// cell, and the value the pass emits (a key's slot word as the pass numbers it, not the value
/// collect gave it). A value names a str by its bytes, a static by its symbol (and path), a fn
/// pointer by its trampoline and the prototype it calls, never by an index a merge or a rebuilt
/// session moves. The layouts are the pass's Type reads. Hashed in ranges of statics on all cores.
pub(crate) fn statics_content_fp(p: &Program, slots: &[u32]) -> (u64, u64) {
    use crate::ty::consteval::ConstValue as CV;
    fn value(p: &Program, v: &CV, slots: &[u32], out: &mut Vec<u8>) {
        let len = |out: &mut Vec<u8>, n: usize| out.extend_from_slice(&(n as u64).to_le_bytes());
        match v {
            CV::Int(i) => {
                out.push(1);
                out.extend_from_slice(&i.to_le_bytes());
            }
            CV::Float(bits, ft) => {
                out.push(2);
                out.extend_from_slice(&bits.to_le_bytes());
                out.extend_from_slice(format!("{ft:?}").as_bytes());
            }
            CV::Bool(b) => out.extend_from_slice(&[3, *b as u8]),
            CV::Char(c) => {
                out.push(4);
                out.extend_from_slice(&(*c as u32).to_le_bytes());
            }
            CV::Str(i) => {
                let s = p.ast.strings[*i as usize].as_bytes();
                out.push(5);
                len(out, s.len());
                out.extend_from_slice(s);
            }
            CV::StrBytes(b) | CV::Bytes(b) => {
                out.push(if matches!(v, CV::StrBytes(_)) { 6 } else { 7 });
                len(out, b.as_slice().len());
                out.extend_from_slice(b.as_slice());
            }
            CV::Unit => out.push(8),
            CV::Aggregate(vs) => {
                out.push(9);
                len(out, vs.len());
                vs.iter().for_each(|x| value(p, x, slots, out));
            }
            CV::Variant(k, vs) => {
                out.push(10);
                out.extend_from_slice(&k.to_le_bytes());
                len(out, vs.len());
                vs.iter().for_each(|x| value(p, x, slots, out));
            }
            CV::Repeat(x, n) => {
                out.push(11);
                out.extend_from_slice(&n.to_le_bytes());
                value(p, x, slots, out);
            }
            CV::Ref(x) => {
                out.push(12);
                value(p, x, slots, out);
            }
            CV::StaticRef(i) => {
                out.push(13);
                out.extend_from_slice(static_sym(p, *i).as_bytes());
                out.push(0);
            }
            CV::StaticPlace(i, path) => {
                out.push(14);
                out.extend_from_slice(static_sym(p, *i).as_bytes());
                out.extend_from_slice(format!("{path:?}").as_bytes());
                out.push(0);
            }
            CV::FnPtr(f) => {
                out.push(15);
                if let Some(&slot) = slots.get(*f as usize) {
                    out.extend_from_slice(fn_sig(p, LocalDefId(*f), slot).as_bytes());
                    out.extend_from_slice(trampoline(p, LocalDefId(*f), slot).as_bytes());
                }
                out.push(0);
            }
        }
    }
    let order = super::statics_in_order(p);
    let tls_word: HashMap<usize, CV> =
        order.iter().filter(|&&i| p.statics[i].tls.is_some()).enumerate().map(|(n, &i)| (i, CV::Int(n as i128 + 1))).collect();
    let ranges: Vec<std::ops::Range<usize>> = (0..order.len()).step_by(64).map(|a| a..(a + 64).min(order.len())).collect();
    let (names, tag) = (current(), super::layout_phase());
    let hashes = crate::pool::par_map(&ranges, |r| {
        super::in_layout_phase(tag, || {
            with(names.as_ref(), || {
                let mut out = Vec::new();
                for &i in &order[r.clone()] {
                    let st = &p.statics[i];
                    out.extend_from_slice(static_sym(p, i as u32).as_bytes());
                    out.push(0);
                    out.extend_from_slice(mangle(&cty(&p.tys, st.ty)).as_bytes());
                    out.push(0);
                    match super::native_tls_cell(p, i) {
                        Some(cell) => {
                            out.push(1);
                            out.extend_from_slice(mangle(&cell).as_bytes());
                        }
                        None => {
                            out.push(0);
                            value(p, tls_word.get(&i).unwrap_or(&st.value), slots, &mut out);
                        }
                    }
                }
                crate::driver::cache::hash128(&[&out], 41)
            })
        })
    });
    let all: Vec<u8> = hashes.iter().flat_map(|(a, b)| a.to_le_bytes().into_iter().chain(b.to_le_bytes())).collect();
    crate::driver::cache::hash128(&[&(order.len() as u64).to_le_bytes(), &all], 42)
}

/// The B1 record of a statics pass (`statics_parts` with `rec`): one hash of the pieces of its
/// index and its parts, in order, and every read of the pass (the union of theirs, with
/// `Read::Statics`). None when a text of the pass came from no piece.
pub type StaticsRecord = Option<((u64, u64), Vec<record::Read>)>;

/// Release C statics in parts (`LUST_RELEASE_STATICS_KB`): the statics in emission order, cut
/// where a static's own bytes say (`cut_after` at odds bytes / `target`; a static of `target`
/// bytes or more alone), so a merge that changes one static recompiles its part only, and a
/// program's giant tables sit in parts of their own. One pass makes them all (`statics_outs`,
/// as `static_defs`), so each pointee, str array and trampoline has one definition, global, in
/// the part of the static whose value made it first, and equal content keeps one address
/// across parts as in one unit. A part declares each such name it uses (its own too: a static's
/// data can point into a later one's). Returns the index (unit 1), which registers every
/// pointee in the pass's order (`lust_kstatics_init`), the parts, and with `rec` the pass's B1
/// record (every byte of the index and the parts a piece).
pub fn statics_parts(p: &Program, g: &GlueSet, target: usize, rec: bool) -> (String, Vec<String>, StaticsRecord) {
    let (outs, cx) = statics_outs(p, &g.slots);
    let target = target.max(1);
    let mut cuts: Vec<Vec<usize>> = Vec::new();
    let mut cur = Vec::new();
    for (k, o) in outs.iter().enumerate() {
        let bytes = o.data.len() + o.made.len();
        if bytes >= target && !cur.is_empty() {
            cuts.push(std::mem::take(&mut cur));
        }
        cur.push(k);
        if cut_after(&o.sym, bytes, target as u64) {
            cuts.push(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() {
        cuts.push(cur);
    }
    // Each name the pass defined: its declaration, its place in the pass, and its static.
    let mut decl_of: HashMap<&str, (&str, usize, usize)> = HashMap::new();
    for (k, o) in outs.iter().enumerate() {
        for d in o.decls.clone() {
            let (name, decl, _) = &cx.decls[d];
            decl_of.insert(name, (decl, d, k));
        }
    }
    let by_sym: HashMap<&str, usize> = outs.iter().enumerate().map(|(k, o)| (o.sym.as_str(), k)).collect();
    // The names a part may use, in sets built once: the pass's names and the statics' symbols,
    // and the glue fns (by name, with their keys and prototypes).
    let wanted: crate::intern::FxSet<&str> = decl_of.keys().chain(by_sym.keys()).copied().collect();
    let mut glue: crate::intern::FxMap<&str, Vec<(&(Glue, CTy), &String)>> = crate::intern::FxMap::default();
    for (k, proto) in &g.protos {
        glue.entry(proto_name(proto)).or_default().push((k, proto));
    }
    let glue_names: crate::intern::FxSet<&str> = glue.keys().copied().collect();
    let names = CUR.with(|c| c.borrow().clone());
    let tag = super::layout_phase();
    let decls = std::sync::Arc::new(super::DeclCache::default());
    let parts = crate::pool::par_map(&cuts, |ks| {
        super::in_layout_phase(tag, || {
            with(names.as_ref(), || super::with_decl_cache(&decls, || {
                if rec {
                    record::open();
                }
                let body: String = ks.iter().map(|&k| outs[k].made.as_str()).chain(ks.iter().map(|&k| outs[k].data.as_str())).collect();
                // The names it uses, and the names the alias macros among them use.
                let mut used = names_found(&body, &wanted);
                let mut stack: Vec<&str> = used.iter().copied().collect();
                while let Some(n) = stack.pop() {
                    if let Some((d, _, _)) = decl_of.get(n).filter(|(d, _, _)| d.starts_with("#define")) {
                        stack.extend(names_found(d, &wanted).into_iter().filter(|m| used.insert(m)));
                    }
                }
                // The statics whose types it reads: its own, and those whose data or pointees it names.
                let mut statics: std::collections::BTreeSet<usize> = ks.iter().map(|&k| outs[k].idx).collect();
                for n in &used {
                    if let Some(&k) = by_sym.get(n) {
                        statics.insert(outs[k].idx);
                    }
                    if let Some(&(_, _, k)) = decl_of.get(n) {
                        statics.insert(outs[k].idx);
                    }
                }
                let (types, mut pointed) = statics_types(p, statics.iter().copied());
                // Only the glue the data names (a vtable's drop entry, say).
                let mut protos: Vec<&String> = Vec::new();
                for n in names_found(&body, &glue_names) {
                    for &(k, proto) in &glue[n] {
                        record::read(record::Read::Glue(k.0, k.1.clone()));
                        collect_types(&k.1, &mut pointed);
                        protos.push(proto);
                    }
                }
                protos.sort();
                pointed.retain(|t| !types.contains(t));
                let mut c = unit_header();
                record::piece(record::Kind::Fixed, 0, &c);
                // No blocks: an initializer names the fields of every type its value holds.
                type_decls_with(p, &mut c, &types, &pointed, Decls::ByValue { blocks: false }, &HashSet::new());
                for x in protos {
                    c.push_str(x);
                    record::piece(record::Kind::GlueProto, record::key(x), x);
                }
                let named: HashSet<usize> = used.iter().filter_map(|n| by_sym.get(n)).map(|&k| outs[k].idx).collect();
                let at = c.len();
                c.push_str(&static_decls_for(p, &named));
                record::piece(record::Kind::Statics, 0, &c[at..]);
                // The declarations, in the pass's order: externs and prototypes, then the macros.
                let mut decls: Vec<(usize, &str)> = used.iter().filter_map(|n| decl_of.get(n)).map(|&(d, at, _)| (at, d)).collect();
                decls.sort_unstable();
                let at = c.len();
                decls.iter().filter(|(_, d)| !d.starts_with("#define")).for_each(|(_, d)| c.push_str(d));
                decls.iter().filter(|(_, d)| d.starts_with("#define")).for_each(|(_, d)| c.push_str(d));
                record::piece(record::Kind::Externs, 0, &c[at..]);
                c.push_str(&body);
                record::piece(record::Kind::Data, 0, &body);
                let r = if rec { record::close(&c) } else { None };
                (c, r)
            }))
        })
    });
    let (parts, part_recs): (Vec<String>, Vec<_>) = parts.into_iter().unzip();
    // The index: every pointee, declared, then registered in the pass's order.
    if rec {
        record::open();
    }
    let mut index = unit_header();
    record::piece(record::Kind::Fixed, 0, &index);
    let regs: Vec<&str> = kconst::kstatics_regs(&cx).collect();
    let type_of: HashMap<&str, &CTy> = cx.decls.iter().filter_map(|(n, _, t)| Some((n.as_str(), t.as_ref()?))).collect();
    let mut named = HashSet::new();
    for r in &regs {
        if let Some(t) = type_of.get(r) {
            collect_types(t, &mut named);
        }
    }
    type_decls_with(p, &mut index, &HashSet::new(), &named, Decls::ByValue { blocks: false }, &HashSet::new());
    let at = index.len();
    for r in &regs {
        if let Some((d, _, _)) = decl_of.get(r) {
            index.push_str(d);
        }
    }
    record::piece(record::Kind::Externs, 0, &index[at..]);
    let at = index.len();
    index.push_str(&kconst::kstatics_init(&cx));
    record::piece(record::Kind::Register, 0, &index[at..]);
    // One record of the whole pass: its texts' pieces in order, and all their reads.
    let record = if rec { record::close(&index) } else { None }.and_then(|first| {
        let mut hashes = Vec::with_capacity(16 * (1 + part_recs.len()));
        let mut reads: HashSet<record::Read> = HashSet::new();
        for (h, rs) in std::iter::once(Some(first)).chain(part_recs).collect::<Option<Vec<_>>>()? {
            hashes.extend_from_slice(&h.0.to_le_bytes());
            hashes.extend_from_slice(&h.1.to_le_bytes());
            reads.extend(rs);
        }
        reads.insert(record::Read::Statics);
        Some((crate::driver::cache::hash128(&[&hashes], 18), reads.into_iter().collect()))
    });
    (index, parts, record)
}

/// The fn a glue prototype declares: the last name before its parameter list.
fn proto_name(proto: &str) -> &str {
    proto.split('(').next().and_then(|h| h.rsplit(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_')).next()).unwrap_or("")
}

/// The names among `wanted` that `text` holds as identifiers (runs of ASCII letters,
/// digits and `_`; the empty name when `text` has an empty run, as `str::split` gives).
/// The statics unit asks it for the glue names of 20k+ prototypes over its 15 MB of data
/// (tsgo): the text is scanned on all cores, in pieces cut at ASCII bytes outside names.
fn names_in<'a>(text: &str, wanted: impl Iterator<Item = &'a str>) -> HashSet<&'a str> {
    let wanted: crate::intern::FxSet<&str> = wanted.collect();
    let sep = |ch: char| !(ch.is_ascii_alphanumeric() || ch == '_');
    let mut found: HashSet<&str> = HashSet::new();
    if wanted.contains("") && text.split(sep).any(str::is_empty) {
        found.insert("");
    }
    let (bytes, step) = (text.as_bytes(), text.len().div_ceil(64).max(1 << 16));
    let mut cuts = vec![0];
    while let Some(&last) = cuts.last() {
        let mut at = (last + step).min(text.len());
        while at < text.len() && (bytes[at] >= 0x80 || !sep(bytes[at] as char)) {
            at += 1;
        }
        cuts.push(at);
        if at == text.len() {
            break;
        }
    }
    let pieces: Vec<&str> = cuts.windows(2).map(|w| &text[w[0]..w[1]]).collect();
    for part in crate::pool::par_map(&pieces, |piece| names_found(piece, &wanted)) {
        found.extend(part);
    }
    found
}

/// `names_in` on this thread, for a caller that is one of many jobs on the pool (a statics
/// part): a nested `par_map` on a busy pool spawns threads of its own.
fn names_found<'a>(text: &str, wanted: &crate::intern::FxSet<&'a str>) -> HashSet<&'a str> {
    text.split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_')).filter_map(|w| wanted.get(w).copied()).collect()
}

/// The fns whose pointers the constant `v` holds.
fn const_fns(v: &crate::ty::consteval::ConstValue, out: &mut Vec<u32>) {
    use crate::ty::consteval::ConstValue as CV;
    match v {
        CV::FnPtr(f) => out.push(*f),
        CV::Aggregate(vs) | CV::Variant(_, vs) => vs.iter().for_each(|x| const_fns(x, out)),
        CV::Repeat(x, _) | CV::Ref(x) => const_fns(x, out),
        _ => {}
    }
}

/// Whether a release C unit (or glue shard) ends after the fn (glue key) `id` of `size`
/// bytes: with odds size / `target`, so a unit holds about `target` bytes, decided by the
/// id and its own size only. A cut test that followed the program's mean size moved every
/// cut when glue or code anywhere moved the mean across a step.
pub fn cut_after(id: &str, size: usize, target: u64) -> bool {
    hash64(id) % target < size as u64
}

fn hash64(s: &str) -> u64 {
    let mut x = crate::intern::FxHasher::default();
    std::hash::Hash::hash(s, &mut x);
    std::hash::Hasher::finish(&x)
}

#[cfg(test)]
mod tests {
    use super::names_in;
    use std::collections::HashSet;

    /// `names_in` finds what the set of every identifier of the text finds, over a text of many
    /// pieces with UTF-8 and names at every offset, the empty name included.
    #[test]
    fn names_in_matches_the_split_of_the_whole_text() {
        let mut text = String::from(";;");
        for i in 0..40_000u32 {
            text.push_str(&format!("glue_{}(x){}", i % 997, if i % 7 == 0 { " é→ " } else { ", " }));
        }
        let wanted: Vec<String> = (0..1200).map(|i| format!("glue_{i}")).chain(["".to_string(), "x".into(), "é".into()]).collect();
        let all: HashSet<&str> = text.split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_')).collect();
        let want: HashSet<&str> = wanted.iter().map(String::as_str).filter(|w| all.contains(w)).collect();
        assert!(text.len() > 4 << 16 && want.contains("") && want.contains("glue_996") && !want.contains("glue_997"));
        assert_eq!(names_in(&text, wanted.iter().map(String::as_str)), want);
        assert_eq!(names_in("abc", ["", "abc"].into_iter()), HashSet::from(["abc"]));
    }
}
