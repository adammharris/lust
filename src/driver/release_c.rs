// Release C (`LUST_RELEASE_C=1`, `lust build`): C whose units depend only on their own
// fns, so a content-keyed object cache (key = a unit's C text plus the C compiler, its
// flags and the target) reuses every unit a commit did not touch, across commits,
// machines and CI runs. A one-shot build writes it, and so does a persistent session (a
// front image, src/image.rs) for the release driver: its units are a one-shot build's,
// byte for byte, as every name and unit follows from identities and content (the
// location unit numbers fns by id, `names::loc_unit`, and the glue shards hold what the
// live fns reach, `names::glue_shards`). Dev builds through tcc in a persistent session (the
// daemon) keep numbered names and byte groups (their overlays need the fn table).
//   names      cgen/names.rs: content-addressed fn, Adt and vtable names, direct calls,
//              panic locations through the location unit's slot table
//   partition  `groups`: a fn's unit follows from its own identity: its source file
//              (an instance: its generic fn's file), and inside a big file a
//              content-defined chunk: fns in source order, a cut after each fn whose id
//              hash hits 1 in (target bytes / mean fn bytes). Adding a fn moves no other
//              fn; a cut moves only when the fn that makes it goes.
use crate::cgen::{self, FnOut};
use crate::check::collect::{LocalDefId, Program};
use std::sync::Arc;

/// True when a build writes release C: `LUST_RELEASE_C` set, for a one-shot build or
/// a release driver build (`cc`) of a persistent session.
pub fn on(persistent: bool, cc: bool) -> bool {
    (!persistent || cc) && std::env::var_os("LUST_RELEASE_C").is_some_and(|v| !v.is_empty() && v != "0")
}

/// What decides a slot's C besides its program: release C or not, debug info, unwind
/// tables, and the switches of the release backends (every LUST_RELEASE_ variable, such as
/// LUST_RELEASE_UNREACHABLE) and of drop elaboration (`LUST_DROPFLAGS`). A persistent session
/// makes every slot's C again when it moves.
pub fn codegen_key(release: bool, debug: bool, unwind_tables: bool) -> u64 {
    let mut vars: Vec<(String, String)> = std::env::vars()
        .filter(|(k, _)| k.starts_with("LUST_RELEASE_") || k.starts_with("LUST_LL_") || k == "LUST_DROPFLAGS")
        .collect();
    vars.sort();
    let mut x = crate::intern::FxHasher::default();
    std::hash::Hash::hash(&(release, debug, unwind_tables, vars), &mut x);
    std::hash::Hasher::finish(&x)
}

fn hash64(s: &str) -> u64 {
    let mut x = crate::intern::FxHasher::default();
    std::hash::Hash::hash(s, &mut x);
    std::hash::Hasher::finish(&x)
}

/// The stable names of `program`'s release C: each slot's fn by a hash of its
/// `DiskDefId`, each Adt by its def hash (`d`) or instance key hash (`i`).
pub fn names(program: &Program, fn_slot: &[u32], n_slots: usize, inst_adts: &[(u32, u64)]) -> Arc<cgen::names::Names> {
    // The names are made on the pool (7 ms on one thread for tsgo's 78k fns).
    let fn_ids: Vec<u32> = (0..fn_slot.len().min(program.fns.len()) as u32).collect();
    let made = crate::pool::par_map(&fn_ids, |&i| {
        let d = program.disk_id(LocalDefId(i));
        format!("{:016x}", hash64(&format!("{:016x}{:016x}", d.krate.0, d.hash.0)))
    });
    let mut fns = vec![None; n_slots];
    for (i, name) in made.into_iter().enumerate() {
        if let Some(x) = fns.get_mut(fn_slot[i] as usize) {
            *x = Some(name);
        }
    }
    let inst: crate::intern::FxMap<u32, u64> = inst_adts.iter().copied().collect();
    let adt_ids: Vec<u32> = (0..program.adts.len() as u32).collect();
    let adts = crate::pool::par_map(&adt_ids, |&a| match (inst.get(&a), program.defs.def_of_adt(crate::ty::AdtId(a))) {
        (Some(k), _) => format!("i{k:016x}"),
        (None, Some(d)) => format!("d{:016x}", d.hash.0),
        (None, None) => format!("x{a}"),
    });
    Arc::new(cgen::names::Names { fns, adts, by_id: Default::default() })
}

/// The release fn units: (registration fn name, slots in unit order), in a stable
/// order. `file` and `line` give each slot's source file and line (an instance: its
/// generic fn's). Chunks aim at `unit_bytes` of fn code.
/// The target size of a release C unit in bytes of fn or glue code (`LUST_RELEASE_UNIT_KB`,
/// default 128).
pub fn unit_bytes() -> usize {
    std::env::var("LUST_RELEASE_UNIT_KB").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(128) * 1024
}

/// The target size of a release C glue shard in bytes of glue definitions
/// (`LUST_RELEASE_SHARD_KB`, default 16). A shard declares the types its glue reads, so a merge
/// that changes a central type recompiles the shards whose keys hold it, and the slowest one
/// bounds the cc step of a small merge. tsgo's replay in CI's shape, three runs against 64 KB:
/// median lust -20% / -10% / -11%, the small merges' -14% / -11% / -13% (their tail about
/// halved), compile CPU +3% / -4% / -5%; m9, the biggest merge, +18% / +4% / -1% (about twice
/// as many shards miss). 24 KB: median -14% / -9.5%; 32 KB: -16%.
pub fn shard_bytes() -> usize {
    std::env::var("LUST_RELEASE_SHARD_KB").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(16) * 1024
}

/// Whether release C's target (`triple`, the host's when empty) makes ELF objects: not
/// Apple's Mach-O, Windows' COFF or wasm. The location unit's symbol aliases are ELF
/// assembler (`cgen::names::loc_unit`).
pub fn elf_target(triple: &str) -> bool {
    let t = if triple.is_empty() { crate::protocol::host_triple() } else { triple };
    !["apple", "darwin", "windows", "wasm", "uefi"].iter().any(|os| t.contains(os))
}

pub fn groups(out: &[FnOut], names: &cgen::names::Names, file: &[String], line: &[u32]) -> Vec<(String, Vec<usize>)> {
    group_fns(out, names, file, line, unit_bytes(), unit_cap())
}

/// `groups` for a unit target and cap (`unit_bytes`, `unit_cap`) of `target` and `cap` bytes.
fn group_fns(out: &[FnOut], names: &cgen::names::Names, file: &[String], line: &[u32], target: usize, cap: usize) -> Vec<(String, Vec<usize>)> {
    let live: Vec<usize> = (0..out.len()).filter(|&s| out[s].has_code()).collect();
    // A fn's size: its C; with the LLVM backend its statement count (`FnOut::ll_cost`) at
    // 200 bytes each, which no lowering, fact or ABI choice moves, so every such variant
    // gets the same units (and about as many as C).
    let llvm = live.iter().any(|&s| !out[s].ll.is_empty());
    // A C fn's named constants count too: their definitions travel in its externs (cgen's
    // kdata), where its literals were part of its code before.
    let kdata = |s: usize| out[s].externs.iter().filter(|e| e.starts_with('#')).map(|e| e.len()).sum::<usize>();
    let size = |s: usize| if llvm { out[s].ll_cost as usize * 200 } else { out[s].code_len() + kdata(s) };
    let target = target.max(1) as u64;
    let id = |s: usize| names.fns.get(s).and_then(|x| x.clone()).unwrap_or_else(|| format!("dead{s}"));
    let mut by_file: std::collections::BTreeMap<&str, Vec<(u32, String, usize)>> = Default::default();
    for &s in &live {
        by_file.entry(file.get(s).map_or("", String::as_str)).or_default().push((line.get(s).copied().unwrap_or(0), id(s), s));
    }
    let mut groups: Vec<Vec<(String, usize)>> = Vec::new();
    for (_, mut fns) in by_file {
        // Source order: an edit in one region of a file touches few chunks.
        fns.sort();
        let mut cur: Vec<(String, usize)> = Vec::new();
        for (_, n, s) in fns {
            let cut = cgen::names::cut_after(&n, size(s), target);
            cur.push((n, s));
            if cut {
                groups.push(std::mem::take(&mut cur));
            }
        }
        if !cur.is_empty() {
            groups.push(cur);
        }
    }
    if cap > 0 {
        groups = groups.into_iter().flat_map(|g| split_over(g, cap as u64, target / 2, &size)).collect();
    }
    groups
        .into_iter()
        .map(|g| {
            let ids: Vec<&str> = g.iter().map(|(n, _)| n.as_str()).collect();
            (format!("lust_register_g{:016x}", hash64(&ids.join(","))), g.into_iter().map(|(_, s)| s).collect())
        })
        .collect()
}

/// The target size of a part of the release C statics in bytes of their C (`LUST_RELEASE_STATICS_KB`,
/// default 128; 0: one statics unit), `cgen::names::statics_parts`. tsgo's statics were one
/// 15.6 MB unit (2-4 s under load) that 7 of 12 merges of its replay recompiled for a few
/// changed statics; 128 KB beat 256 KB and one unit there.
pub fn statics_bytes() -> usize {
    std::env::var("LUST_RELEASE_STATICS_KB").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(128) * 1024
}

/// The cap on a release C fn unit's fn code (`LUST_RELEASE_UNIT_CAP_KB`, default 256; 0: none).
/// The cuts at odds bytes / target leave a long tail of large units (tsgo: units of 1.3-1.9 MB of
/// C at 3-4 s under load, the slowest compile of many small merges); 256 KB beat 512 and 128 KB
/// on its replay.
pub fn unit_cap() -> usize {
    std::env::var("LUST_RELEASE_UNIT_CAP_KB").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(256) * 1024
}

/// A unit `g` over `cap` bytes of fn code, cut after each fn whose cut test meets `odds` (the
/// unit target's halved: every cut the unit had meets them too), and each part still over the
/// cap again at half those odds. The cuts follow from each fn's own id and size, so a unit
/// splits the same way while it stays over the cap, and no other unit moves.
fn split_over(g: Vec<(String, usize)>, cap: u64, odds: u64, size: &impl Fn(usize) -> usize) -> Vec<Vec<(String, usize)>> {
    if g.len() < 2 || odds == 0 || g.iter().map(|(_, s)| size(*s) as u64).sum::<u64>() <= cap {
        return vec![g];
    }
    let mut parts: Vec<Vec<(String, usize)>> = Vec::new();
    let mut cur = Vec::new();
    for (n, s) in g {
        let cut = cgen::names::cut_after(&n, size(s), odds);
        cur.push((n, s));
        if cut {
            parts.push(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() {
        parts.push(cur);
    }
    parts.into_iter().flat_map(|p| split_over(p, cap, odds / 2, size)).collect()
}

/// The table unit of release C: the fn tables stay declared (the runtime header names
/// them) but hold nothing, and `lust_base_init` runs the `registers` it gets: main's unit's
/// only, the one registration that sets anything. A call to each unit's empty one touched
/// a page of code per unit at every process start.
pub fn table_unit(registers: &[String]) -> String {
    let mut c = cgen::unit_header();
    c.push_str("lust_fnptr lust_fns[1];\nlust_fnptr lust_tramps[1];\nint (*lust_main_entry_p)(void);\n");
    let mut regs: Vec<&String> = registers.iter().collect();
    regs.sort();
    for r in &regs {
        c.push_str(&format!("void {r}(void);\n"));
    }
    c.push_str("void lust_base_init(void) {\n");
    for r in &regs {
        c.push_str(&format!("  {r}();\n"));
    }
    c.push_str("}\n");
    c
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `n` fns in one file, slot `s` on line `10 * s` with `size` bytes of code each.
    fn program(n: usize, size: usize) -> (Vec<FnOut>, cgen::names::Names, Vec<String>, Vec<u32>) {
        let out = (0..n).map(|_| FnOut { text: cgen::CText::Plain("x".repeat(size)), ..Default::default() }).collect();
        let names = cgen::names::Names {
            fns: (0..n).map(|s| Some(format!("{:016x}", hash64(&format!("fn{s}"))))).collect(),
            adts: Vec::new(),
            by_id: Default::default(),
        };
        (out, names, vec!["src/a.rs".to_string(); n], (0..n as u32).map(|s| 10 * s).collect())
    }

    /// The units as sets of fn ids, so two programs with other slot numbers compare: the cuts at
    /// a 128 KB target, without a cap (`a_unit_over_the_cap_splits_where_its_fns_say` has one).
    fn unit_ids(out: &[FnOut], names: &cgen::names::Names, file: &[String], line: &[u32]) -> Vec<Vec<String>> {
        group_fns(out, names, file, line, 128 * 1024, 0).into_iter().map(|(_, g)| g.into_iter().map(|s| names.fns[s].clone().unwrap()).collect()).collect()
    }

    /// A fn's unit follows from its own identity, size and source order: inserting a fn
    /// (here 12x the others' size) in the middle of a file changes only the unit it joins,
    /// and every other unit keeps its fns (and so its registration name).
    #[test]
    fn inserting_a_fn_moves_no_other_unit() {
        let (out, names, file, line) = program(400, 4096);
        let before = unit_ids(&out, &names, &file, &line);
        assert!(before.len() > 4, "a 1.6 MB file splits into several units: {}", before.len());
        // A new fn (slot 400) on line 1995, between slots 199 and 200.
        let (mut out2, mut names2, mut file2, mut line2) = (out, names, file, line);
        out2.push(FnOut { text: cgen::CText::Plain("y".repeat(50_000)), ..Default::default() });
        names2.fns.push(Some(format!("{:016x}", hash64("new fn"))));
        file2.push("src/a.rs".to_string());
        line2.push(1995);
        let after = unit_ids(&out2, &names2, &file2, &line2);
        let lost = before.iter().filter(|u| !after.contains(u)).count();
        let new = after.iter().filter(|u| !before.contains(u)).count();
        assert_eq!(lost, 1, "only the unit the fn joins changes");
        assert!(new <= 2, "it comes back as one unit, or two when the new fn makes a cut: {new}");
    }

    /// A fn's named constants count in its cut size as its code does (cgen's kdata moves its
    /// literals from its code into guarded definitions among its externs), so moving bytes
    /// from the one to the other moves no cut.
    #[test]
    fn named_data_counts_in_the_cut_size() {
        let (out, names, file, line) = program(400, 4096);
        let before = unit_ids(&out, &names, &file, &line);
        let def: std::sync::Arc<str> = format!("#{}", "d".repeat(999)).into();
        let moved: Vec<FnOut> = (0..400)
            .map(|_| FnOut {
                text: cgen::CText::Plain("x".repeat(3096)),
                externs: [def.clone()].into_iter().collect(),
                ..Default::default()
            })
            .collect();
        assert_eq!(unit_ids(&moved, &names, &file, &line), before);
    }

    /// With a cap, a unit over it splits at cuts that follow from its fns' own ids and sizes:
    /// no part is over the cap unless it is one fn, every unit without the cap ends where a
    /// part ends, and growing one fn changes only the parts of the unit that holds it.
    #[test]
    fn a_unit_over_the_cap_splits_where_its_fns_say() {
        let (out, names, file, line) = program(1200, 2048);
        let ids = |out: &[FnOut], cap: usize| -> Vec<Vec<String>> {
            group_fns(out, &names, &file, &line, 128 * 1024, cap).into_iter().map(|(_, g)| g.into_iter().map(|s| names.fns[s].clone().unwrap()).collect()).collect()
        };
        let cap = 160 * 1024;
        let (whole, parts) = (ids(&out, 0), ids(&out, cap));
        assert!(whole.iter().any(|u| u.len() * 2048 > cap), "the program has a unit over the cap");
        assert!(parts.len() > whole.len());
        assert!(parts.iter().all(|u| u.len() == 1 || u.len() * 2048 <= cap), "no part over the cap");
        let ends = |us: &[Vec<String>]| us.iter().map(|u| u.last().unwrap().clone()).collect::<std::collections::HashSet<_>>();
        assert!(ends(&whole).is_subset(&ends(&parts)), "the cuts without the cap stay cuts");
        // Grow a fn of the largest unit: only that unit's parts may change.
        let big = whole.iter().max_by_key(|u| u.len()).unwrap();
        let slot = (0..out.len()).find(|&s| names.fns[s].as_deref() == Some(big[big.len() / 2].as_str())).unwrap();
        let mut out2 = program(1200, 2048).0;
        out2[slot].text = cgen::CText::Plain(out2[slot].code_text().into_owned() + &"z".repeat(3000));
        let after = ids(&out2, cap);
        let moved: Vec<&Vec<String>> = after.iter().filter(|u| !parts.contains(u)).collect();
        assert!(moved.iter().all(|u| u.iter().all(|f| big.contains(f))), "only the grown unit's parts move");
    }
}
