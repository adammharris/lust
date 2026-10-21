// Speculative checks (materialize's template and discovery checks,
// check/generics.rs `Ahead`).
//
// Materialize checks the items of a round in order, and each turn's apply
// step adds instances, closures, glue rows and types that a later item's
// check can read. A window of items checks ahead in parallel against the
// program as it is at the turn the window opens. Each window check logs
// what it reads from the tables that materialize changes (`read`,
// `read_all`), and the main thread logs each write to them with a stamp
// (`wrote`, `wrote_all`, `new_stamp`: a new one each turn, and one after
// materialize's early type interning). A window result stands at its
// item's turn only when no key it read was written at or after the stamp
// it read (`stale_since`); else the item checks again in its turn. A result that
// stands read the same values the in-order check reads, so it is the same
// result.
//
// The logged tables are `Logged` maps (no `Deref`: each read and write
// goes through a method that logs it), the global type store's arenas and
// maps (ty/mod.rs), `Defs`, and `GenTables::anon_wants`, which a check also
// writes: a window check writes it into its own overlay (`note_anon`),
// which `Ahead::take` replays in turn order. Keys are 64-bit hashes; a
// collision only makes an item check again.

use crate::intern::FxMap;
use std::cell::{Cell, RefCell};
use std::hash::{BuildHasherDefault, Hash, Hasher};

/// The logged tables (one bit each in a `Log`'s table masks).
pub mod tab {
    // The global type store (ty/mod.rs).
    pub const KINDS: u8 = 0;
    pub const ARGS: u8 = 1;
    pub const TYS_LIST: u8 = 2;
    pub const CONSTS: u8 = 3;
    pub const SIGS: u8 = 4;
    pub const BOUNDS: u8 = 5;
    pub const BINDINGS: u8 = 6;
    pub const TY_ADT1: u8 = 7;
    pub const TY_ADT_LOCALS: u8 = 8;
    pub const TY_ADT_DEFS: u8 = 9;
    pub const TY_ADT_INSTANCES: u8 = 10;
    pub const TY_ADT_C_KEYS: u8 = 11;
    pub const TY_ADT_C_CANON: u8 = 12;
    pub const TY_ADT_FULL: u8 = 13;
    pub const TY_UNSIZED: u8 = 14;
    pub const TY_UNSIZED_INSTS: u8 = 15;
    // `Defs` (ty/defs.rs) and `Program` (check/collect.rs).
    pub const DEFS: u8 = 16;
    pub const DEF_ADT_LOCALS: u8 = 17;
    pub const DEF_ADT_DEFS: u8 = 18;
    /// The length of `Program::adts` (a scan of every Adt row).
    pub const ADTS: u8 = 19;
    pub const METHODS: u8 = 20;
    pub const DEF_BY_HASH: u8 = 21;
    pub const ANON_WANTS: u8 = 22;
    // `GenTables` (check/generics.rs).
    pub const INSTANCES: u8 = 23;
    pub const INSTANCE_BY_KEY: u8 = 24;
    pub const CLOSURES: u8 = 25;
    pub const CLOSURE_FNS: u8 = 26;
    pub const TEMPLATE_CLOSURES: u8 = 27;
    pub const TEMPLATE_CALLS: u8 = 28;
    pub const DROP_METHODS: u8 = 29;
    pub const GLUE_METHODS: u8 = 30;
    pub const CLONE_FROM_METHODS: u8 = 31;
    pub const PCMP_METHODS: u8 = 32;
    pub const REF_DEFAULT_METHODS: u8 = 33;
    pub const FMT_METHODS: u8 = 34;
    pub const HASHER_METHODS: u8 = 35;
    pub const BUILD_HASHERS: u8 = 36;
    pub const ITER_METHODS: u8 = 37;
    pub const WRITTEN_HASH: u8 = 38;
    pub const HASH_IMPLS: u8 = 39;
    pub const DYN_KEYS: u8 = 40;
    pub const GENERIC_HASH: u8 = 41;
    pub const BORROW_IMPLS: u8 = 42;
    pub const TRAIT_PICKS: u8 = 43;
    pub const VTABLE_BY_KEY: u8 = 44;
    pub const OPAQUE_RET_OF: u8 = 45;
    pub const OPAQUE_HIDDEN: u8 = 46;
    pub const TEMPLATE_CHECKS: u8 = 47;
    pub const WRITTEN_PROJECTIONS: u8 = 48;
    pub const FMT_WRITE_METHODS: u8 = 49;
    /// No table: an arena of a body overlay (`ty::Tys`).
    pub const NONE: u8 = u8::MAX;
}

const OFF: u8 = 0;
const READ: u8 = 1;
const WRITE: u8 = 2;

thread_local! {
    /// What this thread logs: nothing, its reads (a window check), or its
    /// writes (the main thread while a window is open).
    static MODE: Cell<u8> = const { Cell::new(OFF) };
    static LOG: RefCell<Log> = RefCell::new(Log::default());
    /// The main thread's writes since its round began (`begin_round`).
    static WRITES: RefCell<Writes> = RefCell::new(Writes::default());
    /// The `anon_wants` notes of this thread's window check, in order.
    static ANON: RefCell<Vec<(u32, Option<crate::check::generics::ConstScalar>)>> = const { RefCell::new(Vec::new()) };
    /// Steps left before this thread's window check gives up (`step`).
    static FUEL: Cell<u64> = const { Cell::new(u64::MAX) };
}

/// What one window check read: key hashes, the tables those keys are
/// in, and whole-table reads (an iteration, a length).
#[derive(Default, Debug)]
pub struct Log {
    keys: std::collections::HashSet<u64, BuildHasherDefault<NoHash>>,
    key_tabs: u64,
    all: u64,
}

/// A hasher for keys that are hashes already: one multiply spreads the
/// table byte (`hash_key`) over the bits the set probes with.
#[derive(Default)]
pub struct NoHash(u64);

impl Hasher for NoHash {
    fn finish(&self) -> u64 {
        self.0.wrapping_mul(0x9E37_79B9_7F4A_7C15)
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = self.0.rotate_left(8) ^ b as u64;
        }
    }
    fn write_u64(&mut self, n: u64) {
        self.0 = n;
    }
}

impl Log {
    /// The table of one read that a write at stamp `since` or later made
    /// stale, if any: None when the check made at the start of stamp
    /// `since` still holds now.
    pub fn stale_since(&self, w: &Writes, since: u32) -> Option<u8> {
        let after = |stamp: u32| stamp >= since;
        for t in 0..64u8 {
            let bit = 1u64 << t;
            let (whole, keyed) = (w.all[t as usize], w.key_tabs[t as usize]);
            if self.all & bit != 0 && (after(whole) || after(keyed)) || self.key_tabs & bit != 0 && after(whole) {
                return Some(t);
            }
        }
        self.keys.iter().find(|k| w.keys.get(k).is_some_and(|&turn| after(turn))).map(|k| (k >> 56) as u8)
    }

    fn key(&mut self, t: u8, k: u64) {
        self.keys.insert(k);
        self.key_tabs |= 1 << t;
    }
}

/// What the main thread wrote to logged tables since its round began:
/// per key, per table, and per whole table, the stamp of its last write
/// (0 is never).
pub struct Writes {
    keys: std::collections::HashMap<u64, u32, BuildHasherDefault<NoHash>>,
    key_tabs: [u32; 64],
    all: [u32; 64],
    /// The stamp of the writes made now (`new_stamp`).
    stamp: u32,
}

impl Default for Writes {
    fn default() -> Writes {
        Writes { keys: Default::default(), key_tabs: [0; 64], all: [0; 64], stamp: 1 }
    }
}

/// A key's hash, with its table in the top byte (`Log::stale_by`).
#[inline]
fn hash_key<K: Hash + ?Sized>(t: u8, k: &K) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    k.hash(&mut h);
    (h.finish() >> 8) | (t as u64) << 56
}

#[inline]
fn mode() -> u8 {
    MODE.with(Cell::get)
}

/// Notes a read of key `k` of table `t` (a window check).
#[inline]
pub fn read<K: Hash + ?Sized>(t: u8, k: &K) {
    if mode() == READ {
        let h = hash_key(t, k);
        LOG.with(|l| l.borrow_mut().key(t, h));
    }
}

/// Notes a read of all of table `t`: an iteration or a length.
#[inline]
pub fn read_all(t: u8) {
    if mode() == READ {
        LOG.with(|l| l.borrow_mut().all |= 1 << t);
    }
}

/// Notes a write of key `k` of table `t` (the main thread in a round).
#[inline]
pub fn wrote<K: Hash + ?Sized>(t: u8, k: &K) {
    if mode() == WRITE {
        let h = hash_key(t, k);
        WRITES.with(|w| {
            let mut w = w.borrow_mut();
            let stamp = w.stamp;
            w.keys.insert(h, stamp);
            w.key_tabs[t as usize] = stamp;
        });
    }
}

/// Notes a write that may touch any key of table `t`.
#[inline]
pub fn wrote_all(t: u8) {
    if mode() == WRITE {
        WRITES.with(|w| {
            let mut w = w.borrow_mut();
            w.all[t as usize] = w.stamp;
        });
    }
}

/// True on a thread running a window check.
#[inline]
pub fn reading() -> bool {
    mode() == READ
}

/// Begins a round on the main thread: from now on its writes to logged
/// tables are logged (`Writes`), each with the stamp of its time
/// (`new_stamp`), until `end_round`.
pub fn begin_round() {
    MODE.with(|m| m.set(WRITE));
    WRITES.with(|w| *w.borrow_mut() = Writes::default());
}

pub fn end_round() {
    MODE.with(|m| m.set(OFF));
    WRITES.with(|w| *w.borrow_mut() = Writes::default());
}

/// A new stamp for the main thread's writes from now on; a check made
/// now reads the program as of this stamp.
pub fn new_stamp() -> u32 {
    WRITES.with(|w| {
        let mut w = w.borrow_mut();
        w.stamp += 1;
        w.stamp
    })
}

/// The table of one read of `reads` that a write at stamp `since` or
/// later made stale (`Log::stale_since`).
pub fn stale_since(reads: &Log, since: u32) -> Option<u8> {
    WRITES.with(|w| reads.stale_since(&w.borrow(), since))
}

/// Why a window check stopped early (`step`); not a panic, so no hook
/// prints it.
pub struct OutOfFuel;

/// One window check of `f`: its result, its read log, its `anon_wants`
/// notes and the steps it took; None when it panicked or ran out of
/// `fuel` steps (the body then checks in its turn, which repeats a real
/// panic there). A cancel of a background compile goes on unwinding.
#[allow(clippy::type_complexity)]
pub fn speculate<R>(fuel: u64, f: impl FnOnce() -> R) -> Option<(R, Log, Vec<(u32, Option<crate::check::generics::ConstScalar>)>, u64)> {
    let prev = MODE.with(|m| m.replace(READ));
    let saved = LOG.with(|l| std::mem::take(&mut *l.borrow_mut()));
    FUEL.with(|c| c.set(fuel));
    QUIET.with(|q| q.set(true));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    QUIET.with(|q| q.set(false));
    let left = FUEL.with(|c| c.replace(u64::MAX));
    let log = LOG.with(|l| std::mem::replace(&mut *l.borrow_mut(), saved));
    let anon = ANON.with(|a| std::mem::take(&mut *a.borrow_mut()));
    MODE.with(|m| m.set(prev));
    match r {
        Ok(r) => Some((r, log, anon, fuel - left)),
        // A cancelled background compile (`pool::Cancelled`) stops here
        // too, not only in the item's turn.
        Err(payload) if payload.is::<crate::pool::Cancelled>() => std::panic::resume_unwind(payload),
        Err(_) => None,
    }
}

/// Counts `n` steps of a window check; one past its fuel stops it. Called
/// from the solver loops that can run long on a program state the
/// in-order check never sees.
#[inline]
pub fn step(n: u64) {
    if mode() != READ {
        return;
    }
    let left = FUEL.with(|c| {
        let v = c.get().saturating_sub(n);
        c.set(v);
        v
    });
    if left == 0 {
        std::panic::resume_unwind(Box::new(OutOfFuel));
    }
}

thread_local! {
    /// Set while a window check runs: its panics are caught and the body
    /// checks again in its turn, so the panic hook stays quiet.
    static QUIET: Cell<bool> = const { Cell::new(false) };
}

/// Installs (once) a panic hook that is quiet on a thread running a window
/// check and the previous hook everywhere else.
pub fn quiet_hook() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !QUIET.with(Cell::get) {
                prev(info);
            }
        }));
    });
}

/// `GenTables::anon_wants` note of a window check: kept in its overlay.
/// False on any other thread (the caller writes the shared table).
pub fn note_anon(e: u32, want: Option<crate::check::generics::ConstScalar>) -> bool {
    if mode() != READ {
        return false;
    }
    ANON.with(|a| a.borrow_mut().push((e, want)));
    true
}

/// The `anon_wants` entry of `e` as this thread sees it: on a window
/// check, its own last note with a type (logging the read), else `shared`.
pub fn anon_want(e: u32, shared: impl FnOnce() -> Option<crate::check::generics::ConstScalar>) -> Option<crate::check::generics::ConstScalar> {
    if mode() == READ {
        read(tab::ANON_WANTS, &e);
        let own = ANON.with(|a| a.borrow().iter().rev().find(|(k, w)| *k == e && w.is_some()).and_then(|(_, w)| *w));
        if own.is_some() {
            return own;
        }
    }
    shared()
}

/// A map whose reads and writes are logged for window checks (see the
/// module docs). `T` is its table (`tab`). It has the
/// map methods its users call; each logs.
#[derive(Clone, Debug)]
pub struct Logged<K, V, const T: u8> {
    map: FxMap<K, V>,
}

impl<K, V, const T: u8> Default for Logged<K, V, T> {
    fn default() -> Self {
        Logged { map: FxMap::default() }
    }
}

impl<K: Hash + Eq, V, const T: u8> Logged<K, V, T> {
    #[inline]
    pub fn get<Q: Hash + Eq + ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: std::borrow::Borrow<Q>,
    {
        read(T, k);
        self.map.get(k)
    }
    #[inline]
    pub fn contains_key<Q: Hash + Eq + ?Sized>(&self, k: &Q) -> bool
    where
        K: std::borrow::Borrow<Q>,
    {
        read(T, k);
        self.map.contains_key(k)
    }
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        wrote(T, &k);
        self.map.insert(k, v)
    }
    pub fn get_mut<Q: Hash + Eq + ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: std::borrow::Borrow<Q>,
    {
        wrote(T, k);
        self.map.get_mut(k)
    }
    pub fn remove<Q: Hash + Eq + ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        K: std::borrow::Borrow<Q>,
    {
        wrote(T, k);
        self.map.remove(k)
    }
    pub fn entry(&mut self, k: K) -> std::collections::hash_map::Entry<'_, K, V> {
        wrote(T, &k);
        self.map.entry(k)
    }
    pub fn len(&self) -> usize {
        read_all(T);
        self.map.len()
    }
    pub fn is_empty(&self) -> bool {
        read_all(T);
        self.map.is_empty()
    }
    pub fn iter(&self) -> std::collections::hash_map::Iter<'_, K, V> {
        read_all(T);
        self.map.iter()
    }
    pub fn keys(&self) -> std::collections::hash_map::Keys<'_, K, V> {
        read_all(T);
        self.map.keys()
    }
    pub fn values(&self) -> std::collections::hash_map::Values<'_, K, V> {
        read_all(T);
        self.map.values()
    }
    pub fn iter_mut(&mut self) -> std::collections::hash_map::IterMut<'_, K, V> {
        wrote_all(T);
        self.map.iter_mut()
    }
    pub fn values_mut(&mut self) -> std::collections::hash_map::ValuesMut<'_, K, V> {
        wrote_all(T);
        self.map.values_mut()
    }
    pub fn retain(&mut self, f: impl FnMut(&K, &mut V) -> bool) {
        wrote_all(T);
        self.map.retain(f)
    }
    pub fn clear(&mut self) {
        wrote_all(T);
        self.map.clear()
    }
    pub fn drain(&mut self) -> std::collections::hash_map::Drain<'_, K, V> {
        wrote_all(T);
        self.map.drain()
    }
    pub fn reserve(&mut self, n: usize) {
        self.map.reserve(n)
    }
    /// The whole map, read as a whole.
    pub fn as_map(&self) -> &FxMap<K, V> {
        read_all(T);
        &self.map
    }
}

impl<K: Hash + Eq, V, const T: u8> Extend<(K, V)> for Logged<K, V, T> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, it: I) {
        wrote_all(T);
        self.map.extend(it)
    }
}

impl<K, V, const T: u8> From<FxMap<K, V>> for Logged<K, V, T> {
    fn from(map: FxMap<K, V>) -> Self {
        Logged { map }
    }
}

impl<K: Hash + Eq, V, const T: u8> FromIterator<(K, V)> for Logged<K, V, T> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(it: I) -> Self {
        Logged { map: it.into_iter().collect() }
    }
}

impl<'a, K: Hash + Eq, V, const T: u8> IntoIterator for &'a Logged<K, V, T> {
    type Item = (&'a K, &'a V);
    type IntoIter = std::collections::hash_map::Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<K: Hash + Eq, V: PartialEq, const T: u8> PartialEq for Logged<K, V, T> {
    fn eq(&self, other: &Self) -> bool {
        self.map == other.map
    }
}

impl<K: Hash + Eq + std::borrow::Borrow<Q>, Q: Hash + Eq + ?Sized, V, const T: u8> std::ops::Index<&Q> for Logged<K, V, T> {
    type Output = V;
    fn index(&self, k: &Q) -> &V {
        read(T, k);
        &self.map[k]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_read_holds_until_its_key_is_written() {
        let mut m: Logged<u32, u32, { tab::CLOSURES }> = Logged::default();
        m.insert(1, 10);
        begin_round();
        m.insert(9, 90);
        let at = new_stamp();
        let (_, reads, _, _) = speculate(u64::MAX, || (m.get(&1).copied(), m.get(&2).copied(), m.get(&9).copied())).unwrap();
        m.insert(3, 30);
        assert_eq!(stale_since(&reads, at), None, "a write before the check does not count");
        let later = new_stamp();
        m.insert(2, 20);
        assert_eq!(stale_since(&reads, at), Some(tab::CLOSURES));
        assert_eq!(stale_since(&reads, later + 1), None);
        end_round();
    }

    #[test]
    fn a_whole_table_read_is_stale_after_any_write() {
        let mut m: Logged<u32, u32, { tab::CLOSURES }> = Logged::default();
        let mut other: Logged<u32, u32, { tab::INSTANCES }> = Logged::default();
        begin_round();
        let at = new_stamp();
        let (_, reads, _, _) = speculate(u64::MAX, || m.len()).unwrap();
        other.insert(1, 1);
        assert_eq!(stale_since(&reads, at), None);
        m.insert(7, 7);
        assert_eq!(stale_since(&reads, at), Some(tab::CLOSURES));
        end_round();
    }

    #[test]
    fn a_window_check_out_of_fuel_stops() {
        assert!(speculate(3, || (0..10).for_each(|_| step(1))).is_none());
        assert_eq!(speculate(30, || (0..10).for_each(|_| step(1))).map(|r| r.3), Some(10));
        // Outside a window check, steps cost nothing.
        (0..10).for_each(|_| step(1));
    }
}
