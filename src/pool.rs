// A persistent worker pool for the compiler's parallel phases (`par_map`).
//
// Workers start on the first parallel phase and serve every later phase. A
// cold compile used to spawn about a hundred threads (one set per phase), and
// each new thread started with a cold allocator heap, so every phase touched
// fresh memory. Reused workers keep their heaps.
//
// One phase runs on the pool at a time. A `par_map` that finds the pool busy
// (a nested call from inside a phase, a second compile on another daemon
// thread, or a stopped pool) uses scoped threads, as every phase did before
// the pool. Background work (the daemon guard, `set_background`) never
// takes the pool, so a check in flight does not hold it while a request is
// served.
//
// `stop` ends every pool thread and keeps the pool stopped while its guard
// lives. tcc's in-memory run forks (src/tcc.rs), and a fork copies only the
// calling thread, so no pool thread may be alive then. The next phase after
// the guard drops starts the pool again.
//
// Unsafe waiver (docs/ARCH.md section 9.6): `run` erases the lifetime of its
// job to share it with the workers. It is the one `unsafe` in lust's own
// code that is not a C or libc call; the SAFETY comment there is the proof.
use std::any::Any;
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex, MutexGuard, OnceLock};
use std::thread::JoinHandle;

/// The shared job: every worker that joins runs it once. It must split
/// its own work (`par_map` takes items from an atomic counter). Stored
/// with its lifetime erased; see `run`.
type Job = dyn Fn() + Sync + 'static;

thread_local! {
    /// Set on a background thread (the daemon guard, `set_background`) and
    /// on every phase thread it starts: the cancel flag of its work.
    static BACKGROUND: std::cell::RefCell<Option<std::sync::Arc<AtomicBool>>> = const { std::cell::RefCell::new(None) };
}

/// The unwind payload of background work whose cancel flag was set
/// (`set_background`), raised at the start of its next `par_map`.
pub struct Cancelled;

/// Marks this thread's compiler work as background work with a cancel
/// flag (None clears it). Its `par_map` phases never take the pool (they
/// run on scoped threads, which inherit the thread's scheduling priority),
/// so serve work keeps the pool's warm workers; and once `cancel` is set,
/// the next phase unwinds with `Cancelled` instead of running.
pub fn set_background(cancel: Option<std::sync::Arc<AtomicBool>>) {
    BACKGROUND.with(|b| *b.borrow_mut() = cancel);
}

/// True on a background thread (`set_background`) and the phase threads it starts.
pub fn is_background() -> bool {
    BACKGROUND.with(|b| b.borrow().is_some())
}

/// The name of every pool thread (also what /proc shows for it).
const THREAD_NAME: &str = "lust-pool";

/// The name of a scoped phase thread (the `par_map` fallback when the
/// pool is busy or stopped). Not `THREAD_NAME`: `stop`'s contract is
/// about pool threads only, and the stop test counts them by name.
const SCOPED_NAME: &str = "lust-par";

/// The stack size of every compiler thread (pool workers, scoped phase
/// threads, the daemon guard, and the thread `lust-core` runs on). The
/// default 2 MB overflows on deep expressions the parser accepts (a
/// 2000-term chain checks about 1500 deep in 2 MB); the parser bounds
/// AST depth (see `MAX_AST_DEPTH` in src/parser.rs), and this stack
/// holds several times that depth in every pass. The space is virtual:
/// pages are committed only as a thread's stack grows into them.
pub const STACK_SIZE: usize = 256 << 20;

/// A thread builder with the compiler stack size, for threads that run
/// compiler work outside the pool (such as the daemon guard). The main
/// thread gets the same room by a raised stack limit (src/main.rs).
pub fn thread(name: &str) -> std::thread::Builder {
    std::thread::Builder::new().name(name.into()).stack_size(STACK_SIZE)
}

/// Detached threads still running (`drop_detached`).
static DETACHED: AtomicUsize = AtomicUsize::new(0);

/// Drops `value` on a detached thread named `name` (large trees free off
/// the request's path), or here when no thread starts. A front image save
/// waits for these (`wait_detached`): they free heap blocks.
pub fn drop_detached<T: Send + 'static>(name: &str, value: T) {
    DETACHED.fetch_add(1, Ordering::AcqRel);
    let done = || DETACHED.fetch_sub(1, Ordering::AcqRel);
    if thread(name)
        .spawn(move || {
            drop(value);
            done();
        })
        .is_err()
    {
        // The closure (and `value`) dropped with the failed spawn.
        done();
    }
}

/// Waits until every `drop_detached` thread has finished.
pub fn wait_detached() {
    while DETACHED.load(Ordering::Acquire) != 0 {
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
}

struct State {
    /// The job of the current phase. Its real lifetime is the `run` call
    /// that set it: `run` returns only after every worker that took it is
    /// done, and late workers cannot take it (`wanted` is 0 by then).
    job: Option<&'static Job>,
    /// Bumped per phase, so a worker joins each phase at most once.
    epoch: u64,
    /// Workers that may still join this phase.
    wanted: usize,
    /// Workers inside the job now.
    running: usize,
    /// The first worker panic of this phase; `run` resumes it in its caller.
    panic: Option<Box<dyn Any + Send>>,
    /// A phase or a stop holds the pool.
    busy: bool,
    /// Set by `stop`: workers exit.
    quit: bool,
    /// `stop` calls waiting for the pool. While one waits, no new phase
    /// takes the pool, so a stream of phases cannot starve a stop.
    stops: usize,
}

struct Pool {
    state: Mutex<State>,
    /// Workers wait here for a phase or a stop.
    start: Condvar,
    /// `run` waits here for `running` to reach 0.
    done: Condvar,
    /// `stop` waits here for `busy` to clear.
    idle: Condvar,
    workers: usize,
    /// The helper thread that started the workers and joins them when they
    /// quit (see `start_threads`); None while the pool has no threads.
    helper: Mutex<Option<JoinHandle<()>>>,
}

fn lock(p: &Pool) -> MutexGuard<'_, State> {
    p.state.lock().unwrap_or_else(|e| e.into_inner())
}

static POOL: OnceLock<Pool> = OnceLock::new();

/// The thread count for parallel work: `LUST_THREADS` when it is set to a
/// number (0 counts as 1), else the core count. Read once per process. It
/// sizes the pool, caps `par_map`, and sets how many pieces the resolver
/// cuts a big file into.
pub fn threads() -> usize {
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| {
        let cores = std::thread::available_parallelism().map_or(4, |n| n.get());
        std::env::var("LUST_THREADS").ok().and_then(|v| v.parse().ok()).unwrap_or(cores).max(1)
    })
}

/// The process pool: `threads() - 1` workers (the caller is the last one).
/// Its threads start with the first phase (`start_threads`).
fn pool() -> &'static Pool {
    POOL.get_or_init(|| Pool {
        state: Mutex::new(State { job: None, epoch: 0, wanted: 0, running: 0, panic: None, busy: false, quit: false, stops: 0 }),
        start: Condvar::new(),
        done: Condvar::new(),
        idle: Condvar::new(),
        workers: threads() - 1,
        helper: Mutex::new(None),
    })
}

/// Starts the pool's threads when it has none. Called with the pool held
/// (`busy`), so no other thread starts or stops them at the same time. One
/// helper thread starts the workers, so a phase does not wait for every
/// thread start: its caller begins at once, and workers join the phase as
/// they come up. The helper then works as the last worker, and when the
/// workers quit it joins them, so joining the helper joins them all. A
/// thread that fails to start only leaves the phase fewer workers.
fn start_threads(p: &'static Pool) {
    let mut helper = p.helper.lock().unwrap_or_else(|e| e.into_inner());
    if helper.is_some() || p.workers == 0 {
        return;
    }
    let workers = p.workers;
    *helper = thread(THREAD_NAME)
        .spawn(move || {
            let others: Vec<JoinHandle<()>> =
                (1..workers).filter_map(|_| thread(THREAD_NAME).spawn(move || worker(p)).ok()).collect();
            worker(p);
            for h in others {
                let _ = h.join();
            }
        })
        .ok();
}

/// One pool thread: joins each phase it sees while the phase wants
/// workers, and returns at a stop.
fn worker(p: &'static Pool) {
    #[cfg(test)]
    let _live = tests::Live::new();
    let mut seen = 0u64;
    loop {
        let job = {
            let mut st = lock(p);
            loop {
                if st.quit {
                    return;
                }
                if st.epoch != seen && st.wanted > 0 {
                    break;
                }
                // A phase that needs no more workers counts as seen.
                seen = st.epoch;
                st = p.start.wait(st).unwrap_or_else(|e| e.into_inner());
            }
            seen = st.epoch;
            st.wanted -= 1;
            st.running += 1;
            st.job.expect("a phase in progress has a job")
        };
        let result = catch_unwind(AssertUnwindSafe(job));
        let mut st = lock(p);
        st.running -= 1;
        if let Err(payload) = result
            && st.panic.is_none()
        {
            st.panic = Some(payload);
        }
        if st.running == 0 {
            p.done.notify_all();
        }
    }
}

/// Releases the pool held by a phase (`run`) or a stop.
fn release(p: &Pool) {
    lock(p).busy = false;
    p.idle.notify_all();
}

/// Ends a phase on every exit path of `run`, a panic included: no more
/// workers may join, the borrowed job outlives every worker that took it,
/// and the pool is released. `panic` takes the phase's first worker panic
/// before the pool is free for the next phase.
struct EndPhase {
    p: &'static Pool,
    panic: Option<Box<dyn Any + Send>>,
}

impl EndPhase {
    /// Waits until no worker is inside the job. Idempotent.
    fn finish(&mut self) {
        let mut st = lock(self.p);
        st.wanted = 0;
        while st.running > 0 {
            st = self.p.done.wait(st).unwrap_or_else(|e| e.into_inner());
        }
        st.job = None;
        if self.panic.is_none() {
            self.panic = st.panic.take();
        }
    }
}

impl Drop for EndPhase {
    fn drop(&mut self) {
        self.finish();
        release(self.p);
    }
}

/// Runs `job` on this thread and on up to `extra` workers at once, and
/// returns when every run of it has returned. False (nothing ran) when the
/// pool is busy with another phase, stopped, or wanted by a `stop`. A
/// worker's panic resumes here with its own payload (its message was
/// already printed where it happened).
fn run(extra: usize, job: &(dyn Fn() + Sync)) -> bool {
    let p = pool();
    if p.workers == 0 {
        return false;
    }
    {
        let mut st = lock(p);
        if st.busy || st.stops > 0 {
            return false;
        }
        st.busy = true;
    }
    // Made at once, so every exit path from here on, a panic in the
    // thread start included, ends the phase and releases the pool.
    let mut end = EndPhase { p, panic: None };
    start_threads(p);
    // SAFETY (waiver: docs/ARCH.md 9.6): only the lifetime is erased.
    // Workers reach `job` only through `State::job` while `wanted` lets them
    // join, and `EndPhase` (which runs before this function returns or
    // unwinds) sets `wanted` to 0 and waits until no worker is inside the
    // job, then clears it. So no use of the reference outlives this call,
    // and `job` is `Sync` for shared use.
    let job_static: &'static Job = unsafe { std::mem::transmute::<&(dyn Fn() + Sync), &'static Job>(job) };
    {
        let mut st = lock(p);
        st.job = Some(job_static);
        st.epoch += 1;
        st.wanted = extra.min(p.workers);
        st.running = 0;
        st.panic = None;
    }
    p.start.notify_all();
    job();
    end.finish();
    let panic = end.panic.take();
    drop(end);
    if let Some(payload) = panic {
        resume_unwind(payload);
    }
    true
}

/// Holds the pool stopped: no pool thread is alive while this lives, and
/// every `par_map` meanwhile uses scoped threads. Dropping it lets the next
/// phase start the pool again.
pub struct Stopped {
    p: &'static Pool,
}

impl Drop for Stopped {
    fn drop(&mut self) {
        lock(self.p).quit = false;
        release(self.p);
    }
}

/// Stops the pool: waits for a phase in progress (another thread's) to end,
/// tells every pool thread to quit, and joins them all. A waiting stop goes
/// before any new phase. Call it where the process must run no other
/// compiler thread: tcc's in-memory run calls it before its fork. Never call
/// it from inside a `par_map` task.
pub fn stop() -> Stopped {
    let p = pool();
    {
        let mut st = lock(p);
        st.stops += 1;
        while st.busy {
            st = p.idle.wait(st).unwrap_or_else(|e| e.into_inner());
        }
        st.stops -= 1;
        st.busy = true;
        st.quit = true;
    }
    // Made at once, so a panic below still releases the pool.
    let stopped = Stopped { p };
    p.start.notify_all();
    let helper = p.helper.lock().unwrap_or_else(|e| e.into_inner()).take();
    if let Some(h) = helper {
        let _ = h.join();
    }
    stopped
}

/// Held under `cargo test` by each test whose code calls `stop` (the pool
/// tests, tcc's in-memory run): one test's stop would join or hold the pool
/// threads that another test is counting.
#[cfg(test)]
pub(crate) fn stop_tests() -> MutexGuard<'static, ()> {
    static LOCK: Mutex<()> = Mutex::new(());
    LOCK.lock().unwrap_or_else(|e| e.into_inner())
}

/// Set by a one-shot compile (`small_pages_in_parallel`): parallel regions
/// run without transparent huge pages, serial code keeps them.
static SMALL_PAGES: AtomicBool = AtomicBool::new(false);
/// Parallel regions open now (nested `par_map` calls count too).
static PARALLEL_DEPTH: AtomicUsize = AtomicUsize::new(0);

/// Makes every later `par_map` run with transparent huge pages off and
/// turn them on again when it ends. Pool threads touch fresh memory
/// sparsely, so a huge page costs a 2 MB zeroing per first touch, under
/// contention; serial phases touch memory densely and gain from them
/// (see `tcc::set_huge_pages`).
pub fn small_pages_in_parallel() {
    SMALL_PAGES.store(true, Ordering::Relaxed);
}

/// Open while one parallel region runs: the first one in turns huge pages
/// off, the last one out turns them on.
struct SmallPages;

impl SmallPages {
    fn enter() -> Option<SmallPages> {
        if !SMALL_PAGES.load(Ordering::Relaxed) {
            return None;
        }
        if PARALLEL_DEPTH.fetch_add(1, Ordering::AcqRel) == 0 {
            crate::tcc::set_huge_pages(false);
        }
        Some(SmallPages)
    }
}

impl Drop for SmallPages {
    fn drop(&mut self) {
        if PARALLEL_DEPTH.fetch_sub(1, Ordering::AcqRel) == 1 {
            crate::tcc::set_huge_pages(true);
        }
    }
}

/// Runs `f` for each item on `threads()` threads. Results keep the input
/// order. Items are taken in small batches from one atomic counter, so
/// uneven items still spread over every thread. A panic in `f` resumes in
/// the caller with its own payload.
pub fn par_map<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let background = BACKGROUND.with(|b| b.borrow().clone());
    if background.as_ref().is_some_and(|c| c.load(Ordering::Relaxed)) {
        resume_unwind(Box::new(Cancelled));
    }
    let n = threads().min(items.len().max(1));
    if n <= 1 {
        return items.iter().map(f).collect();
    }
    let _pages = SmallPages::enter();
    let next = AtomicUsize::new(0);
    // Batches amortize the atomic counter, but stay small enough to keep every thread busy.
    let batch = (items.len() / (n * 8)).clamp(1, 16);
    let take = || {
        let mut out = Vec::new();
        loop {
            let start = next.fetch_add(batch, Ordering::Relaxed);
            if start >= items.len() {
                break;
            }
            let end = (start + batch).min(items.len());
            out.extend(items[start..end].iter().enumerate().map(|(k, item)| (start + k, f(item))));
        }
        out
    };
    let parts: Mutex<Vec<Vec<(usize, R)>>> = Mutex::new(Vec::new());
    let job = || {
        let out = take();
        parts.lock().unwrap_or_else(|e| e.into_inner()).push(out);
    };
    let chunks: Vec<Vec<(usize, R)>> = if background.is_none() && run(n - 1, &job) {
        parts.into_inner().unwrap_or_else(|e| e.into_inner())
    } else {
        // A background phase's threads carry its cancel flag, so their
        // nested phases stay off the pool too.
        let scoped = || {
            set_background(background.clone());
            take()
        };
        std::thread::scope(|s| {
            let handles: Vec<_> = (0..n).map(|_| thread(SCOPED_NAME).spawn_scoped(s, scoped).unwrap_or_else(|_| s.spawn(scoped))).collect();
            handles.into_iter().map(|h| h.join().unwrap_or_else(|payload| resume_unwind(payload))).collect()
        })
    };
    let mut all: Vec<Option<R>> = (0..items.len()).map(|_| None).collect();
    for chunk in chunks {
        for (i, r) in chunk {
            all[i] = Some(r);
        }
    }
    all.into_iter().map(|r| r.unwrap()).collect()
}

#[cfg(test)]
mod tests {
    use super::{THREAD_NAME, par_map, stop, stop_tests};
    use std::sync::atomic::{AtomicUsize, Ordering};

    /// Pool threads inside `worker` now: each counts itself while it runs.
    static LIVE: AtomicUsize = AtomicUsize::new(0);

    pub(super) struct Live;

    impl Live {
        pub(super) fn new() -> Live {
            LIVE.fetch_add(1, Ordering::SeqCst);
            Live
        }
    }

    impl Drop for Live {
        fn drop(&mut self) {
            LIVE.fetch_sub(1, Ordering::SeqCst);
        }
    }

    /// Results come back in input order through the pool, a nested call
    /// (which finds the pool busy) still runs every item, and the pool
    /// serves the next phase after both.
    #[test]
    fn par_map_order_nesting_and_reuse() {
        let items: Vec<u64> = (0..1000).collect();
        let out = par_map(&items, |&i| par_map(&[i, i + 1], |&j| j * 2).iter().sum::<u64>());
        assert_eq!(out, items.iter().map(|&i| 4 * i + 2).collect::<Vec<_>>());
        let again = par_map(&items, |&i| i + 1);
        assert_eq!(again, (1..=1000).collect::<Vec<_>>());
    }

    /// A panic in a task reaches the caller with its own payload (on the
    /// pool or on scoped threads, whichever ran it), and the pool still
    /// works after it.
    #[test]
    fn par_map_panic_reaches_caller() {
        let items: Vec<u32> = (0..64).collect();
        for _ in 0..20 {
            let r = std::panic::catch_unwind(|| par_map(&items, |&i| if i == 40 { panic!("task 40") } else { i }));
            let payload = r.expect_err("the panic reaches the caller");
            assert_eq!(payload.downcast_ref::<&str>(), Some(&"task 40"));
        }
        assert_eq!(par_map(&items, |&i| i * 3)[63], 189);
    }

    /// Two threads race `par_map` (a daemon guard compile next to a served
    /// compile), and a third stops the pool now and then: one phase takes
    /// the pool, the others use scoped threads, every call returns every
    /// result in order, and each stop gets its turn (no new phase takes the
    /// pool while a stop waits).
    #[test]
    fn racing_par_maps_and_stops() {
        let _serial = stop_tests();
        let items: Vec<u64> = (0..3000).collect();
        let done = std::sync::atomic::AtomicBool::new(false);
        std::thread::scope(|s| {
            let racers: Vec<_> = (0..2u64)
                .map(|t| {
                    let items = &items;
                    s.spawn(move || {
                        for round in 0..150u64 {
                            let out = par_map(items, |&i| i * 3 + t + round);
                            assert!(out.iter().enumerate().all(|(i, &v)| v == i as u64 * 3 + t + round), "racer {t} round {round}");
                        }
                    })
                })
                .collect();
            let stopper = s.spawn(|| {
                let mut stops = 0;
                loop {
                    drop(stop());
                    stops += 1;
                    if done.load(Ordering::SeqCst) {
                        return stops;
                    }
                    std::thread::yield_now();
                }
            });
            for r in racers {
                r.join().unwrap();
            }
            done.store(true, Ordering::SeqCst);
            assert!(stopper.join().unwrap() > 0, "a stop got its turn");
        });
    }

    /// The live threads of this process with the pool's thread name.
    fn pool_threads() -> usize {
        std::fs::read_dir("/proc/self/task")
            .map(|d| {
                d.filter_map(|e| e.ok())
                    .filter(|e| std::fs::read_to_string(e.path().join("comm")).is_ok_and(|c| c.trim_end() == THREAD_NAME))
                    .count()
            })
            .unwrap_or(0)
    }

    /// `stop` leaves no pool thread alive while its guard lives (what tcc's
    /// in-memory fork needs): when it returns, every pool thread has left
    /// its loop and been joined, and the OS lists none soon after. A phase
    /// meanwhile still runs every item on scoped threads, and after the
    /// guard drops the pool starts again.
    #[test]
    fn stop_joins_every_pool_thread() {
        if std::thread::available_parallelism().map_or(1, |n| n.get()) < 2 || !std::path::Path::new("/proc/self/task").exists() {
            return;
        }
        let _serial = stop_tests();
        let items: Vec<u64> = (0..4096).collect();
        let slow = |&i: &u64| -> u64 { (0..2000u64).fold(i, |a, k| a.wrapping_mul(31).wrapping_add(k)) };
        let want: Vec<u64> = items.iter().map(slow).collect();
        let secs = |n| std::time::Duration::from_secs(n);
        // Phases until pool threads are up (other tests may hold the pool
        // for a while, and a new thread takes its name as it starts). A loaded
        // gate box can take many seconds, as for the restart below.
        let t0 = std::time::Instant::now();
        while pool_threads() == 0 && t0.elapsed() < secs(30) {
            assert_eq!(par_map(&items, slow), want);
        }
        assert!(pool_threads() > 0, "the pool has threads before the stop");
        let stopped = stop();
        assert_eq!(LIVE.load(Ordering::SeqCst), 0, "a pool thread runs after stop returned");
        // A thread can stay listed for a moment after its join returns.
        let t0 = std::time::Instant::now();
        while pool_threads() > 0 && t0.elapsed() < secs(2) {
            std::thread::yield_now();
        }
        assert_eq!(pool_threads(), 0, "pool threads alive after stop");
        assert_eq!(par_map(&items, slow), want);
        assert_eq!(pool_threads(), 0, "a stopped pool must not start threads");
        assert_eq!(LIVE.load(Ordering::SeqCst), 0);
        drop(stopped);
        // Restarting threads can take seconds when other test binaries or gates load the box.
        let t0 = std::time::Instant::now();
        while pool_threads() == 0 && t0.elapsed() < secs(30) {
            assert_eq!(par_map(&items, slow), want);
        }
        assert!(pool_threads() > 0, "the pool starts again after the guard drops");
    }
}
