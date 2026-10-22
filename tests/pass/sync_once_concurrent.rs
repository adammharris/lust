// Threads that call `call_once` while the first run is still going wait for
// it, as std's `Once` makes them wait: none of them sees the `Once` as
// poisoned, and the closure runs once (twig-doc's `register_bundled`, called
// by two tests at the same time under `cargo test`).
use std::sync::Once;
use std::sync::atomic::{AtomicUsize, Ordering};

static ONCE: Once = Once::new();
static RUNS: AtomicUsize = AtomicUsize::new(0);

fn init() -> usize {
    ONCE.call_once(|| {
        std::thread::sleep(std::time::Duration::from_millis(50));
        RUNS.fetch_add(1, Ordering::SeqCst);
    });
    RUNS.load(Ordering::SeqCst)
}

fn main() {
    let hs: Vec<_> = (0..4).map(|_| std::thread::spawn(init)).collect();
    let seen: Vec<usize> = hs.into_iter().map(|h| h.join().unwrap()).collect();
    println!("{seen:?} runs={} completed={}", RUNS.load(Ordering::SeqCst), ONCE.is_completed());
}
