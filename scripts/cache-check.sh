#!/usr/bin/env bash
# cache-check.sh [JOBS]: edit sequences through the persistent disk cache (unit objects in
# .lust-cache) with the default thread count; every step's binary must match an uncached
# (LUST_NO_CACHE=1) build. The gate-sized run of scripts/cache_check.py (see its header):
# 40 sequences of 4 steps, then a daemon run (one daemon per sequence, 12 sequences of 12
# steps, threads 1, 4, and 24 in turn) whose binaries must match too; about 12 s on boat.
# warm-check.sh covers cold vs threads vs daemon on one source; this covers the cache and
# the daemon's reused C across edits (fx-unitcache). Last, 6 sequences of 4 steps through
# the release driver (with a front image), whose binaries must be byte-identical with and
# without the cache and whose no-change rebuild must compile nothing, and 6 more with one fn
# per release unit (no image). With zig on PATH,
# the same through zig cc (musl, release C, then the epoch case with LLVM units): zig's
# own compile cache must not change a binary.
# Run after scripts/build.sh. Exit 0 = all same, 1 = a difference, 2 = setup error. The
# last line is the last run's summary; the exit code covers all runs.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
jobs=${1:-$(getconf _NPROCESSORS_ONLN)}
python3 "$root/scripts/cache_check.py" --seqs "${SEQS:-40}" --steps 4 --seed "${SEED:-1}" --jobs "$jobs"
rc=$?
python3 "$root/scripts/cache_check.py" --seqs "${DAEMON_SEQS:-12}" --steps 12 --seed "${SEED:-1}" --jobs "$jobs" --daemon --threads 1,4,24
drc=$?
# Release driver builds (release C, the host cc), the cached ones through a front image as
# the release job runs them: with and without the cache history, the binaries must be
# byte-identical, and a no-change rebuild must compile no unit.
python3 "$root/scripts/cache_check.py" --seqs "${RELEASE_SEQS:-6}" --steps 4 --seed "${SEED:-1}" --jobs "$jobs" --release --front
rrc=$?
# B1's skipping (the run above is its oracle): unassembled units' objects, programs' output.
python3 "$root/scripts/cache_check.py" --seqs "${RELEASE_SEQS:-6}" --steps 4 --seed "$((${SEED:-1} + 3))" --jobs "$jobs" --release --front --b1 skip
src=$?
rrc=$((rrc > src ? rrc : src))
# The same with one fn per unit: most of a unit's types are then held only by other
# definitions and declared as byte blocks (cgen `nested_block`), so a code path that reads
# an Adt's fields without recording it fails to compile here.
LUST_RELEASE_UNIT_KB=0 python3 "$root/scripts/cache_check.py" --seqs "${RELEASE_SEQS:-6}" --steps 4 --seed "$((${SEED:-1} + 7))" --jobs "$jobs" --release
brc=$?
rrc=$((rrc > brc ? rrc : brc))
# zig keys a compile on its source and args only: the same unit text with another input
# (a profile, linked bitcode, SOURCE_DATE_EPOCH) must still give its own object.
zrc=0
if command -v zig > /dev/null; then
  python3 "$root/scripts/cache_check.py" --seqs "${ZIG_SEQS:-2}" --steps 3 --seed "${SEED:-1}" --jobs "$jobs" --release --front --zig
  zc=$?
  python3 "$root/scripts/cache_check.py" --seqs 0 --jobs "$jobs" --release --front --zig --backend llvm
  zl=$?
  zrc=$((zc > zl ? zc : zl))
else
  echo "cache-check: no zig on PATH, the zig cache runs are skipped"
fi
m=$((rc > drc ? rc : drc))
m=$((m > rrc ? m : rrc))
exit $((m > zrc ? m : zrc))
