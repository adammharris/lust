#!/usr/bin/env bash
# warm-check.sh [JOBS]: every tests/pass case must build to the same program four ways:
#   cold   one in-process compile (LUST_NO_DAEMON=1), the reference;
#   t1     the same with LUST_THREADS=1 (parallel phases in one thread);
#   d1     the first build through a daemon (a fresh session);
#   d2     a second build of the unchanged file through the same daemon (a warm session: the
#          shape of `lust check` then `lust build`, or a rebuild).
# Each binary runs once; stdout and exit code must equal cold's. Any build that fails where cold
# passed, any difference, and any "guard:" line in a daemon log is a failure. This catches order
# and state dependence in collect, mono, and codegen (fx-scanfa round 2: a warm build said
# "`take` (Template) has no generated body" because a pending discovery was stored for replay).
# Run after scripts/build.sh. Env: STRIDE=n checks every n-th case (default 1), CASES=<glob>.
# Every selected case must give exactly one result line; a missing line fails the run.
# Exit 0 = all same, 1 = a difference, a case whose cold build fails, or a missing result,
# 2 = setup error.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
[ -x "$lust" ] || { echo "error: $lust not built. Run scripts/build.sh first."; exit 2; }
jobs=${1:-$(getconf _NPROCESSORS_ONLN)}
stride=${STRIDE:-1}
work=$(mktemp -d "${TMPDIR:-/tmp}/warm-check.XXXXXX")
trap 'rm -rf "$work"' EXIT
unset LUST_DAEMON_SOCKET LUST_CACHE_DIR
extras=$(cd "$root/tests/pass" && ls | grep -v '\.rs$' | tr '\n' ' ')
export LUST_NO_CACHE=1 lust work root extras

# one <case>: prints "ok <name>" or "bad <name>: <why>" (a cold build that fails is bad: a
# tests/pass case must build).
one() {
  local f=$1 name d out
  name=$(basename "$f" .rs)
  d=$work/$name
  mkdir -p "$d" && cp "$f" "$d/main.rs" || { echo "bad $name: setup"; return; }
  # The files a case includes (`include_bytes!`, `#[path]` modules) sit next to it.
  for x in $extras; do ln -s "$root/tests/pass/$x" "$d/$x"; done
  cd "$d" || return
  run() { ( timeout 20 "./$1" > "$1.out" 2>/dev/null ) 2>/dev/null; echo "exit=$?" >> "$1.out"; }
  if ! LUST_NO_DAEMON=1 timeout 120 "$lust" build main.rs -o cold > cold.err 2>&1; then
    echo "bad $name: cold build failed: $(head -c 200 cold.err)"; return
  fi
  run cold
  LUST_NO_DAEMON=1 LUST_THREADS=1 timeout 120 "$lust" build main.rs -o t1 > t1.err 2>&1 || { echo "bad $name: LUST_THREADS=1 build failed: $(head -c 200 t1.err)"; return; }
  timeout 120 "$lust" build main.rs -o d1 > d1.err 2>&1 || out="daemon build failed: $(head -c 200 d1.err)"
  timeout 120 "$lust" build main.rs -o d2 > d2.err 2>&1 || out="${out:-warm daemon build failed: $(head -c 200 d2.err)}"
  # Removing the socket makes the daemon exit (daemon.rs).
  rm -f .lust-daemon-*.sock
  [ -n "${out:-}" ] && { echo "bad $name: $out"; return; }
  for b in t1 d1 d2; do
    run $b
    cmp -s cold.out $b.out || { echo "bad $name: $b output differs from cold: $(diff cold.out $b.out | head -4 | tr '\n' ' ')"; return; }
  done
  if grep -q "^guard:" .lust-cache/daemon.log 2>/dev/null; then
    echo "bad $name: $(grep -m1 '^guard:' .lust-cache/daemon.log | head -c 200)"; return
  fi
  echo "ok $name"
  cd "$work" && rm -rf "$d"
}
export -f one

cases=$(ls "$root"/tests/pass/${CASES:-*}.rs | awk -v s="$stride" 'NR % s == 0')
[ -n "$cases" ] || { echo "error: no cases"; exit 2; }
n=$(printf '%s\n' $cases | wc -l)
printf '%s\n' $cases | xargs -P "$jobs" -I{} bash -c 'one {}' > "$work/results.txt"
ok=$(grep -c '^ok ' "$work/results.txt")
bad=$(grep -c '^bad ' "$work/results.txt")
grep -E '^bad ' "$work/results.txt" | sort
# A case whose job died before it printed (or printed twice) shows up here.
missing=$(( n - ok - bad ))
[ "$missing" -eq 0 ] || echo "error: $n cases, but $((ok + bad)) result lines"
echo "warm-check: $ok same, $bad different, $missing missing, of $n cases"
[ "$bad" -eq 0 ] && [ "$missing" -eq 0 ]
