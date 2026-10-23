#!/usr/bin/env bash
# Client tests: daemon autostart, the whole-request disk cache, and the release
# handoff to Cargo/rustc. Run after `cargo build --release`.
#   autostart: fresh dir, first build cold and standalone, second build served
#              by the daemon (its binary loads libbase.so). Plus LUST_NO_DAEMON,
#              a 4-way start race, a held daemon lock (no second daemon), and the
#              idle timeout.
#   temp:      the daemon temp dir dies with the daemon (SIGTERM, SIGINT, socket
#              removal, idle), a startup sweep removes SIGKILL leftovers, and
#              kept binaries still run.
#   cache:     hit, then miss on edit, on -g, and on a compiler id change.
#              Eviction keeps the newest entries under the size cap.
#   release:   single file via rustc, a tiny Cargo project via cargo (package
#              and bin selection, --profile), and `check --rustc` as oracle.
# Every client call runs under the one timeout rule (scripts/timeout-lib.sh)
# through a generated shim: CASE_TIMEOUT seconds (default 60), one solo retry
# at RETRY_CASE_TIMEOUT (default 6x). A finished retry is reported as "slow"
# at the end; a second timeout is a HANG and fails the suite. Without the
# shim, a hung client or daemon would hang this suite until the gate's step
# limit killed it, with no case named.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
if [ ! -x "$lust" ]; then
  echo "error: $lust not built. Run cargo build --release first."
  exit 2
fi
unset LUST_DAEMON_SOCKET LUST_CACHE_DIR LUST_NO_DAEMON LUST_NO_CACHE \
  LUST_CACHE_COMPILER_ID LUST_CACHE_MAX_BYTES LUST_DAEMON_IDLE LUST_THREADS
work=$(mktemp -d)
pass=0
fail=0
daemon_dirs=()

# The timeout shim (see the header). Slow and hang lines go to files, not
# stderr: several checks compare a captured command's full output byte for
# byte, and a slow retry must not fail them. The lines print at the end.
case_timeout=${CASE_TIMEOUT:-60}
retry_timeout=${RETRY_CASE_TIMEOUT:-$((case_timeout * 6))}
cat >"$work/lust" <<EOF
#!/bin/sh
timeout "$case_timeout" "$lust" "\$@"; st=\$?
case \$st in 124|137) ;; *) exit \$st ;; esac
timeout "$retry_timeout" "$lust" "\$@"; st=\$?
case \$st in
  124|137) echo "HANG: lust \$* timed out alone at ${retry_timeout}s (first at ${case_timeout}s)" >>"$work/timeouts.log"; echo hang >>"$work/hangs.log" ;;
  *) echo "slow: lust \$* timed out at ${case_timeout}s, finished alone at ${retry_timeout}s" >>"$work/timeouts.log" ;;
esac
exit \$st
EOF
chmod +x "$work/lust"
lust=$work/lust

ok() { pass=$((pass + 1)); echo "ok   $1"; }
bad() { fail=$((fail + 1)); echo "FAIL $1: $2"; }
# check <name> <test...> : ok when the test command succeeds.
check() { local name=$1; shift; if "$@" >/dev/null 2>&1; then ok "$name"; else bad "$name" "command failed: $*"; fi; }

# sock <dir> : the daemon socket path in <dir> (its name holds the compiler build hash).
sock() { local f; for f in "$1"/.lust-daemon-*.sock "$1"/.lust-daemon-*.sock.lock; do [ -e "$f" ] && { echo "${f%.lock}"; return; }; done; echo "$1/.lust-daemon-none.sock"; }

stop_daemon() { # stop_daemon <dir>
  local pid
  pid=$(cat "$(sock "$1").lock" 2>/dev/null) || return 0
  [ -n "$pid" ] && kill "$pid" 2>/dev/null
  return 0
}
cleanup() {
  local d
  for d in "${daemon_dirs[@]}"; do stop_daemon "$d"; done
  rm -rf "$work"
}
trap cleanup EXIT

# loads_base <exe> : true when <exe> loads libbase.so, so a daemon built it. ldd output is
# captured first: `ldd | grep -q` under pipefail fails when grep exits at the match and ldd
# takes SIGPIPE on its next line (the `race` flake: the binary was right, the check was not).
loads_base() { local out; out=$(ldd "$1" 2>/dev/null) && [[ $out == *libbase* ]]; }
wait_socket() { # wait_socket <dir> : true when the daemon socket appears
  local i
  for i in $(seq 1 100); do [ -S "$(sock "$1")" ] && return 0; sleep 0.05; done
  return 1
}
wait_socket_path() { # wait_socket_path <socket> : true when that socket appears
  local i
  for i in $(seq 1 100); do [ -S "$1" ] && return 0; sleep 0.05; done
  return 1
}
fresh() { # fresh <name> : a new dir with a hello.rs, prints its path
  local d=$work/$1
  mkdir -p "$d"
  printf 'fn main() { println!("hello {}", 40 + 2); }\n' >"$d/hello.rs"
  echo "$d"
}

# ---------------------------------------------------------------- autostart
d=$(fresh autostart); daemon_dirs+=("$d")
(cd "$d" && "$lust" build hello.rs -o h1) >/dev/null 2>&1
check "autostart: first build ok" test -x "$d/h1"
if loads_base "$d/h1"; then
  bad "autostart: first build is standalone" "loads libbase.so, so a daemon built it"
else
  ok "autostart: first build is standalone (cold)"
fi
check "autostart: first build runs" test "$("$d/h1")" = "hello 42"
check "autostart: daemon socket appears" wait_socket "$d"
(cd "$d" && "$lust" build hello.rs -o h2) >/dev/null 2>&1
if loads_base "$d/h2"; then
  ok "autostart: second build served by the daemon"
else
  bad "autostart: second build served by the daemon" "no libbase.so in ldd output"
fi
check "autostart: second build runs" test "$("$d/h2")" = "hello 42"
check "autostart: log file in cache dir" test -s "$d/.lust-cache/daemon.log"
stop_daemon "$d"; sleep 0.3

d=$(fresh nodaemon)
(cd "$d" && LUST_NO_DAEMON=1 "$lust" check hello.rs) >/dev/null 2>&1
sleep 0.5
if [ -S "$(sock "$d")" ]; then bad "LUST_NO_DAEMON: no daemon starts" "socket exists"; else ok "LUST_NO_DAEMON: no daemon starts"; fi

# A warm daemon must re-expand what positions and included files feed:
# adding blank lines moves `line!`, and editing only the included file
# changes `include_str!`. LUST_NO_DAEMON must also skip the live daemon.
d=$(fresh warmedit); daemon_dirs+=("$d")
printf 'fn main() { println!("{} {}", line!(), include_str!("data.txt")); }\n' >"$d/hello.rs"
printf one >"$d/data.txt"
(cd "$d" && "$lust" run hello.rs) >/dev/null 2>&1
check "warmedit: daemon socket appears" wait_socket "$d"
out1=$(cd "$d" && "$lust" run hello.rs 2>&1)
check "warmedit: warm v1 output" test "$out1" = "1 one"
printf '\n\nfn main() { println!("{} {}", line!(), include_str!("data.txt")); }\n' >"$d/hello.rs"
printf two >"$d/data.txt"
out2=$(cd "$d" && "$lust" run hello.rs 2>&1)
check "warmedit: warm v2 sees new line and included file" test "$out2" = "3 two"
(cd "$d" && LUST_NO_DAEMON=1 "$lust" build hello.rs -o hnd) >/dev/null 2>&1
if loads_base "$d/hnd"; then
  bad "LUST_NO_DAEMON: live daemon not used" "loads libbase.so, so the daemon built it"
else
  ok "LUST_NO_DAEMON: live daemon not used"
fi
stop_daemon "$d"; sleep 0.3

d=$(fresh race); daemon_dirs+=("$d")
pids=()
for i in 1 2 3 4; do (cd "$d" && "$lust" check hello.rs) >/dev/null 2>&1 & pids+=($!); done
race_rc=0
for p in "${pids[@]}"; do wait "$p" || race_rc=1; done
check "race: 4 concurrent first commands pass" test $race_rc -eq 0
check "race: one daemon socket serves after" wait_socket "$d"
(cd "$d" && "$lust" build hello.rs -o h) >/dev/null 2>&1
if loads_base "$d/h"; then ok "race: warm build after the race"; else bad "race: warm build after the race" "no libbase.so"; fi
stop_daemon "$d"; sleep 0.3

# The lock file is the single-daemon guarantee: whoever holds its flock owns the socket.
# This is the race window frozen: a daemon holds the lock but its pid is not written yet
# (the file still names the exited client that started it). A client must not replace the
# file or start a second daemon: two daemons on two lock files would remove each other's socket.
d=$(fresh lockheld); s=$d/s.sock
sh -c 'exit 0' & dead=$!; wait $dead
printf '%s' "$dead" >"$s.lock"
# One process holds the lock: the subshell execs into sleep with fd 9, so killing it frees the lock.
( exec 9>>"$s.lock"; flock 9; exec sleep 30 ) & holder=$!
for i in $(seq 1 100); do flock -n "$s.lock" true || break; sleep 0.05; done
ino=$(stat -c %i "$s.lock")
(cd "$d" && LUST_DAEMON_SOCKET=$s LUST_DAEMON_IDLE=5 "$lust" check hello.rs) >/dev/null 2>&1
check "lockheld: client answers cold" test $? -eq 0
check "lockheld: a held lock file is never replaced" test "$(stat -c %i "$s.lock")" = "$ino"
sleep 0.5
check "lockheld: no second daemon starts" test ! -S "$s"
kill "$holder" 2>/dev/null; wait "$holder" 2>/dev/null
# Once the holder is gone, the leftover file (stale pid, no flock) does not block a start.
(cd "$d" && LUST_DAEMON_SOCKET=$s LUST_DAEMON_IDLE=5 "$lust" check hello.rs) >/dev/null 2>&1
check "lockheld: a free stale lock file allows a start" wait_socket_path "$s"
kill "$(cat "$s.lock" 2>/dev/null)" 2>/dev/null; sleep 0.3

d=$(fresh idle); daemon_dirs+=("$d")
(cd "$d" && LUST_DAEMON_IDLE=1 "$lust" check hello.rs) >/dev/null 2>&1
check "idle: daemon starts" wait_socket "$d"
ipid=$(cat "$(sock "$d").lock" 2>/dev/null)
gone=0
for i in $(seq 1 100); do
  if ! kill -0 "$ipid" 2>/dev/null; then gone=1; break; fi
  sleep 0.1
done
check "idle: daemon exits after the idle span" test $gone -eq 1
if [ -S "$(sock "$d")" ]; then bad "idle: socket removed on exit" "socket still there"; else ok "idle: socket removed on exit"; fi
(cd "$d" && LUST_DAEMON_IDLE=0 "$lust" check hello.rs) >/dev/null 2>&1
check "idle: next command works and restarts a daemon" wait_socket "$d"
stop_daemon "$d"; sleep 0.3

# ---------------------------------------------------------- temp cleanup
# The daemon's temp dir (/tmp/lust-daemon-<pid>) must die with the daemon
# on every exit path, and executables built against its base libraries
# must keep running (bases live in .lust-cache/bases, not in temp space).
# A private TMPDIR keeps these checks exact and fast.
saved_tmpdir=${TMPDIR:-}
export TMPDIR=$work/td; mkdir -p "$TMPDIR"
wait_gone() { # wait_gone <path>
  local i
  for i in $(seq 1 100); do [ ! -e "$1" ] && return 0; sleep 0.05; done
  return 1
}
wait_dead_pid() { # wait_dead_pid <pid>
  local i
  for i in $(seq 1 100); do kill -0 "$1" 2>/dev/null || return 0; sleep 0.05; done
  return 1
}
# warm_build <dir> <out> : cold build (starts a daemon), then a daemon build to <out>.
warm_build() {
  (cd "$1" && "$lust" build hello.rs -o warm1) >/dev/null 2>&1
  wait_socket "$1" >/dev/null
  (cd "$1" && "$lust" build hello.rs -o "$2") >/dev/null 2>&1
}
for sig in TERM INT; do
  d=$(fresh tmp$sig); daemon_dirs+=("$d")
  warm_build "$d" warm2
  pid=$(cat "$(sock "$d").lock" 2>/dev/null)
  check "temp $sig: temp dir exists while daemon runs" test -d "$TMPDIR/lust-daemon-$pid"
  kill -"$sig" "$pid" 2>/dev/null
  check "temp $sig: daemon exits" wait_dead_pid "$pid"
  if wait_gone "$TMPDIR/lust-daemon-$pid"; then ok "temp $sig: temp dir removed on exit"; else bad "temp $sig: temp dir removed on exit" "$TMPDIR/lust-daemon-$pid remains"; fi
  if [ -S "$(sock "$d")" ]; then bad "temp $sig: socket removed on exit" "socket still there"; else ok "temp $sig: socket removed on exit"; fi
  check "temp $sig: daemon-built binary still runs" test "$("$d/warm2")" = "hello 42"
done
# Removing the socket file is also a stop request: the daemon takes the
# same controlled exit and removes its temp dir.
d=$(fresh tmpsockrm); daemon_dirs+=("$d")
warm_build "$d" warm2
pid=$(cat "$(sock "$d").lock" 2>/dev/null)
s=$(sock "$d")
check "temp sockrm: temp dir exists while daemon runs" test -d "$TMPDIR/lust-daemon-$pid"
rm -f "$s"
check "temp sockrm: daemon exits" wait_dead_pid "$pid"
if wait_gone "$TMPDIR/lust-daemon-$pid"; then ok "temp sockrm: temp dir removed on exit"; else bad "temp sockrm: temp dir removed on exit" "$TMPDIR/lust-daemon-$pid remains"; fi
check "temp sockrm: daemon-built binary still runs" test "$("$d/warm2")" = "hello 42"
# Idle exit also removes the temp dir (directory checked here; the
# socket and restart behavior are covered in the idle section above).
d=$(fresh tmpidle); daemon_dirs+=("$d")
(cd "$d" && LUST_DAEMON_IDLE=1 "$lust" check hello.rs) >/dev/null 2>&1
wait_socket "$d" >/dev/null
pid=$(cat "$(sock "$d").lock" 2>/dev/null)
check "temp idle: daemon exits" wait_dead_pid "$pid"
if wait_gone "$TMPDIR/lust-daemon-$pid"; then ok "temp idle: temp dir removed on exit"; else bad "temp idle: temp dir removed on exit" "dir remains"; fi
# SIGKILL cannot clean up; the next daemon's startup sweep does, and a
# kept binary survives both (its base is not in the temp dir).
d=$(fresh tmpkill); daemon_dirs+=("$d")
warm_build "$d" warm2
pid=$(cat "$(sock "$d").lock" 2>/dev/null)
kill -9 "$pid" 2>/dev/null
wait_dead_pid "$pid" >/dev/null
check "temp kill: temp dir left by SIGKILL" test -d "$TMPDIR/lust-daemon-$pid"
mkdir -p "$TMPDIR/lust-daemon-4000000002" "$TMPDIR/lust-4000000002"
touch "$TMPDIR/lust-daemon-4000000002/x.o" "$TMPDIR/lust-rustc-check-4000000002.rmeta"
mkdir -p "$TMPDIR/lust-daemon-$$"
d2=$(fresh tmpsweep); daemon_dirs+=("$d2")
(cd "$d2" && "$lust" check hello.rs) >/dev/null 2>&1
wait_socket "$d2" >/dev/null
if wait_gone "$TMPDIR/lust-daemon-$pid"; then ok "temp sweep: SIGKILLed daemon dir swept at startup"; else bad "temp sweep: SIGKILLed daemon dir swept at startup" "dir remains"; fi
if wait_gone "$TMPDIR/lust-daemon-4000000002" && wait_gone "$TMPDIR/lust-4000000002" && wait_gone "$TMPDIR/lust-rustc-check-4000000002.rmeta"; then
  ok "temp sweep: dead-pid lust dirs and files swept"
else
  bad "temp sweep: dead-pid lust dirs and files swept" "a dead entry remains"
fi
check "temp sweep: live-pid dir kept" test -d "$TMPDIR/lust-daemon-$$"
rm -rf "$TMPDIR/lust-daemon-$$"
check "temp sweep: kept binary still runs after sweep" test "$("$d/warm2")" = "hello 42"
stop_daemon "$d2"; sleep 0.3
# A cold one-shot build leaves no temp dir either (the cached runtime
# object file is intentional; only directories count here).
d=$(fresh tmpcold)
(cd "$d" && LUST_NO_DAEMON=1 "$lust" build hello.rs -o cold1) >/dev/null 2>&1
if [ -z "$(find "$TMPDIR" -mindepth 1 -type d -print -quit)" ]; then ok "temp cold: no temp dir after a one-shot build"; else bad "temp cold: no temp dir after a one-shot build" "a dir remains in TMPDIR"; fi
check "temp cold: binary runs" test "$("$d/cold1")" = "hello 42"
if [ -n "$saved_tmpdir" ]; then export TMPDIR=$saved_tmpdir; else unset TMPDIR; fi

# -------------------------------------------------------------------- cache
d=$(fresh cache)
run_lust() { (cd "$d" && LUST_NO_DAEMON=1 "$lust" "$@") 2>&1; }
out=$(run_lust build hello.rs -o h --timings)
case "$out" in *"cache hit"*) bad "cache: first build misses" "reported a hit";; *) ok "cache: first build misses";; esac
check "cache: default dir next to source" test -d "$d/.lust-cache"
out=$(run_lust build hello.rs -o h --timings)
case "$out" in *"whole-request cache hit"*) ok "cache: second build hits";; *) bad "cache: second build hits" "no hit line";; esac
check "cache: hit build runs" test "$("$d/h")" = "hello 42"
run_lust check hello.rs --timings >/dev/null
out=$(run_lust check hello.rs --timings)
case "$out" in *"whole-request cache hit"*) ok "cache: second check hits";; *) bad "cache: second check hits" "no hit line";; esac
sed 's/40 + 2/1 + 2/' "$d/hello.rs" >"$d/hello.rs.tmp" && mv "$d/hello.rs.tmp" "$d/hello.rs"
out=$(run_lust build hello.rs -o h --timings)
case "$out" in *"cache hit"*) bad "cache: edit misses" "reported a hit after an edit";; *) ok "cache: edit misses";; esac
check "cache: edited build has new output" test "$("$d/h")" = "hello 3"
out=$(run_lust build hello.rs -o h -g --timings)
case "$out" in *"cache hit"*) bad "cache: -g change misses" "reported a hit";; *) ok "cache: -g change misses";; esac
out=$(run_lust build hello.rs -o h -g --timings)
case "$out" in *"cache hit"*) ok "cache: repeated -g build hits";; *) bad "cache: repeated -g build hits" "no hit line";; esac
out=$( (cd "$d" && LUST_NO_DAEMON=1 LUST_CACHE_COMPILER_ID=other-compiler "$lust" check hello.rs --timings) 2>&1 )
case "$out" in *"cache hit"*) bad "cache: compiler id change misses" "reported a hit";; *) ok "cache: compiler id change misses";; esac
out=$( (cd "$d" && LUST_NO_DAEMON=1 LUST_RELEASE_C=1 "$lust" build hello.rs -o h -g --timings) 2>&1 )
case "$out" in *"cache hit"*) bad "cache: a LUST_ setting misses" "reported a hit";; *) ok "cache: a LUST_ setting misses";; esac
out=$( (cd "$d" && LUST_NO_DAEMON=1 LUST_NO_CACHE=1 "$lust" check hello.rs --timings) 2>&1 )
case "$out" in *"cache hit"*) bad "cache: LUST_NO_CACHE never hits" "reported a hit";; *) ok "cache: LUST_NO_CACHE never hits";; esac

d=$(fresh evict)
cap=60000
evict_run() { (cd "$d" && LUST_NO_DAEMON=1 LUST_CACHE_DIR="$d/c" LUST_CACHE_MAX_BYTES=$cap "$lust" "$@") 2>&1; }
for n in 1 2 3 4 5; do
  printf 'fn main() { println!("n %s"); }\n' "$n" > "$d/f$n.rs"
  # A mark between build 4 and build 5 (a second apart from both: file times are coarse).
  [ "$n" = 5 ] && { sleep 1; touch "$d/mark"; sleep 1; }
  evict_run build "f$n.rs" -o "h$n" >/dev/null
  [ "$n" = 1 ] && first_entry=$(ls "$d/c" | grep '^req-' | grep -v '\.exe$' | head -1)
done
# The cap bounds what the last build did not write or use: a build never evicts the unit
# objects it stored or took (a tsgo release holds about 1 GB of them, more than the default
# cap) or its own whole-request entry, so those may pass the cap together.
older=$(find "$d/c" -type f ! -newer "$d/mark" -printf '%s\n' | awk '{ s += $1 } END { print s + 0 }')
if [ "$older" -le "$cap" ]; then ok "evict: entries older than the last build fit the cap ($older bytes)"; else bad "evict: entries older than the last build fit the cap" "$older bytes over cap $cap"; fi
if [ -n "${first_entry:-}" ] && [ ! -e "$d/c/$first_entry" ]; then ok "evict: oldest entry deleted first"; else bad "evict: oldest entry deleted first" "$first_entry still present"; fi
out=$(evict_run build f5.rs -o h5 --timings)
case "$out" in *"cache hit"*) ok "evict: newest entry kept";; *) bad "evict: newest entry kept" "f5 missed";; esac

# ------------------------------------------------------------------ release
d=$(fresh release1)
out=$( (cd "$d" && "$lust" build --release hello.rs -o rel) 2>&1 ); rc=$?
check "release: single file builds" test $rc -eq 0
case "$out" in *"via rustc"*) ok "release: single file names rustc";; *) bad "release: single file names rustc" "output: $out";; esac
check "release: single file runs" test "$("$d/rel")" = "hello 42"
out=$( (cd "$d" && "$lust" check --rustc hello.rs) 2>&1 ); rc=$?
check "check --rustc: valid file passes" test $rc -eq 0
case "$out" in *rustc*) ok "check --rustc: names rustc";; *) bad "check --rustc: names rustc" "output: $out";; esac
printf 'fn main() { let x: i32 = "s"; println!("{}", x); }\n' > "$d/bad.rs"
out=$( (cd "$d" && "$lust" check --rustc bad.rs) 2>&1 ); rc=$?
if [ $rc -ne 0 ]; then ok "check --rustc: bad file fails"; else bad "check --rustc: bad file fails" "exit 0"; fi
case "$out" in *E0308*) ok "check --rustc: rustc error text streams through";; *) bad "check --rustc: rustc error text streams through" "output: $out";; esac
# Default lint levels: rustc's deny-by-default MIR lints reject in both rustc paths (a
# metadata-only check or -A unconditional_panic would accept these), and a source allow wins.
printf 'fn main() {\n    let a = [1, 2, 3];\n    println!("{}", a[5]);\n}\n' > "$d/idx.rs"
printf 'fn main() {\n    let x: u8 = 255 + 1;\n    println!("{}", x);\n}\n' > "$d/ovf.rs"
printf '#![allow(unconditional_panic)]\nfn main() {\n    let a = [1, 2, 3];\n    if std::env::args().count() > 5 {\n        println!("{}", a[5]);\n    }\n    println!("ok");\n}\n' > "$d/idx_allow.rs"
out=$( (cd "$d" && "$lust" check --rustc idx.rs) 2>&1 ); rc=$?
if [ $rc -ne 0 ]; then ok "check --rustc: unconditional_panic rejects"; else bad "check --rustc: unconditional_panic rejects" "exit 0"; fi
case "$out" in *unconditional_panic*) ok "check --rustc: names the lint";; *) bad "check --rustc: names the lint" "output: $out";; esac
(cd "$d" && "$lust" check --rustc ovf.rs) >/dev/null 2>&1; rc=$?
if [ $rc -ne 0 ]; then ok "check --rustc: arithmetic_overflow rejects"; else bad "check --rustc: arithmetic_overflow rejects" "exit 0"; fi
(cd "$d" && "$lust" check --rustc idx_allow.rs) >/dev/null 2>&1; rc=$?
check "check --rustc: a source #![allow] is kept" test $rc -eq 0
(cd "$d" && "$lust" build --release idx.rs -o idxrel) >/dev/null 2>&1; rc=$?
if [ $rc -ne 0 ]; then ok "release: unconditional_panic rejects"; else bad "release: unconditional_panic rejects" "exit 0"; fi
(cd "$d" && "$lust" build --release ovf.rs -o ovfrel) >/dev/null 2>&1; rc=$?
if [ $rc -ne 0 ]; then ok "release: arithmetic_overflow rejects (overflow-checks off)"; else bad "release: arithmetic_overflow rejects (overflow-checks off)" "exit 0"; fi
(cd "$d" && "$lust" build --release idx_allow.rs -o allowrel) >/dev/null 2>&1; rc=$?
check "release: a source #![allow] is kept" test $rc -eq 0 -a "$("$d/allowrel" 2>/dev/null)" = "ok"
ls "$d" | grep -q '\.o$' && bad "check --rustc: leaves no object file" "$(ls "$d")" || ok "check --rustc: leaves no object file"
(cd "$d" && "$lust" check --release hello.rs) >/dev/null 2>&1; rc=$?
check "release: --release on check is a usage error" test $rc -eq 2
(cd "$d" && "$lust" build --rustc hello.rs) >/dev/null 2>&1; rc=$?
check "release: --rustc on build is a usage error" test $rc -eq 2

d=$work/cargo; mkdir -p "$d"; cp -r "$root/tests/cargo-proj" "$d/proj"
out=$( (cd "$d/proj" && "$lust" build --release src/main.rs) 2>&1 ); rc=$?
check "cargo: release build passes" test $rc -eq 0
case "$out" in *"via cargo"*) ok "cargo: names cargo";; *) bad "cargo: names cargo" "output: $out";; esac
case "$out" in *"--bin tinyproj"*) ok "cargo: src/main.rs selects the package bin";; *) bad "cargo: src/main.rs selects the package bin" "output: $out";; esac
check "cargo: release binary runs" test "$("$d/proj/target/release/tinyproj")" = "tiny main 42"
if [ -e "$d/proj/target/release/extra" ]; then bad "cargo: other bin not built" "extra exists"; else ok "cargo: other bin not built"; fi
out=$( (cd "$d/proj" && "$lust" build --release src/bin/extra.rs -o "$d/extra") 2>&1 ); rc=$?
check "cargo: src/bin build passes" test $rc -eq 0
case "$out" in *"--bin extra"*) ok "cargo: src/bin/extra.rs selects --bin extra";; *) bad "cargo: src/bin/extra.rs selects --bin extra" "output: $out";; esac
check "cargo: -o copies the artifact" test "$("$d/extra")" = "tiny extra"
out=$( (cd "$d/proj" && "$lust" build --profile fast src/main.rs) 2>&1 ); rc=$?
check "cargo: --profile build passes" test $rc -eq 0
case "$out" in *"--profile fast"*) ok "cargo: --profile name passes through";; *) bad "cargo: --profile name passes through" "output: $out";; esac
check "cargo: profile binary runs" test "$("$d/proj/target/fast/tinyproj")" = "tiny main 42"

# Timeout report (see the shim at the top). Slow retries do not fail; every
# hang does, even when the checks around the hung call happened to pass.
[ -f "$work/timeouts.log" ] && cat "$work/timeouts.log"
[ -f "$work/hangs.log" ] && fail=$((fail + $(wc -l <"$work/hangs.log")))
echo "test-client: $pass passed, $fail failed"
[ $fail -eq 0 ]
