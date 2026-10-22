#!/usr/bin/env bash
# Crate fixture tests (docs/ARCH.md sections 1.1, 9.2 S6, 9.3 runner table):
# every directory in tests/crates/ is a small Cargo package. Each fixture is
# built by Cargo (the oracle) and by lust from its crate root file, then both
# binaries run and stdout plus exit status must match.
#
# Per-fixture selections live in the fixture's optional fixture.txt, one
# key=value per line (# starts a comment):
#   bin=<name>        bin target to build (default: the package name)
#   root=<path>       crate root file for the lust build (default: src/main.rs)
#   manifest=<path>   manifest for both builds, relative to the fixture
#                     root (default: Cargo.toml). Workspace fixtures name
#                     the bin package's manifest here.
#   features=<a,b>    passed to cargo and to lust as --features
#   dev-config=1      the fixture's [package.metadata.lust] config drives
#                     the lust selection (no feature flags to lust); the
#                     Cargo oracle gets --no-default-features plus
#                     `features=` as the same effective list
#   target=<triple>   passed to cargo and to lust as --target; the value
#                     `host` means the rustc host triple. No line = no flag.
#   args=<words>      program arguments (split on spaces; no quoting)
#   stderr=exact      also compare the program's stderr, with the thread id
#                     of a panic line masked (panic location fixtures; the
#                     package sets panic = "abort" so the exits match)
#   lib=1             check the lib target only: `cargo build --lib` (not
#                     check: metadata skips deny lints like unconditional_panic) and
#                     `lust check <root> --lib` must both accept (or both
#                     reject, with expect=); nothing runs. root= names the
#                     lib root (default src/lib.rs)
#   test=<lib|name>   run tests instead: `cargo test --lib` (or `--test <name>`)
#                     and `lust test <root> --manifest-path .. --lib` (or
#                     `--test <name>`); the sorted `test <name> ... <status>`
#                     lines and the exit status (zero or not) must match.
#                     root= defaults to src/lib.rs or tests/<name>.rs
#   projdir=<name>    the project directory's name in the work dir (default
#                     proj), for paths Cargo percent-encodes in package ids
#                     (a space, `#`, a non-ASCII char)
#   daemon=1          after the cold build, also build twice through a private
#                     daemon (cold, then warm) and compare both programs
#   expect=<L####>    negative fixture: lust must reject with this code.
#                     Cargo must also reject unless the line cargo=pass is
#                     present (valid Rust lust rejects on purpose).
# The lust build names the same crate to the compiler:
#   lust build <root> --manifest-path <Cargo.toml> --bin <bin> [--features ..] [--target ..]
# Lust loads the crate through the Cargo graph and its module files
# (W-RESOLVE), so fixtures are real multi-file crates.
#
# Usage: scripts/test-crates.sh [filter]
#   SANITIZE=1 also builds the lust-generated C with gcc
#   -fsanitize=address,undefined and runs it, as difftest does.
#   CASE_TIMEOUT seconds per lust compile (default 60). A timed-out lust
#   compile retries once at RETRY_CASE_TIMEOUT (default 6x); a finished
#   retry is reported as "slow", a second timeout is a HANG failure
#   (scripts/timeout-lib.sh).
# A missing tests/crates dir or an empty one fails the run; it never skips.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
fixtures=$root/tests/crates
if [ ! -x "$lust" ]; then
  echo "error: $lust not built. Run cargo build --release first."
  exit 2
fi
if [ ! -d "$fixtures" ]; then
  echo "error: fixture dir $fixtures is missing"
  exit 2
fi
if ! command -v timeout >/dev/null; then
  echo "error: timeout command not found (per-case timeout needs it)"
  exit 2
fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
# Cold, cache-free lust builds: daemon routing has its own gate in smoke.py.
export LUST_NO_DAEMON=1
export LUST_DAEMON_SOCKET="$work/no-daemon.sock"
export LUST_NO_CACHE=1
# Fixtures have no dependencies; keep Cargo off the network and out of the repo.
export CARGO_NET_OFFLINE=true
filter=${1:-}
pass=0
fail=0
seen=0
case_timeout=${CASE_TIMEOUT:-60}
# The one timeout rule for lust compiles (lust_cc). Serial here, so the
# retry is alone. Cargo builds and program runs keep their plain timeouts.
# shellcheck source=scripts/timeout-lib.sh
source "$root/scripts/timeout-lib.sh"
# slow_note <case> <step>: a lust_cc needed its retry and finished.
slow_note() { [ "$lust_cc_slow" = 1 ] && echo "slow: $1 $2 timed out at ${case_timeout}s, finished alone at ${retry_timeout}s"; return 0; }

# A panic line names the OS thread id, which differs per run: mask it.
mask_tid() { sed -E -e "s/^thread '([^']*)' \([0-9]+\) /thread '\1' (TID) /" -e '/^timeout: the monitored command dumped core$/d' -e '/: line [0-9]+: +[0-9]+ .* timeout /d' "$1"; }

report() {
  if [ "$1" = ok ]; then pass=$((pass + 1)); echo "ok   $2"; else fail=$((fail + 1)); echo "FAIL $2: $3"; fi
}

host_triple=$(rustc -vV | sed -n 's/^host: //p')

for dir in "$fixtures"/*/; do
  name=$(basename "$dir")
  [[ -n "$filter" && "$name" != *"$filter"* ]] && continue
  seen=$((seen + 1))
  case_dir=$work/$name
  # `projdir=` is read first: the copy goes there.
  projdir=$(sed -n 's/^projdir=//p' "$dir/fixture.txt" 2>/dev/null | head -1)
  proj=$case_dir/${projdir:-proj}
  mkdir -p "$proj"
  cp -r "$dir/." "$proj/"

  # Fixture selections, with the defaults named in the header.
  bin=$(sed -n 's/^name = "\(.*\)"/\1/p' "$proj/Cargo.toml" | head -1)
  manifest=Cargo.toml
  root_file=src/main.rs
  features=""
  dev_config=""
  target=""
  expect=""
  cargo_pass=""
  stderr_mode=""
  lib=""
  test_sel=""
  daemon=""
  prog_args=()
  if [ -f "$proj/fixture.txt" ]; then
    while IFS='=' read -r k v; do
      case "$k" in
        bin) bin=$v ;;
        root) root_file=$v ;;
        manifest) manifest=$v ;;
        features) features=$v ;;
        dev-config) dev_config=$v ;;
        target) target=$v ;;
        expect) expect=$v ;;
        cargo) cargo_pass=$v ;;
        stderr) stderr_mode=$v ;;
        lib) lib=$v ;;
        test) test_sel=$v ;;
        daemon) daemon=$v ;;
        projdir) ;;
        args) # split on spaces by design (see header)
          read -r -a prog_args <<<"$v" ;;
        "" | \#*) ;;
        *) report bad "$name" "unknown fixture.txt key: $k"; continue 2 ;;
      esac
    done <"$proj/fixture.txt"
  fi
  if [ "$target" = host ]; then target=$host_triple; fi
  if [ -n "$lib" ] && ! grep -q '^root=' "$proj/fixture.txt"; then root_file=src/lib.rs; fi

  cargo_args=(build --manifest-path "$proj/$manifest" --bin "$bin")
  lust_args=(build "$proj/$root_file" -o "$case_dir/lust.bin"
    --manifest-path "$proj/$manifest" --bin "$bin")
  if [ -n "$dev_config" ]; then
    cargo_args+=(--no-default-features)
    if [ -n "$features" ]; then
      cargo_args+=(--features "$features")
    fi
  elif [ -n "$features" ]; then
    cargo_args+=(--features "$features")
    lust_args+=(--features "$features")
  fi
  cargo_bin=$case_dir/cargo-target/debug/$bin
  if [ -n "$target" ]; then
    cargo_args+=(--target "$target")
    lust_args+=(--target "$target")
    cargo_bin=$case_dir/cargo-target/$target/debug/$bin
  fi

  if [ -n "$lib" ]; then
    cargo_args=(build --manifest-path "$proj/$manifest" --lib)
    lust_args=(check "$proj/$root_file" --manifest-path "$proj/$manifest" --lib)
  fi

  if [ -n "$test_sel" ]; then
    # A test fixture: the test targets' per-test results, not one program.
    if [ "$test_sel" = lib ]; then sel=(--lib); dflt=src/lib.rs; else sel=(--test "$test_sel"); dflt=tests/$test_sel.rs; fi
    grep -q '^root=' "$proj/fixture.txt" || root_file=$dflt
    feat=()
    [ -n "$features" ] && feat=(--features "$features")
    results() { grep -E '^test .* \.\.\. (ok|FAILED|ignored|TIMEOUT)' "$1" | sed -E 's/ \([0-9.]+ms\)$//' | sort; }
    (cd "$proj" && timeout 120 cargo test --manifest-path "$proj/$manifest" "${sel[@]}" "${feat[@]}" --target-dir "$case_dir/cargo-target" -- --test-threads 1) >"$case_dir/cargo.out" 2>"$case_dir/cargo.err"
    cst=$?
    (cd "$proj" && lust_cc "$lust" test "$proj/$root_file" --manifest-path "$proj/$manifest" "${sel[@]}" "${feat[@]}" --test-threads 1) >"$case_dir/lust.out" 2>"$case_dir/lust.err"
    st=$?
    if is_timeout "$st"; then
      report bad "$name" "HANG lust test timed out alone at ${retry_timeout}s (first at ${case_timeout}s)"
    elif [ "$(results "$case_dir/cargo.out")" != "$(results "$case_dir/lust.out")" ] || [ $((cst == 0)) -ne $((st == 0)) ]; then
      report bad "$name" "results differ (cargo exit $cst, lust exit $st): $(diff <(results "$case_dir/cargo.out") <(results "$case_dir/lust.out") | head -5) $(head -3 "$case_dir/lust.err")"
    elif ! grep -q '^test ' "$case_dir/cargo.out"; then
      report bad "$name" "cargo ran no tests: $(tail -3 "$case_dir/cargo.err")"
    else
      slow_note "$name" "lust test"
      report ok "$name"
    fi
    continue
  fi

  cargo_ok=1
  if ! (cd "$proj" && timeout 60 cargo "${cargo_args[@]}" --target-dir "$case_dir/cargo-target") >"$case_dir/cargo.out" 2>"$case_dir/cargo.err"; then
    cargo_ok=0
  fi
  if [ -n "$expect" ]; then
    # Negative fixture: the oracle outcome is pinned by `cargo=pass`
    # (valid Rust lust rejects) or its absence (both must reject), and
    # lust must reject with exactly the expected code present.
    if [ "$cargo_pass" = pass ] && [ $cargo_ok -eq 0 ]; then
      report bad "$name" "cargo=pass but cargo rejects it: $(tail -3 "$case_dir/cargo.err")"
      continue
    fi
    if [ "$cargo_pass" != pass ] && [ $cargo_ok -eq 1 ]; then
      report bad "$name" "cargo accepts it; add cargo=pass if lust rejects valid Rust on purpose"
      continue
    fi
    lust_cc "$lust" "${lust_args[@]}" >"$case_dir/lust.out" 2>"$case_dir/lust.err"; st=$?
    if is_timeout "$st"; then
      # A timeout is never the expected reject.
      report bad "$name" "HANG lust timed out alone at ${retry_timeout}s (first at ${case_timeout}s), want $expect"
      continue
    fi
    slow_note "$name" "lust"
    if [ "$st" -eq 0 ]; then
      report bad "$name" "lust accepted it, want $expect"
      continue
    fi
    if grep -q "$expect" "$case_dir/lust.err"; then
      report ok "$name"
    else
      report bad "$name" "want $expect, got: $(head -3 "$case_dir/lust.err")"
    fi
    continue
  fi
  if [ -n "$lib" ]; then
    if [ $cargo_ok -eq 0 ]; then
      report bad "$name" "cargo build --lib failed: $(tail -3 "$case_dir/cargo.err")"
    else
      lust_cc "$lust" "${lust_args[@]}" >"$case_dir/lust.out" 2>"$case_dir/lust.err"; st=$?
      if is_timeout "$st"; then
        report bad "$name" "HANG lust check --lib timed out alone at ${retry_timeout}s (first at ${case_timeout}s)"
      elif [ "$st" -ne 0 ]; then
        slow_note "$name" "lust check --lib"
        report bad "$name" "lust check --lib failed: $(head -5 "$case_dir/lust.err")"
      else
        slow_note "$name" "lust check --lib"
        report ok "$name"
      fi
    fi
    continue
  fi
  if [ $cargo_ok -eq 0 ]; then
    report bad "$name" "cargo build failed: $(tail -3 "$case_dir/cargo.err")"
    continue
  fi
  if [ ! -x "$cargo_bin" ]; then
    report bad "$name" "cargo built, but no binary at $cargo_bin"
    continue
  fi
  lust_cc "$lust" "${lust_args[@]}" >"$case_dir/lust.out" 2>"$case_dir/lust.err"; st=$?
  if is_timeout "$st"; then
    report bad "$name" "HANG lust build timed out alone at ${retry_timeout}s (first at ${case_timeout}s)"
    continue
  fi
  slow_note "$name" "lust build"
  if [ "$st" -ne 0 ]; then
    report bad "$name" "lust build failed: $(head -5 "$case_dir/lust.err")"
    continue
  fi

  timeout 30 "$cargo_bin" "${prog_args[@]}" >"$case_dir/cargo.run.out" 2>"$case_dir/cargo.run.err"; cs=$?
  timeout 30 "$case_dir/lust.bin" "${prog_args[@]}" >"$case_dir/lust.run.out" 2>"$case_dir/lust.run.err"; ls_=$?
  if [ $cs -ne $ls_ ]; then
    report bad "$name" "exit status cargo=$cs lust=$ls_"
    continue
  fi
  if ! cmp -s "$case_dir/cargo.run.out" "$case_dir/lust.run.out"; then
    report bad "$name" "stdout differs:"
    diff "$case_dir/cargo.run.out" "$case_dir/lust.run.out" | head -10
    continue
  fi
  if [ "$stderr_mode" = exact ] && ! diff -q <(mask_tid "$case_dir/cargo.run.err") <(mask_tid "$case_dir/lust.run.err") >/dev/null; then
    report bad "$name" "stderr differs:"
    diff <(mask_tid "$case_dir/cargo.run.err") <(mask_tid "$case_dir/lust.run.err") | head -10
    continue
  fi

  if [ "$daemon" = 1 ]; then
    # The same build twice through a private daemon (the client starts it
    # on this socket, inside the project dir; it exits once idle): its
    # cold build, then its warm one, must give the same program.
    dbad=""
    for dpass in cold warm; do
      env -u LUST_NO_DAEMON LUST_DAEMON_SOCKET="$proj/.lust-daemon.sock" LUST_DAEMON_IDLE=20 \
        timeout "$case_timeout" "$lust" "${lust_args[@]}" >"$case_dir/daemon.$dpass.out" 2>"$case_dir/daemon.$dpass.err"; st=$?
      if [ "$st" -ne 0 ]; then
        dbad="daemon $dpass build failed (exit $st): $(head -3 "$case_dir/daemon.$dpass.err")"
        break
      fi
      timeout 30 "$case_dir/lust.bin" "${prog_args[@]}" >"$case_dir/daemon.$dpass.run.out" 2>/dev/null
      if ! cmp -s "$case_dir/cargo.run.out" "$case_dir/daemon.$dpass.run.out"; then
        dbad="daemon $dpass build: stdout differs: $(diff "$case_dir/cargo.run.out" "$case_dir/daemon.$dpass.run.out" | head -4)"
        break
      fi
    done
    if [ -n "$dbad" ]; then
      report bad "$name" "$dbad"
      continue
    fi
  fi

  if [ "${SANITIZE:-0}" = 1 ]; then
    emit=("${lust_args[@]}")
    emit[3]=$case_dir/lust.tmp.bin # the value after -o (lust_args[2])
    lust_cc "$lust" "${emit[@]}" --emit-c "$case_dir/emit" >"$case_dir/emit.out" 2>"$case_dir/emit.err"; st=$?
    if is_timeout "$st"; then
      report bad "$name" "HANG lust --emit-c build timed out alone at ${retry_timeout}s (first at ${case_timeout}s)"
      continue
    fi
    slow_note "$name" "lust --emit-c build"
    if [ "$st" -ne 0 ]; then
      report bad "$name" "lust --emit-c build failed: $(head -3 "$case_dir/emit.err")"
      continue
    fi
    if ! gcc -O1 -w -fno-sanitize-recover=undefined -fsanitize=address,undefined -o "$case_dir/san.bin" "$case_dir"/emit.*.c 2>"$case_dir/san.err"; then
      report bad "$name" "gcc could not build the generated C: $(head -3 "$case_dir/san.err")"
      continue
    fi
    timeout 30 "$case_dir/san.bin" "${prog_args[@]}" >"$case_dir/san.run.out" 2>"$case_dir/san.run.err"; ss=$?
    if grep -qE "[0-9]: runtime error|Sanitizer" "$case_dir/san.run.err"; then
      report bad "$name" "sanitizer: $(grep -m2 -E '[0-9]: runtime error|Sanitizer' "$case_dir/san.run.err")"
      continue
    fi
    if [ $ss -ne $cs ] || ! cmp -s "$case_dir/cargo.run.out" "$case_dir/san.run.out"; then
      report bad "$name" "sanitized build differs (exit $ss vs cargo $cs)"
      continue
    fi
  fi
  report ok "$name"
done

if [ $seen -eq 0 ]; then
  echo "error: no fixtures matched (filter: '${filter}'); a silent skip is not a pass"
  exit 2
fi
echo "test-crates: $pass passed, $fail failed"
[ $fail -eq 0 ]
