# case-pool.sh: the parallel case runner and the rustc result cache that scripts/difftest.sh
# and scripts/runtest.sh share. Source it after setting $root, $work (the run's temp dir),
# and $filter. Each case runs in its own dir; see run_all.
#   DIFFTEST_JOBS        cases at the same time (default nproc).
#   DIFFTEST_RUSTC_CACHE rustc result cache dir (default ~/.cache/lust-difftest; "off" turns
#                        it off, as the landing gate does). Only rustc's side is cached, never
#                        lust's.
#   CASE_TIMEOUT seconds per compile (default 30), RUN_TIMEOUT per run (default 10).
#   RETRY_CASE_TIMEOUT seconds for the solo rerun of a case whose lust compile timed
#                        out (default 6x CASE_TIMEOUT; see run_lust and run_all).
#   DIFFTEST_SHARD       <k>/<n>: run only the matching cases whose index i (0-based, in run_all
#                        order) has i % n == k. The n shards together run every case once; the
#                        landing gate runs them on separate machines. $matched counts the cases
#                        the filter matched before the shard cut.
case_timeout=${CASE_TIMEOUT:-30}
run_timeout=${RUN_TIMEOUT:-10}
retry_timeout=${RETRY_CASE_TIMEOUT:-$((case_timeout * 6))}
run_cc() { timeout "$case_timeout" "$@"; }
run_to() { timeout "$run_timeout" "$@"; }
# is_timeout <status>: a timeout (124) or a kill after one (137), as in
# scripts/timeout-lib.sh. Other signal deaths are crashes and fail at once.
is_timeout() { [ "$1" = 124 ] || [ "$1" = 137 ]; }
# run_lust <cmd...>: run_cc for lust compiles only. On a timeout it leaves a
# `.lust-timeout` marker file in the case dir; run_all reruns a marked case once,
# alone, at $retry_timeout after the pool drains (a timeout is never a reject:
# the marker is how a parallel case asks for its solo retry). Rustc compiles
# keep plain run_cc: a rustc timeout is the oracle's own result (and a
# "// rustc-timeout: N" fail case needs it to stay one).
run_lust() {
  timeout "$case_timeout" "$@"
  local st=$?
  is_timeout "$st" && : >.lust-timeout
  return "$st"
}
# run_to_err <errfile> <cmd...>: run_to with only the command's own stderr in <errfile>. A plain
# `run_to cmd 2>file` also puts timeout's "dumped core" note and bash's "Aborted" job report
# there when cmd dies by a signal (a panic=abort panic).
run_to_err() { local e=$1; shift; run_to bash -c 'exec "$@" 2>"$0"' "$e" "$@" 2>/dev/null; }
jobs=${DIFFTEST_JOBS:-$(getconf _NPROCESSORS_ONLN)}
rustc_cache=${DIFFTEST_RUSTC_CACHE:-$HOME/.cache/lust-difftest}
[ "$rustc_cache" = off ] || mkdir -p "$rustc_cache" || rustc_cache=off
rustc_version=$(rustc -vV 2>&1)
# For the rustc cache key, per fixture dir:
#   dep_hash[dir]: every file under the dir (subdirs too) except the dir's own .rs cases:
#                  include!/include_str! data and module files in subdirs.
#   sib_hash[dir]: the dir's own .rs cases. Only in the key of a case that names other files
#                  (`mod x;`, `#[path`, `include!`), because it may read a sibling case.
declare -A dep_hash sib_hash
for d in "$root"/tests/{pass,fail,reject,unwind,release}; do
  [ -d "$d" ] || continue
  dep_hash[$d]=$(cd "$d" && find . -type f ! -regex '\./[^/]*\.rs' -print0 | sort -z | xargs -0 -r sha256sum | sha256sum)
  sib_hash[$d]=$(cd "$d" && find . -maxdepth 1 -type f -name '*.rs' -print0 | sort -z | xargs -0 -r sha256sum | sha256sum)
done
shard_k=0
shard_n=1
if [ -n "${DIFFTEST_SHARD:-}" ]; then
  if [[ ! "$DIFFTEST_SHARD" =~ ^([0-9]+)/([1-9][0-9]*)$ ]] || [ "${BASH_REMATCH[1]}" -ge "${BASH_REMATCH[2]}" ]; then
    echo "FAIL: DIFFTEST_SHARD must be <k>/<n> with k < n, not '$DIFFTEST_SHARD'"
    exit 1
  fi
  shard_k=${BASH_REMATCH[1]} shard_n=${BASH_REMATCH[2]}
fi
pass=0
fail=0
seen=0
matched=0
unsupported=0

# mask_stderr <file>: a program's stderr without what differs per run: the OS thread id in
# Rust's `thread '..' (<tid>)` lines, `timeout`'s note on a dumped core, and bash's job
# note on a signal death ("line 54: <pid> Aborted  timeout ..."), which lands in the
# redirected stderr of a function call. A std source path in a panic location is
# `@STD@/library/..`: boat's rustc prints `/rustc/<hash>/library/..`, a toolchain with
# rust-src installed prints its local `lib/rustlib/src/rust/library/..`. W-PANIC compares
# the rest byte for byte.
mask_stderr() { sed -E -e "s/^thread '([^']*)' \([0-9]+\) /thread '\1' (TID) /" -e 's#(/rustc/[0-9a-f]+|/[^ :]*/lib/rustlib/src/rust)/library/#@STD@/library/#g' -e '/^timeout: the monitored command dumped core$/d' -e '/: line [0-9]+: +[0-9]+ .* timeout /d' "$1"; }

# mask_stdout <case file> <stdout file>: a program's stdout with the paths it can print
# masked: the case's path as @CASE@ and the checkout root as @ROOT@ (`file!()`,
# `Location::file()`, a panic location formatted and printed). rustc_oracle stores the
# oracle's stdout masked this way, so one cache serves every checkout root: an unmasked
# cached stdout holds the filling job's root and fails a job in another root on a pooled
# boat box (tests/unwind/hooks.rs, rel-opt 05:21). Every stdout compare masks both sides.
mask_stdout() { sed -e "s|$1|@CASE@|g" -e "s|$root|@ROOT@|g" "$2"; }

# report ok|bad <name> [msg]: a case's result. Runs inside the case's subshell, in its dir.
report() {
  echo "$1" >st
  [ "$1" = ok ] || echo "FAIL $2: $3"
}

# rustc_oracle build|run <file> <rustc flags...>: runs rustc on <file> in the case dir and
# writes rustc.cc (exit status) and rustc.err (stderr); in run mode, when the build passes,
# it also runs the program with the args in $oracle_args (if set) and writes rustc.out
# (stdout) and rustc.rs (exit status). Results come from $rustc_cache when the key
# matches: a hash of the rustc version, the mode, the flags, the args, the case's name and
# bytes, and the files it can read (dep_hash, sib_hash). A timeout is never cached, and
# neither is a case that reads the environment (env!, option_env!, std::env::var): its
# result depends on more than its files.
rustc_oracle() {
  local mode=$1 f=$2; shift 2
  local key="" entry="" cc rs=0 tmp d
  local args=("${oracle_args[@]}")
  if [ "$rustc_cache" != off ] && ! grep -qE 'env!|env::(var|vars|var_os|vars_os|current_dir|temp_dir|home_dir)\b' "$f"; then
    d=$(dirname "$f")
    key=$({
      # v3: rustc.out is stored masked with mask_stdout (older entries hold a raw root).
      printf 'v3\n%s\n%s\n%s\n%s\n%s\n' "$rustc_version" "$mode" "$*" "${args[*]}" "$(basename "$f")"
      # file!() and panic locations print the path; key those cases on the full path too
      # (defense in depth next to the stdout mask, which is the root fix).
      grep -qE 'file!|[Ll]ocation' "$f" && echo "$f"
      cat "$f"
      echo "${dep_hash[$d]:-}"
      grep -qE '^\s*(pub(\([^)]*\))?\s+)?mod\s+\w+\s*;|#\[path|include(_str|_bytes)?!' "$f" && echo "${sib_hash[$d]:-}"
    } | sha256sum | cut -c1-40)
    entry=$rustc_cache/$key
    if [ -f "$entry/rustc.cc" ]; then
      cp "$entry"/rustc.* .
      return
    fi
  fi
  # A case may lower rustc's compile limit with a "// rustc-timeout: N" line, for a fail case
  # whose rustc rejection is a hang (a timeout counts as a reject and is never cached).
  local ct; ct=$(sed -n 's|^// rustc-timeout: *\([0-9][0-9]*\).*|\1|p' "$f" | head -1)
  case_timeout=${ct:-$case_timeout} run_cc rustc "$@" -o rustc.bin "$f" 2>rustc.err; cc=$?
  echo $cc >rustc.cc
  if [ "$mode" = run ] && [ $cc -eq 0 ]; then
    # stderr (panic text and location) and stdout (paths a program prints) are kept
    # masked (mask_stdout), so a cached result serves any checkout.
    run_to ./rustc.bin "${args[@]}" >rustc.out 2>rustc.stderr; rs=$?
    echo $rs >rustc.rs
    # Through a temp file, not `sed -i`: BSD sed (macOS) reads -i's next word as a suffix.
    sed "s|$f|@CASE@|g" rustc.stderr >rustc.stderr.tmp && mv rustc.stderr.tmp rustc.stderr
    sed -e "s|$f|@CASE@|g" -e "s|$root|@ROOT@|g" rustc.out >rustc.out.tmp && mv rustc.out.tmp rustc.out
  fi
  [ -n "$entry" ] && [ $cc -ne 124 ] && [ $cc -ne 137 ] && [ $rs -ne 124 ] && [ $rs -ne 137 ] || return 0
  tmp=$(mktemp -d "$rustc_cache/.tmp.XXXXXX") || return 0
  cp rustc.cc rustc.err "$tmp"/ && { [ ! -f rustc.out ] || cp rustc.out rustc.rs rustc.stderr "$tmp"/; } \
    && mv -T "$tmp" "$entry" 2>/dev/null || rm -rf "$tmp"
}

# run_all <case fn> <file...>: runs `<case fn> <name> <file>` for each file whose name
# matches $filter (and is in this DIFFTEST_SHARD), $jobs at a time. Case i runs in $work/c/i (its cwd, lust cache dir, and
# daemon socket path), with its report in c/i/st and its output in c/i/log. A case whose
# lust compile timed out (run_lust left a `.lust-timeout` marker) then reruns once, alone, at
# $retry_timeout, and the rerun's result is the case's result: a finished rerun is
# reported as "slow", a second timeout is a HANG and fails. Then prints every log in
# case order, so the output does not depend on the job count, and adds to pass, fail,
# unsupported, and seen.
run_all() {
  local fn=$1; shift
  # tidy: once a case's status is ok or unsupported (and no solo rerun is due), its build
  # files go and only its log and status stay (a full release difftest kept ~5 MB a case, 12 GB
  # of the shared /tmp). A failing case keeps everything.
  tidy() {
    case "$(cat st 2>/dev/null)" in
      ok | unsupported) [ -f .lust-timeout ] || find . -mindepth 1 -maxdepth 1 ! -name log ! -name log.retry ! -name st -exec rm -rf {} + ;;
    esac
  }
  local f name i=0 m=0 running=0 st
  local names=() files=()
  rm -rf "$work/c"
  for f in "$@"; do
    name=$(basename "$f" .rs)
    [[ "$f" == */unwind/* ]] && name="unwind-$name"
    [[ "$f" == */release/* ]] && name="release-$name"
    [[ -n "$filter" && "$name" != *"$filter"* ]] && continue
    m=$((m + 1))
    (( (m - 1) % shard_n == shard_k )) || continue
    if [ $running -ge "$jobs" ]; then wait -n; running=$((running - 1)); fi
    mkdir -p "$work/c/$i"
    (
      cd "$work/c/$i" || exit 1
      export LUST_DAEMON_SOCKET=$PWD/no-daemon.sock LUST_CACHE_DIR=$PWD/cache
      "$fn" "$name" "$f"
      tidy
    ) >"$work/c/$i/log" 2>&1 &
    names+=("$name"); files+=("$f"); i=$((i + 1)); running=$((running + 1))
  done
  wait
  # Solo reruns of timed-out cases, in case order, before any result is read.
  for i in "${!names[@]}"; do
    [ -f "$work/c/$i/.lust-timeout" ] || continue
    rm -f "$work/c/$i/.lust-timeout" "$work/c/$i/st"
    (
      cd "$work/c/$i" || exit 1
      export LUST_DAEMON_SOCKET=$PWD/no-daemon.sock LUST_CACHE_DIR=$PWD/cache
      case_timeout=$retry_timeout
      "$fn" "${names[$i]}" "${files[$i]}"
      tidy
    ) >"$work/c/$i/log.retry" 2>&1
    if [ -f "$work/c/$i/.lust-timeout" ]; then
      echo "FAIL ${names[$i]}: HANG lust timed out alone at ${retry_timeout}s (first at ${case_timeout}s under load)" >"$work/c/$i/log"
      echo bad >"$work/c/$i/st"
    else
      { echo "slow: ${names[$i]} lust timed out at ${case_timeout}s under load, finished alone at ${retry_timeout}s"
        cat "$work/c/$i/log.retry"; } >"$work/c/$i/log"
    fi
    rm -f "$work/c/$i/log.retry" "$work/c/$i/.lust-timeout"
  done
  for i in "${!names[@]}"; do
    cat "$work/c/$i/log"
    st=$(cat "$work/c/$i/st" 2>/dev/null)
    case "$st" in
      ok) pass=$((pass + 1)) ;;
      unsupported) unsupported=$((unsupported + 1)) ;;
      bad) fail=$((fail + 1)) ;;
      *) fail=$((fail + 1)); echo "FAIL ${names[$i]}: the case runner gave no result" ;;
    esac
  done
  seen=$((seen + ${#names[@]}))
  matched=$((matched + m))
}
