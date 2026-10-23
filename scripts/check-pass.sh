#!/usr/bin/env bash
# Runs `lust check` (no daemon) on every tests/pass file. difftest builds and runs these
# files, so a rejection that only the check path makes (tf-dynlife 13:14:
# std_collections_btree.rs was L0303 under check and fine under run) would pass the gate.
# Usage: scripts/check-pass.sh   (JOBS=n to set the parallelism, default: all cores)
# Last line: "check-pass: N checked, M rejected".
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
out=$(mktemp)
trap 'rm -f "$out"' EXIT
export lust
ls "$root"/tests/pass/*.rs | xargs -P "${JOBS:-$(getconf _NPROCESSORS_ONLN)}" -I{} sh -c '
  e=$(mktemp)
  if ! LUST_NO_DAEMON=1 timeout 60 "$lust" check "$1" >/dev/null 2>"$e"; then
    echo "REJECT $(basename "$1"): $(head -1 "$e" | cut -c1-160)"
  fi
  rm -f "$e"' _ {} > "$out"
n=$(ls "$root"/tests/pass/*.rs | wc -l)
m=$(grep -c '^REJECT' "$out")
cat "$out"
echo "check-pass: $n checked, $m rejected"
[ "$m" = 0 ]
