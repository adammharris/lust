#!/usr/bin/env bash
# read-cover.sh [SEED] [COUNT]: the read-coverage lane. Runs every daemon scenario and COUNT
# read-gap histories from SEED (scripts/readgap/gen.py) in daemon mode with LUST_CHECK_READS=1:
# each body check then names every table answer it used that no read of its stored set covers
# (src/driver/read_cover.rs). Exit 0 when the runs pass and no access is uncovered; else the
# first uncovered accesses print. LUST_BIN as for the scenario runner.
set -u
seed=${1:-1}
count=${2:-34}
root=$(cd "$(dirname "$0")/.." && pwd)
out=$(mktemp -d "${TMPDIR:-/tmp}/read-cover-XXXXXX")
trap 'rm -rf "$out"' EXIT
python3 "$root/scripts/readgap/gen.py" --seed "$seed" --count "$count" --out "$out/gen" >/dev/null || exit 2
log=$out/uncovered.log
rc=0
export LUST_CHECK_READS=1 LUST_READCOVER_LOG=$log
unset DAEMON_SCENARIO_RESTART LUST_RELEASE_C
for set in scenarios readgap; do
    if [ $set = scenarios ]; then
        res=$(python3 "$root/scripts/test-daemon-scenarios.py" 2>&1)
    else
        res=$(python3 "$root/scripts/test-daemon-scenarios.py" "$out"/gen/* 2>&1)
    fi
    r=$?
    grep -E "^FAIL" <<<"$res" | sed "s/^/read-cover $set: /"
    echo "read-cover $set: $(tail -1 <<<"$res")"
    [ $r = 0 ] || rc=1
done
n=$( [ -f "$log" ] && grep -c '^readcover:' "$log" || echo 0)
echo "read-cover: $n uncovered accesses"
if [ "$n" != 0 ]; then
    sort "$log" | uniq -c | sort -rn | head -20
    rc=1
fi
exit $rc
