#!/usr/bin/env bash
# Determinism gate (Sol's review of COLLECT-OPTIONS.md, 2026-10-19). Two halves:
#   1. scripts/determinism_check.py: fresh one-shot builds of a fixed corpus, release C and LLVM
#      at LUST_THREADS=1, 16, 16 and dev C at 16, 16: complete unit sets (names and bytes),
#      binaries, status and diagnostics equal; plus the order audit (LUST_ORDER_FUZZ: shuffled
#      materialize turn order must not change a release unit; reported, not failed).
#   2. scripts/front_check.py --chains: front-check's edit histories (recovery sequences
#      included) through two independent image chains (1 and 16 threads), each against a fresh
#      one-shot reference, and chain against chain unit for unit.
# Run after scripts/build.sh. Exit 0 = all equal, 1 = a difference, 2 = setup error.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
# --quick (for every land): the one-shot half on a 24-program sample, release C and dev C only,
# no order audit; the image half as in full. The full form is for the release lane.
jobs=${GATE_JOBS:-$(getconf _NPROCESSORS_ONLN)}
t0=$(date +%s)
if [ "${1:-}" = "--quick" ]; then
  shift
  python3 "$root/scripts/determinism_check.py" --jobs "$jobs" --threads 16 --sample 24 "$@"; a=$?
else
  python3 "$root/scripts/determinism_check.py" --jobs "$jobs" --threads 16 --llvm --order-fuzz 1 "$@"; a=$?
fi
python3 "$root/scripts/front_check.py" --jobs "$jobs" --chains; b=$?
echo "determinism-check: one-shot half rc=$a, image half rc=$b, $(( $(date +%s) - t0 )) s"
[ $a -le 1 ] && [ $b -le 1 ] || exit 2
[ $a = 0 ] && [ $b = 0 ]
