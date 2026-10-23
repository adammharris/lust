#!/usr/bin/env bash
# Release builds through a front image must equal one-shot release builds: units byte for byte
# and the binaries' output, release C and LLVM, on a small layout-sensitive corpus plus the dt01
# shape (scripts/front_check.py). About 30-60 s on 16 cores. Run after scripts/build.sh.
# Exit 0 = all same, 1 = a difference or a one-sided build failure, 2 = setup error.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
python3 "$root/scripts/front_check.py" --jobs "${GATE_JOBS:-$(getconf _NPROCESSORS_ONLN)}" "$@"
