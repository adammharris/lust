#!/usr/bin/env bash
# llbuild.sh <prefix> <out>: builds the units `lust build --emit-c <prefix>` wrote with the
# LLVM backend (LUST_RELEASE_C=1 LUST_RELEASE_BACKEND=llvm, src/cgen/ll.rs) into <out>, the
# way src/cc.rs does: a unit with `.ll` and `.hc` companions compiles as one module (its C and
# its helpers' C to bitcode, then the IR with both linked in, the helpers internalized), every
# other unit as plain C, the C++
# unwind unit with clang++, and clang++ links. Env: CC (default clang), CXX (clang++),
# OPT (default -O2), LLOBJ (an object cache dir keyed by the unit texts), JOBS (nproc).
set -euo pipefail
prefix=$1 out=$2
CC=${CC:-clang} CXX=${CXX:-clang++} OPT=${OPT:--O2}
F="-std=gnu11 -w -fsigned-char -fno-strict-aliasing -fwrapv -fexceptions -fno-asynchronous-unwind-tables"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
one() { # one <unit .c file>: its object path on stdout
  local c=$1 ll=${1%.c}.ll hc=${1%.c}.hc key o
  if [ -f "$ll" ]; then key=$(cat "$c" "$ll" "$hc" | sha256sum | cut -c1-40); else key=$(sha256sum < "$c" | cut -c1-40); fi
  key=$key-$(echo "$CC $OPT" | sha256sum | cut -c1-8)
  o=${LLOBJ:-$work}/$key.o
  if [ ! -f "$o" ]; then
    if [ -f "$ll" ] && head -c 64 "$c" | grep -q "^/\* lust: LLVM unit body \*/"; then
      # The C half is only its body (cgen::ll::BODY_MARK): one C file, the helpers' C then the
      # body, and the IR keeps the body's fns external through llvm.used (src/cc.rs compile_pair).
      python3 -I - "$c" "$ll" "$hc" "$work/$key.$$" <<'EOF' || return 1
import re, sys
c, ll, hc, out = sys.argv[1:]
body = open(c).read().split("/* lust: LLVM unit body */\n", 1)[1]
ir = open(ll).read()
names = re.findall(r"^(?!static\b|inline\b)[A-Za-z_][^;{}\n]*?\b([A-Za-z_]\w*)\([^;{}]*\)\s*\{", body, re.M)
used = "".join(f"declare void @{n}()\n" for n in names if f"@{n}(" not in ir)
if names:
    used += '@llvm.used = appending global [%d x ptr] [%s], section "llvm.metadata"\n' % (len(names), ", ".join(f"ptr @{n}" for n in names))
open(out + ".ll", "w").write(ir + "\n" + used)
open(out + ".hc.c", "w").write(open(hc).read() + "\n" + body)
EOF
      $CC $OPT $F -emit-llvm -Xclang -disable-llvm-passes -Xclang -no-enable-noundef-analysis -x c -c "$work/$key.$$.hc.c" -o "$work/$key.$$.h.bc"
      $CC $OPT -w -fexceptions -c "$work/$key.$$.ll" -Xclang -mlink-builtin-bitcode -Xclang "$work/$key.$$.h.bc" -o "$o.$$.tmp"
    elif [ -f "$ll" ]; then
      $CC $OPT $F -emit-llvm -Xclang -disable-llvm-passes -Xclang -no-enable-noundef-analysis -c "$c" -o "$work/$key.$$.c.bc"
      $CC $OPT $F -emit-llvm -Xclang -disable-llvm-passes -Xclang -no-enable-noundef-analysis -x c -c "$hc" -o "$work/$key.$$.h.bc"
      $CC $OPT -w -fexceptions -c "$ll" -Xclang -mlink-bitcode-file -Xclang "$work/$key.$$.c.bc" \
        -Xclang -mlink-builtin-bitcode -Xclang "$work/$key.$$.h.bc" -o "$o.$$.tmp"
    else
      $CC $OPT $F -c "$c" -o "$o.$$.tmp"
    fi
    mv -f "$o.$$.tmp" "$o"
  fi
  echo "$o"
}
export -f one
export CC OPT F work LLOBJ
mkdir -p "${LLOBJ:-$work}"
ls "$prefix".u*.c | xargs -P "${JOBS:-$(getconf _NPROCESSORS_ONLN)}" -I{} bash -c 'one "$@"' _ {} > "$work/objs" || { echo "llbuild: a unit failed" >&2; exit 1; }
objs=$(cat "$work/objs")
if [ -f "$prefix.eh.cc" ]; then
  $CXX -O2 -w -fexceptions -c "$prefix.eh.cc" -o "$work/eh.o"
  objs="$objs $work/eh.o"
fi
# shellcheck disable=SC2086
$CXX -o "$out" $objs -lm -lpthread
