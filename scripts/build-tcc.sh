#!/usr/bin/env bash
# Builds the pinned tinycc (mob) into third_party/tcc. The lust build links its libtcc.a.
# The patches in scripts/tcc-patches/ go on top of the pinned commit, in name order.
set -euo pipefail
TCC_COMMIT=43c7708
root=$(cd "$(dirname "$0")/.." && pwd)
src=$root/third_party/tinycc
out=$root/third_party/tcc
if [ ! -d "$src/.git" ]; then
  git clone -q https://github.com/TinyCC/tinycc.git "$src"
fi
git -C "$src" fetch -q --depth 1 origin "$TCC_COMMIT" 2>/dev/null || true
# -f: a tree with the patches from an earlier run goes back to the commit first.
git -C "$src" checkout -q -f "$TCC_COMMIT"
for p in "$root"/scripts/tcc-patches/*.patch; do
  [ -e "$p" ] || continue
  git -C "$src" apply "$p"
done
cd "$src"
./configure --prefix="$out" >/dev/null
make -j"$(getconf _NPROCESSORS_ONLN)" >/dev/null
make install >/dev/null
echo "tcc $TCC_COMMIT (+$(ls "$root"/scripts/tcc-patches/*.patch 2>/dev/null | wc -l | tr -d " ") patches) installed in $out"
