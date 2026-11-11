#!/bin/sh
# Cross-check kernel512/Simd.lean against this machine's CPU (AVX-512 F and VL needed): the Lean
# model writes test vectors for every instruction of the two one-block kernels, and cross.c runs
# the same bytes. Then a control: a model with PSHUFD's second selector read from the wrong bits
# must be found to differ.
set -eu
here=$(cd "$(dirname "$0")" && pwd); work=${CROSS_WORK:-$(mktemp -d)}; mkdir -p "$work"
cd "$here"
lake build Simd Code CodeSse >/dev/null
lake env lean --run Cross.lean > "$work/vectors.txt"
cc -O1 -o "$work/cross" cross.c
"$work/cross" "$work/vectors.txt"
rm -rf "$work/wrong"; mkdir -p "$work/wrong"; cp Simd.lean Code.lean CodeSse.lean Cross.lean lakefile.toml lean-toolchain "$work/wrong/"
python3 - "$work/wrong/Simd.lean" <<'PY'
import sys
p = sys.argv[1]; t = open(p).read()
old = "  mk4 (dw y (imm % 4)) (dw y (imm / 4 % 4)) (dw y (imm / 16 % 4)) (dw y (imm / 64 % 4))\n/-- SHUFPS"
new = "  mk4 (dw y (imm % 4)) (dw y (imm / 16 % 4)) (dw y (imm / 16 % 4)) (dw y (imm / 64 % 4))\n/-- SHUFPS"
assert t.count(old) == 1
with open(p, "w") as f: f.write(t.replace(old, new))
PY
python3 - "$work/wrong/lakefile.toml" "$here" <<'PY'
import sys
p, here = sys.argv[1:3]; t = open(p).read()
with open(p, "w") as f: f.write(t.replace('path = "../../lean"', f'path = "{here}/../../lean"'))
PY
(cd "$work/wrong" && lake build Simd Code CodeSse > "$work/wrong-build.log" 2>&1 || { tail -n 20 "$work/wrong-build.log"; exit 1; })
(cd "$work/wrong" && lake env lean --run Cross.lean > "$work/wrong-vectors.txt")
if "$work/cross" "$work/wrong-vectors.txt" > "$work/wrong.out"; then echo "the control passed: a wrong PSHUFD was not noticed"; exit 1; fi
tail -n 1 "$work/wrong.out" | sed 's/^/control (a wrong PSHUFD): /'
echo "cross-check done"
