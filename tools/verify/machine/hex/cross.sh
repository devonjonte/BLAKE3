#!/bin/sh
# Cross-check hex/X86.lean (the model under the theorems of gen/ and hex/) against this machine's
# CPU: the Lean model writes test vectors for every instruction of the proved programs, and cross.c
# runs the same bytes on the processor. Then a control: a model in which a 32-bit write keeps the
# register's upper half (a classic mistake) must be found to differ. Linux, x86-64.
set -eu
here=$(cd "$(dirname "$0")" && pwd); work=${CROSS_WORK:-$(mktemp -d)}; mkdir -p "$work"
cd "$here"
lake build X86 CrossTable >/dev/null
lake env lean --run Cross.lean 40 > "$work/vectors.txt"
cc -O1 -o "$work/cross" cross.c
"$work/cross" "$work/vectors.txt"
rm -rf "$work/wrong"; mkdir -p "$work/wrong"; cp Bytes.lean Attr.lean X86.lean CrossTable.lean Cross.lean lakefile.toml lean-toolchain "$work/wrong/"
python3 - "$work/wrong/X86.lean" <<'PY'
import sys
p = sys.argv[1]; t = open(p).read()
old = "      | 32 => v &&& 0xFFFFFFFF\n"
new = "      | 32 => (s.get r &&& ~~~(0xFFFFFFFF : BitVec 64)) ||| (v &&& 0xFFFFFFFF)\n"
assert t.count(old) == 1
with open(p, "w") as f: f.write(t.replace(old, new))
PY
(cd "$work/wrong" && lake build X86 CrossTable > "$work/wrong-build.log" 2>&1 || { tail -n 20 "$work/wrong-build.log"; exit 1; })
(cd "$work/wrong" && lake env lean --run Cross.lean 40 > "$work/wrong-vectors.txt")
if "$work/cross" "$work/wrong-vectors.txt" > "$work/wrong.out"; then echo "the control passed: a wrong 32-bit write was not noticed"; exit 1; fi
tail -n 1 "$work/wrong.out" | sed 's/^/control (a 32-bit write that keeps the upper half): /'
echo "cross-check done"
