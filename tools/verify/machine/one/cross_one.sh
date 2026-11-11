#!/bin/sh
# Cross-check one/Machine.lean (the model under the kernels', the parent functions' and merge's
# theorems) against this machine's CPU: the Lean model writes test vectors for every instruction of
# those programs, and cross_one.c runs the same bytes on the processor. Then a control: a model in
# which a 32-bit write keeps the register's upper half must be found to differ.
# Linux, x86-64 with AVX-512 F and VL.
set -eu
here=$(cd "$(dirname "$0")" && pwd); work=${CROSS_WORK:-$(mktemp -d)}; mkdir -p "$work"
cd "$here"
lake build Machine CrossOneTable >/dev/null
lake env lean --run CrossOne.lean 40 > "$work/vectors.txt"
cc -O1 -o "$work/cross_one" cross_one.c
"$work/cross_one" "$work/vectors.txt"
rm -rf "$work/wrong"; mkdir -p "$work/wrong"; cp Machine.lean CrossOneTable.lean CrossOne.lean lean-toolchain "$work/wrong/"
printf 'name = "wrong"\n[[lean_lib]]\nname = "Machine"\n[[lean_lib]]\nname = "CrossOneTable"\n' > "$work/wrong/lakefile.toml"
python3 wrong_model.py "$work/wrong/Machine.lean"
(cd "$work/wrong" && lake build Machine CrossOneTable > "$work/wrong-build.log" 2>&1 || { tail -n 20 "$work/wrong-build.log"; exit 1; })
(cd "$work/wrong" && lake env lean --run CrossOne.lean 40 > "$work/wrong-vectors.txt")
if "$work/cross_one" "$work/wrong-vectors.txt" > "$work/wrong.out"; then echo "the control passed: a wrong 32-bit write was not noticed"; exit 1; fi
tail -n 1 "$work/wrong.out" | sed 's/^/control (a 32-bit write that keeps the upper half): /'
echo "cross-check done"
