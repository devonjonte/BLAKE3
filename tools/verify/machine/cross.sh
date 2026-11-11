#!/bin/sh
# Cross-check this folder's X86.lean (the model under the detection theorem) against this machine's
# CPU: the Lean model writes test vectors for every instruction of the proved program and of three
# other builds of it (other-compilers/), and hex/cross.c runs the same bytes on the processor. Then a
# control: a model in which a 32-bit write keeps the register's upper half must be found to differ.
# Not here: CPUID and XGETBV (what they return is the theorem's Cpu), jumps, calls, returns, push, pop.
# Linux, x86-64.
set -eu
here=$(cd "$(dirname "$0")" && pwd); work=${CROSS_WORK:-$(mktemp -d)}; mkdir -p "$work"
cd "$here"
lake build X86 CrossTable >/dev/null
lake env lean --run Cross.lean 40 > "$work/vectors.txt"
cc -O1 -o "$work/cross" hex/cross.c
"$work/cross" "$work/vectors.txt"
rm -rf "$work/wrong"; mkdir -p "$work/wrong"; cp Attr.lean X86.lean CrossTable.lean Cross.lean lean-toolchain "$work/wrong/"
printf 'name = "wrong"\n[[lean_lib]]\nname = "Attr"\n[[lean_lib]]\nname = "X86"\n[[lean_lib]]\nname = "CrossTable"\n' > "$work/wrong/lakefile.toml"
python3 wrong_model.py "$work/wrong/X86.lean"
(cd "$work/wrong" && lake build X86 CrossTable > "$work/wrong-build.log" 2>&1 || { tail -n 20 "$work/wrong-build.log"; exit 1; })
(cd "$work/wrong" && lake env lean --run Cross.lean 40 > "$work/wrong-vectors.txt")
if "$work/cross" "$work/wrong-vectors.txt" > "$work/wrong.out"; then echo "the control passed: a wrong 32-bit write was not noticed"; exit 1; fi
tail -n 1 "$work/wrong.out" | sed 's/^/control (a 32-bit write that keeps the upper half): /'
echo "cross-check done"
