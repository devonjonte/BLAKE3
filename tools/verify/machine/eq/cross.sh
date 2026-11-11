#!/bin/sh
# Cross-check eq/X86.lean (the model under hash_eq_is_equality) against this machine's CPU: the Lean
# model writes test vectors for every instruction of the comparison, and cross.c runs the same bytes
# on the processor. Then a control: a model whose PMOVMSKB reads each byte's lowest bit, not its
# highest, must be found to differ. Linux, x86-64.
set -eu
here=$(cd "$(dirname "$0")" && pwd); work=${CROSS_WORK:-$(mktemp -d)}; mkdir -p "$work"
cd "$here"
lake build X86 CrossTable >/dev/null
lake env lean --run Cross.lean 200 > "$work/vectors.txt"
cc -O1 -o "$work/cross" cross.c
"$work/cross" "$work/vectors.txt"
rm -rf "$work/wrong"; mkdir -p "$work/wrong"; cp X86.lean CrossTable.lean Cross.lean lean-toolchain "$work/wrong/"
printf 'name = "wrong"\n[[lean_lib]]\nname = "X86"\n[[lean_lib]]\nname = "CrossTable"\n' > "$work/wrong/lakefile.toml"
python3 wrong_model.py "$work/wrong/X86.lean"
(cd "$work/wrong" && lake build X86 CrossTable > "$work/wrong-build.log" 2>&1 || { tail -n 20 "$work/wrong-build.log"; exit 1; })
(cd "$work/wrong" && lake env lean --run Cross.lean 200 > "$work/wrong-vectors.txt")
if "$work/cross" "$work/wrong-vectors.txt" > "$work/wrong.out"; then echo "the control passed: a wrong PMOVMSKB was not noticed"; exit 1; fi
tail -n 1 "$work/wrong.out" | sed 's/^/control (a PMOVMSKB reading the lowest bits): /'
echo "cross-check done"
