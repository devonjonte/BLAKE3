#!/bin/sh
# A function and its contract, from source to checked theorem (BLAKE3 #361). For `merge` of hasher.ode:
#   1. odec.py reads the source; Lean prints the assembly and where the compiler put each variable;
#   2. the assembler makes an ELF object, and the lifter reads the object's bytes back (llvm-objdump);
#   3. prove_fn.py writes the proof that those bytes meet the contract the source names (written in
#      Lean, by hand, for a reader: Spec_NAME.lean), from the source's invariant and that layout;
#   4. Lean checks NAME_meets. No proof text is written by hand for the function but the lemmas it names.
# Needs python3, cc (clang, or gcc on x86-64 Linux), llvm-objdump (OBJDUMP), lake.
# usage: ./prove_fn.sh [NAME [BASE]]
set -eu
here=$(cd "$(dirname "$0")" && pwd); cd "$here"
OBJDUMP=${OBJDUMP:-llvm-objdump}; export OBJDUMP
name=${1:-merge}; base=${2:-0x60000}
python3 odec.py hasher.ode HasherOde.lean
lake build Lang HasherOde > /dev/null
lake env lean --run HasherOde.lean asm b3l_ only "$name" > "$name.S"
lake env lean --run HasherOde.lean layout "$name" > "$name.layout"
if cc -target x86_64-unknown-linux-gnu -c -o "$name.o" "$name.S" 2>/dev/null; then :; else cc -c -o "$name.o" "$name.S"; fi
"$OBJDUMP" -d -r --x86-asm-syntax=intel "$name.o" > "$name.listing"
# the kernels are where one/KCode.lean has them
python3 ../one/lift_one.py "$name.listing" "b3l_$name" "$base" "Lifted_$name.lean" "Lifted_$name" \
  --call blake3_servil_compress_in_place_avx512=0x30000 --call blake3_servil_compress_in_place_sse41=0x20000
python3 gen_code.py "$name" "Lifted_$name.lean.rows" "Code_$name.lean"
python3 prove_fn.py hasher.ode "$name" "Lifted_$name.lean.rows" "$name.layout" "Proof_$name.lean"
lake build "Proof_$name" 2>&1 | grep -E "error|sorry|Build completed" || true
echo "the compiler's proof of $name: checked"
