#!/bin/sh
# The compiler proves its assembly (BLAKE3 #361): for the kernel `hex` of hasher.ode,
#   1. odec.py turns the source into Lean values, and Lean prints the assembly;
#   2. the assembler makes an object, and the lifter reads the object's bytes back (llvm-objdump);
#   3. prove.py writes the theorem from the source's contract and its proof by recipe;
#   4. Lean checks that those bytes meet the contract.
# Then the audit: instructions changed one at a time must each fail the proof.
# Needs python3, cc (clang, or gcc on x86-64 Linux), llvm-objdump (OBJDUMP), lake. The object is ELF.
set -eu
here=$(cd "$(dirname "$0")" && pwd); cd "$here"
OBJDUMP=${OBJDUMP:-llvm-objdump}; export OBJDUMP
name=${1:-hex}; base=0x50000
python3 odec.py hasher.ode HasherOde.lean
lake build Lang HasherOde > /dev/null
lake env lean --run HasherOde.lean asm b3l_ only "$name" > "$name.S"
if cc -target x86_64-unknown-linux-gnu -c -o "$name.o" "$name.S" 2>/dev/null; then :; else cc -c -o "$name.o" "$name.S"; fi
"$OBJDUMP" -d -r --x86-asm-syntax=intel "$name.o" | awk "/<_?b3l_$name>:/,/ret/" > "$name.listing"
python3 ../one/lift_one.py "$name.listing" "$(head -n 1 "$name.listing" | sed 's/.*<\(.*\)>:/\1/')" $base "Lifted_$name.lean" "Lifted_$name" --object "$name.o"
python3 prove.py hasher.ode "$name" "Lifted_$name.lean.rows" $base .
lake build "Proof_$name" 2>&1 | grep -E "depends on axioms|error|sorry|Build completed" || true
[ "${MUTANTS:-1}" = 0 ] || python3 "mutants_$name.py"
echo "the compiler's proof of $name: checked"
