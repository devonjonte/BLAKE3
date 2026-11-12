#!/bin/sh
# The compiler proves its AArch64 assembly (BLAKE3 #361), on Google DeepMind's model
# (github.com/google-deepmind/code-verification, arm64-semantics, unchanged, at the commit lakefile.toml
# names). For the kernel `hex_neon` of ../lang/hasher.ode:
#   1. odec.py prints the kernel's assembly from the source; it must be the file kept here (NAME.S);
#   2. the assembler makes an ELF object; its instruction words are read back (llvm-objdump);
#   3. gen_arm.py asks their decoder what each word is and writes Quiet_NAME.lean and Proof_NAME.lean
#      from the words and the source's contract clauses; they must be the files kept here;
#   4. Lean builds their model and proof library (minutes) and checks: the words run on 320 hashes in
#      their semantics (HexNeonRun.lean); NAME_quiet and NAME_observed (what an observer sees);
#      NAME_ok (the kernel's own contract); hex_neon_bytes_ok (the reader's contract, in bytes).
# Then the audit: code that shows the hash, or a weaker statement, must be refused.
# Needs python3, clang (or cc on AArch64), llvm-objdump (OBJDUMP), lake.
set -eu
here=$(cd "$(dirname "$0")" && pwd); cd "$here"
OBJDUMP=${OBJDUMP:-llvm-objdump}
name=${1:-hex_neon}
fail() { echo "$1"; echo "the compiler's proof of $name on Google's AArch64 model: NOT checked"; exit 1; }
python3 ../lang/odec.py ../lang/hasher.ode aarch64 "$name" > "$name.printed.S"
cmp -s "$name.S" "$name.printed.S" || fail "$name.S is not what the source prints"
rm -f "$name.printed.S"
CC=${CC:-cc}; command -v clang > /dev/null 2>&1 && CC=clang
if "$CC" -target aarch64-unknown-linux-gnu -c -o "$name.o" "$name.S" 2>/dev/null; then :; else "$CC" -c -o "$name.o" "$name.S"; fi
"$OBJDUMP" -d "$name.o" | awk "/<_?b3l_$name>:/{on=1;next} on && NF>=2 {print \$2}" | tr '\n' ' ' > "$name.words"
[ "$(wc -w < "$name.words" | tr -d ' ')" -gt 0 ] || fail "the object holds no instructions of $name"
lake build Observer > build.log 2>&1 || { tail -n 5 build.log; fail "their model does not build"; }
mkdir -p again
python3 gen_arm.py ../lang/hasher.ode "$name" "$name.words" again || fail "the generator stopped"
for f in "Quiet_$name.lean" "Proof_$name.lean"; do cmp -s "$f" "again/$f" || fail "$f is not what the compiler writes"; done
rm -rf again
if lake build > build.log 2>&1 && ! grep -q -E "error|sorry" build.log; then
  grep -E "axioms|Build completed" -A3 build.log | head -n 30
else
  grep -E "error|sorry" -A5 build.log | head -n 20
  fail "Lean does not accept the proofs"
fi
grep -q "(320, 320)" build.log || fail "the 320 hashes did not all give the hexadecimal"
grep -q "(some 36, true)" build.log || fail "the observer did not see 36 things, the same on two hashes"
grep -q "'hex_neon_meets' depends on axioms" build.log || fail "hex_neon_meets (the contract that names no machine) was not checked"
[ "${MUTANTS:-1}" = 0 ] || python3 mutants_quiet.py "$name" || fail "the audit accepted a change"
echo "the compiler's proof of $name on Google's AArch64 model: checked"
