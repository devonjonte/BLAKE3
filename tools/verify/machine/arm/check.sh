#!/bin/sh
# The NEON `hex` kernel against Google DeepMind's AArch64 model (github.com/google-deepmind/code-verification,
# arm64-semantics, unchanged, at the commit lakefile.toml names):
#   1. the kernel is assembled for AArch64 ELF and its 32 instruction words are compared with the words the
#      Lean files name (so the theorem is about this file's code);
#   2. Lean builds their model and proof library (minutes), runs the words on 320 hashes in their semantics
#      (HexNeonRun.lean) and checks the theorems: the contract (HexNeonProof.lean, HexNeonBytes.lean) and
#      that nothing seen depends on the hash (HexNeonQuiet.lean, written by gen_quiet.py);
#   3. the audit of the last: code that shows the hash, or a weaker statement, must be refused.
# Needs cc (clang, or gcc on AArch64 Linux), llvm-objdump (OBJDUMP), lake.
set -eu
here=$(cd "$(dirname "$0")" && pwd); cd "$here"
OBJDUMP=${OBJDUMP:-llvm-objdump}
CC=${CC:-cc}; command -v clang > /dev/null 2>&1 && CC=clang
if "$CC" -target aarch64-unknown-linux-gnu -c -o hex_neon.o hex_neon.S 2>/dev/null; then :; else "$CC" -c -o hex_neon.o hex_neon.S; fi
words=$("$OBJDUMP" -d hex_neon.o | awk '/<_?b3l_hex_neon>:/{on=1;next} on && NF>=2 {print $2}' | tr '\n' ' ' | sed 's/ $//')
[ "$(echo "$words" | wc -w | tr -d ' ')" = 32 ] || { echo "the object does not hold 32 instructions: NOT checked"; exit 1; }
grep -q -F "\"$words\"" HexNeonProof.lean || { echo "the object's words are not the theorem's: NOT checked"; exit 1; }
for w in $words; do grep -q "0x$w" HexNeonQuiet.lean || { echo "the object's word $w is not among the words run: NOT checked"; exit 1; }; done
python3 gen_quiet.py HexNeonQuiet.again.lean && cmp -s HexNeonQuiet.lean HexNeonQuiet.again.lean || { echo "HexNeonQuiet.lean is not what gen_quiet.py writes: NOT checked"; exit 1; }
rm -f HexNeonQuiet.again.lean
if lake build > build.log 2>&1 && ! grep -q -E "error|sorry" build.log; then
  grep -E "hashes|axioms|Build completed" -A3 build.log | head -n 20
else
  grep -E "error|sorry" -A5 build.log | head -n 20
  echo "the NEON hex kernel on Google's AArch64 model: NOT checked"; exit 1
fi
grep -q "(320, 320)" build.log || { echo "the 320 hashes did not all give the hexadecimal: NOT checked"; exit 1; }
grep -q "(some 36, true)" build.log || { echo "the observer did not see 36 things, the same on two hashes: NOT checked"; exit 1; }
[ "${MUTANTS:-1}" = 0 ] || python3 mutants_quiet.py
echo "the NEON hex kernel on Google's AArch64 model: checked"
