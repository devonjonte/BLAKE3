#!/bin/sh
# A word-level function of ../lang/hasher.ode, printed for AArch64 and proved on Google DeepMind's model
# (a trial, for straight-line functions that call nothing): the source function is the one the x86-64 code is
# printed from. For `push`:
#   1. odec.py prints the function's AArch64 assembly; it must be the file kept here (NAME.S);
#   2. the assembler makes an ELF object; its instruction words are read back;
#   3. gen_fn_arm.py writes Proof_NAME_arm.lean from the words and the contract named (PushCells.lean), which
#      must be the file kept here; Lean checks it;
#   4. PushBytes.lean (by hand): the same code meets Push.byteContract (../spec/PushContract.lean), the
#      contract that names no machine, which the x86-64 code meets too (../lang/Meets_push_bytes.lean).
# usage: ./prove_arm_fn.sh [NAME [SPECFILE SPEC]]
set -eu
here=$(cd "$(dirname "$0")" && pwd); cd "$here"
OBJDUMP=${OBJDUMP:-llvm-objdump}
name=${1:-push}; specfile=${2:-PushCells}; spec=${3:-pushCellsSpec}
fail() { echo "$1"; echo "the compiler's proof of $name (AArch64) on Google's model: NOT checked"; exit 1; }
python3 ../lang/odec.py ../lang/hasher.ode aarch64-fn "$name" > "$name.printed.S"
cmp -s "$name.S" "$name.printed.S" || fail "$name.S is not what the source prints"
rm -f "$name.printed.S"
CC=${CC:-cc}; command -v clang > /dev/null 2>&1 && CC=clang
if "$CC" -target aarch64-unknown-linux-gnu -c -o "$name.o" "$name.S" 2>/dev/null; then :; else "$CC" -c -o "$name.o" "$name.S"; fi
"$OBJDUMP" -d "$name.o" | awk "/<_?b3l_$name>:/{on=1;next} on && NF>=2 {print \$2}" | tr '\n' ' ' > "$name.words"
[ "$(wc -w < "$name.words" | tr -d ' ')" -gt 0 ] || fail "the object holds no instructions of $name"
mkdir -p again
python3 gen_fn_arm.py "$name" "$name.words" "$specfile" "$spec" "again/Proof_${name}_arm.lean" > /dev/null || fail "the generator stopped"
cmp -s "Proof_${name}_arm.lean" "again/Proof_${name}_arm.lean" || fail "Proof_${name}_arm.lean is not what the compiler writes"
rm -rf again
if lake build "Proof_${name}_arm" > "build-$name.log" 2>&1 && ! grep -q -E "error|sorry" "build-$name.log"; then
  grep -E "axioms|Build completed" -A1 "build-$name.log" | head -n 6
else
  grep -E "error|sorry" -A5 "build-$name.log" | head -n 20
  fail "Lean does not accept the proof"
fi
echo "the compiler's proof of $name (AArch64) on Google's model: checked"
# The contract that names no machine (../spec), where there is one for this function (by hand, so far).
if [ "$name" = push ]; then
  if lake build PushBytes > "build-$name-bytes.log" 2>&1 && ! grep -q -E "error|sorry" "build-$name-bytes.log"; then
    grep -E "push_arm_meets. depends" -A1 "build-$name-bytes.log" | head -n 3
    echo "push (AArch64) meets Push.byteContract, the contract the x86-64 code meets: checked"
  else
    grep -E "error|sorry" -A5 "build-$name-bytes.log" | head -n 20
    echo "push (AArch64) meets Push.byteContract: NOT checked"; exit 1
  fi
fi
# The audit: each instruction made to do nothing, and false statements, must be refused (control first).
if [ "$name" = push ] && [ "${MUTANTS:-1}" != 0 ]; then
  python3 mutants_push.py | tee "audit-$name.log" | grep -E "control|ACCEPTED|MALFORMED|instructions:|false statements:"
  grep -q "false statements: 5 rejected$" "audit-$name.log" && grep -q "18 instructions: 18 rejected$" "audit-$name.log" || { echo "the audit of push (AArch64): NOT as expected"; exit 1; }
fi
