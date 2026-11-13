#!/bin/sh
# A function and its contract, from source to checked theorem (BLAKE3 #361). For `merge` of hasher.ode:
#   1. odec.py reads the source; Lean prints the assembly and where the compiler put each variable;
#   2. the assembler makes an ELF object, and the lifter reads the object's bytes back (llvm-objdump);
#   3. prove_fn.py writes the proof that those bytes meet the contract the source names (written in
#      Lean, by hand, for a reader: Spec_NAME.lean), from the source's invariant and that layout;
#   4. the function is run on its examples in the machine model and compared with the contract (seconds);
#   5. Lean checks NAME_meets. No proof text is written by hand for the function but the lemmas it names.
# Needs python3, cc (clang, or gcc on x86-64 Linux), llvm-objdump (OBJDUMP), lake.
# usage: [SOURCE=FILE.ode ODEMOD=Module] ./prove_fn.sh [NAME [BASE]]   (the source and the Lean module odec.py
# writes of it: hasher.ode and HasherOde unless said)
set -eu
here=$(cd "$(dirname "$0")" && pwd); cd "$here"
OBJDUMP=${OBJDUMP:-llvm-objdump}; export OBJDUMP
name=${1:-merge}; base=${2:-0x60000}
source=${SOURCE:-hasher.ode}; odemod=${ODEMOD:-HasherOde}; export ODEMOD="$odemod"
python3 odec.py "$source" "$odemod.lean"
lake build Lang "$odemod" > /dev/null
lake env lean --run "$odemod.lean" asm b3l_ only "$name" > "$name.S"
lake env lean --run "$odemod.lean" layout "$name" > "$name.layout"
# what the contract accepts of its arguments, read from the contract; the checked entry's code is made from it
contract=$(python3 -c "import odec,re,sys; c=odec.contracts_of(open(sys.argv[-1]).read())[0][sys.argv[1]]['head']; print(re.match(r'[\w.]+', next(r for w,r in c if w=='meets')).group(0))" "$name" "$source")
# the contract Xyz.contract is in Spec_xyz.lean
spec=$(python3 -c "import sys; print('Spec_' + sys.argv[1].split('.')[0].lower())" "$contract")
lake build Checks "$spec" > /dev/null
printf 'import Checks\nimport %s\n#checks %s\n' "$spec" "$contract" > "$name.checks.lean"
lake env lean "$name.checks.lean" > "$name.checks" || true
checked=0
if grep -q "^check " "$name.checks"; then checked=1; python3 check_fn.py asm "$source" "$name" "$name.checks" >> "$name.S"
elif grep -q "error" "$name.checks"; then echo "$name: what its contract accepts cannot be tested from the arguments: no checked entry; a caller shows it"; fi
if cc -target x86_64-unknown-linux-gnu -c -o "$name.o" "$name.S" 2>/dev/null; then :; else cc -c -o "$name.o" "$name.S"; fi
"$OBJDUMP" -d -r --x86-asm-syntax=intel "$name.o" > "$name.listing"
# the kernels are where one/KCode.lean has them; a function of this file that is called is where its `callee` line says
owncalls=$(python3 fn_args.py lift "$source" "$name")
withs=$(python3 fn_args.py code "$source" "$name")
python3 ../one/lift_one.py "$name.listing" "b3l_$name" "$base" "Lifted_$name.lean" "Lifted_$name" \
  --call blake3_servil_compress_in_place_avx512=0x30000 --call blake3_servil_compress_in_place_sse41=0x20000 $owncalls
targets="Proof_$name"
if [ "$checked" = 1 ]; then
  at=$(python3 -c "import re,sys; print(hex(int(sys.argv[2],0)+int(next(re.match(r'^([0-9a-f]+) <'+sys.argv[3]+'>:',l).group(1) for l in open(sys.argv[1]) if re.match(r'^[0-9a-f]+ <'+sys.argv[3]+'>:',l)),16)))" "$name.listing" "$base" "b3l_${name}_checked")
  python3 ../one/lift_one.py "$name.listing" "b3l_${name}_checked" "$at" "Lifted_${name}_checked.lean" "Lifted_${name}_checked" --call "b3l_$name=$base"
  python3 gen_code.py "$name" "Lifted_$name.lean.rows" "Code_$name.lean" "Lifted_${name}_checked.lean.rows" $withs
  python3 check_fn.py proof "$source" "$name" "$name.checks" "Lifted_${name}_checked.lean.rows" "$base" "Checked_$name.lean"
  targets="Proof_$name Checked_$name"
else
  python3 gen_code.py "$name" "Lifted_$name.lean.rows" "Code_$name.lean" $withs
fi
# first the quick answer: the function run on its examples (Example_NAME.lean) and compared with the contract.
# At least one example must meet what the contract requires (a contract nothing can meet proves nothing),
# and none may be refuted; a refutation says whether the source or the compiler's code is at fault.
examples=$(echo "$spec" | sed 's/^Spec_/Example_/')       # the contract's examples: every function that meets it is tried on them
if [ -f "$examples.lean" ]; then
  lake build "Code_$name" $(python3 fn_args.py standins "$source" "$name") "$examples" Checks TrySem "$odemod" > "$name.try.build.log" 2>&1 || { grep -E "error" "$name.try.build.log" | head -n 5; echo "the examples of $name do not build"; exit 1; }
  python3 try_fn.py "$source" "$name" "Lifted_$name.lean.rows" || { echo "the compiler's proof of $name: NOT checked (the examples above)"; exit 1; }
fi
# PROVE=0: a function that is tried on its contract's examples and not proved (one that stands in, when
# examples run, for a kernel this model does not hold)
if [ "${PROVE:-1}" = 0 ]; then echo "$name: tried on the examples of $contract; not proved"; exit 0; fi
# every contract comes with a theorem that it can be used (Usable.lean): a contract that asks the impossible is met by any code
ns=$(echo "$contract" | sed 's/\..*//')
grep -q "^theorem $ns.usable : ($contract " Usable.lean || { echo "$contract has no theorem that it can be used ($ns.usable in Usable.lean)"; echo "the compiler's proof of $name: NOT checked"; exit 1; }
targets="$targets Usable"
python3 prove_fn.py "$source" "$name" "Lifted_$name.lean.rows" "$name.layout" "Proof_$name.lean"
if lake build $targets > "$name.build.log" 2>&1 && ! grep -q -E "error|sorry" "$name.build.log"; then
  grep -E "Build completed" "$name.build.log"
  echo "the compiler's proof of $name: checked"
else
  grep -E "error|sorry" "$name.build.log" | head -n 5
  echo "the compiler's proof of $name: NOT checked"; exit 1
fi
