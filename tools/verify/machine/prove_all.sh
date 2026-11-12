#!/bin/sh
# Everything the language's compiler proves, from the source to checked theorems, in one command (BLAKE3 #361).
#
#   x86-64 (our machine model, lang/):  hex, merge (and its checked entry), push, merge_sse, add (by its
#       callees' contracts; then with merge_sse swapped in behind merge's contract), merge_steps
#   AArch64 (Google DeepMind's model, arm/; fetched at the commit arm/lakefile.toml names):
#       hex_neon (the kernel), push (the same source function, printed for AArch64)
#   Contracts that name no machine (spec/HexContract.lean, PushContract.lean, MergeContract.lean): "any-machine"
#       is the four x86-64 theorems (hex, push, merge, add); "hex_neon" and "push-aarch64" end with the two
#       AArch64 ones (hex, push).
#
# Each line of the result is one function: what Lean checked, and how long it took here.
# Needs python3, cc or clang, llvm-objdump (OBJDUMP), lake (elan). AUDIT=1 also runs the audits (minutes more).
set -u
here=$(cd "$(dirname "$0")" && pwd)
OBJDUMP=${OBJDUMP:-llvm-objdump}; export OBJDUMP
fails=0
run() {  # run LABEL DIR COMMAND...
  label=$1; dir=$2; shift 2
  start=$(date +%s)
  if (cd "$here/$dir" && "$@") > "$here/prove_all.$label.log" 2>&1; then verdict=checked; else verdict="NOT checked (prove_all.$label.log)"; fails=$((fails + 1)); fi
  printf '%-28s %-12s %4s s   %s\n' "$label" "$dir/" "$(( $(date +%s) - start ))" "$verdict"
  case "$label" in audit-*) echo "    $(grep -E "rejected" "$here/prove_all.$label.log" | tail -n 1)";; esac
}
if [ "${AUDIT:-0}" = 1 ]; then hexaudit=1; else hexaudit=0; fi
run hex          lang env MUTANTS=$hexaudit ./prove.sh
run merge        lang ./prove_fn.sh merge 0x60000
run push         lang ./prove_fn.sh push 0x70000
run merge_sse    lang ./prove_fn.sh merge_sse 0x90000
run add-and-swap lang ./swap.sh
run merge_steps  lang ./prove_fn.sh merge_steps 0xA0000
run any-machine  lang sh -c 'lake build Meets_hex_bytes Meets_push_bytes Meets_merge_bytes UsableBytes > any.log 2>&1 && ! grep -q -E "error|sorry" any.log && [ "$(grep -c "_meets_bytes. depends on axioms" any.log)" = 4 ] && grep -q "usable_bytes. depends on axioms" any.log'
run hex_neon     arm  env MUTANTS=$hexaudit ./prove_arm.sh
run push-aarch64 arm  env MUTANTS=$hexaudit ./prove_arm_fn.sh
if [ "${AUDIT:-0}" = 1 ]; then
  run audit-merge  lang python3 mutants_fn.py "${JOBS:-6}"
  run audit-push   lang python3 mutants_code.py push "${JOBS:-6}"
  run audit-add    lang python3 mutants_code.py add "${JOBS:-6}"
  run audit-steps  lang python3 mutants_code.py merge_steps "${JOBS:-6}"
fi
[ "$fails" = 0 ] && echo "all checked" || { echo "$fails NOT checked"; exit 1; }
