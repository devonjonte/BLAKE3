#!/bin/sh
# Build this project with a checked machine-code proof by default.
# Usage: ./build.sh NEW_OUTPUT_DIRECTORY [--skip-proof]
set -eu
here=$(cd "$(dirname "$0")" && pwd)
lang=$(cd "$here/../../lang" && pwd)
[ "$#" -ge 1 ] && [ "$#" -le 2 ] || { echo 'usage: build.sh NEW_OUTPUT_DIRECTORY [--skip-proof]' >&2; exit 2; }
out=$1
mode=${2:-prove}
case "$mode" in prove|--skip-proof) ;; *) echo 'the only opt-out is --skip-proof' >&2; exit 2;; esac
# Refuse an existing output before doing any work.
[ ! -e "$out" ] || { echo "output already exists: $out" >&2; exit 2; }
export OBJDUMP=${OBJDUMP:-llvm-objdump-21}
if [ "$mode" = prove ]; then
  (cd "$lang" && SOURCE="$here/adler32.ode" ODEMOD=AdlerOde ./prove_fn.sh adler32 0x100000)
fi
python3 "$here/../../observe.py" "$here/adler32.ode" adler32 "$out"
if [ "$mode" = --skip-proof ]; then
  echo 'UNVERIFIED: proof generation and checking explicitly skipped'
  exit 0
fi
# Both paths use the existing assembly printer. Refuse a mismatch between the
# observed object and the one lifted for the theorem, before claiming success.
cmp "$lang/adler32.o" "$out/function.o"
cp "$lang/Proof_adler32.lean" "$out/Proof_adler32.lean"
cp "$lang/Code_adler32.lean" "$out/Code_adler32.lean"
cp "$lang/adler32.build.log" "$out/proof.log"
python3 - "$out/report.json" <<'PY'
import json, sys
p = sys.argv[1]
r = json.load(open(p))
r['proof'] = 'Lean checked Proof_adler32.adler32_meets on the lifted x86-64 model; see proof.log for axioms'
with open(p, 'w') as f:
    json.dump(r, f, indent=2)
    f.write('\n')
PY
printf '%s\n' 'CHECKED: Proof_adler32.adler32_meets; observed object equals the object lifted for the theorem'
