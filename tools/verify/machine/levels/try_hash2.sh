#!/bin/bash
# `hash2` (the whole hash on the levels) against the contract of `hash`, unchanged: Hash.byteContract
# (../spec/HashContract.lean), by the trial ../lang/HashTry.lean with two names changed and nothing else
# (the source function, and the skip of the 32-lane path that hash2 does not have). Not a proof: the
# source's meaning, kernels as their contracts, on the test vectors' lengths.
# usage: try_hash2.sh [LOG]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); log=${1:-$here/hashtry2.log}
cd "$here/../lang"
python3 odec.py "$here/levels.ode" LevelsOde.lean > /dev/null
python3 - <<'PY'
from pathlib import Path
t = Path("HashTry.lean").read_text()
for old, new, n in (("import HasherOde\n", "import LevelsOde\n", 1),
                    ("(hashEnv Ode.hash) 2000000 Ode.hash [", "(hashEnv Ode.hash2) 2000000 Ode.hash2 [", 1),
                    ("      if plat == 5 && n > 32768 then continue\n", "", 1),
                    ("hash, the source's meaning against", "hash2 (the levels), the source's meaning against", 1)):
    assert t.count(old) == n, old
    t = t.replace(old, new)
Path("HashTry2.lean").write_text(t)
PY
timeout 900 lake build TrySem LevelsOde HashContract > "$log.build" 2>&1 || { echo "NOT tried: the build failed"; tail -n 5 "$log.build"; rm -f HashTry2.lean; exit 1; }
timeout 1800 lake env lean HashTry2.lean > "$log" 2>&1 || { echo "NOT tried"; tail -n 5 "$log"; rm -f HashTry2.lean; exit 1; }
rm -f HashTry2.lean
cat "$log"
grep -q "105 examples meet it, 0 do not" "$log" && grep -q "holds on 105" "$log" || { echo "NOT as expected"; exit 1; }
