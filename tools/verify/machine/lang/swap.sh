#!/bin/sh
# One implementation of a contract swapped for another under a proved caller (BLAKE3 #361).
#
# `add` calls `merge` by Merge.contract, and is proved with nothing of merge but that contract. Here, in a
# copy of this folder, the one line of the source that says which code stands behind the contract is
# changed from `merge` to `merge_sse` (another function, proved to meet the same contract), and `add` is
# proved again from its source. Nothing else changes: not add's code, not its contract, not what the
# source gives the prover.
# Needs what prove_fn.sh needs.
set -eu
here=$(cd "$(dirname "$0")" && pwd); cd "$here"
./prove_fn.sh merge_sse 0x90000
./prove_fn.sh add 0x80000
d=$(mktemp -d ../swap-XXXXXX)
trap 'rm -rf "$d"' EXIT
cp -R . "$d/"
python3 - "$d/hasher.ode" <<'PY'
import sys
old = "callee merge at 0x60000 meets Merge.contract by Proof_merge.merge_meets budget 256"
new = "callee merge at 0x90000 meets Merge.contract by Proof_merge_sse.merge_sse_meets budget 256 code merge_sse"
t = open(sys.argv[1]).read()
assert t.count(old) == 1, "the source no longer has the line to change"
with open(sys.argv[1], "w") as f:
    f.write(t.replace(old, new))
PY
echo "the source, changed in one line:"
diff hasher.ode "$d/hasher.ode" || true
(cd "$d" && ./prove_fn.sh add 0x80000) || { echo "add with merge_sse behind the contract: NOT checked"; exit 1; }
grep -q "Code_add.has_merge_sse (Proof_merge_sse.merge_sse_meets" "$d/Proof_add.lean" || { echo "the proof does not use merge_sse: NOT checked"; exit 1; }
echo "lines of add's generated proof that differ: $(diff Proof_add.lean "$d/Proof_add.lean" | grep -c '^[<>]' || true) of $(wc -l < Proof_add.lean | tr -d ' ')"
echo "add with merge_sse behind Merge.contract in place of merge: checked"
