#!/bin/sh
# The long proofs for one commit, on this VM, their result posted to
# GitHub as the commit's status "long proofs" (beside CI's checks): every
# SME2 kernel at every group count (the chunk and parent kernels'
# inductions are what the SME2 contracts in the Rust and whole-call proofs
# rest on), then the Rust paths and whole calls, with the instruction
# models they run checked against the CPU. About eight hours, in a worktree
# of the commit; nothing should measure meanwhile. The logs stay in
# tmp/long-proofs/COMMIT/, and the status names their BLAKE3 hash.
#
#     sh tools/verify/long-proofs.sh [COMMIT]     (default HEAD)
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
commit=$(git -C "$root" rev-parse "${1:-HEAD}")
token=$(cat "$root/ghtokenclassic.txt")
logs=$root/tmp/long-proofs/$commit
tree=/tmp/long-proofs-$commit
status() {
	pypy3 -c 'import json, sys; print(json.dumps({"state": sys.argv[1], "context": "long proofs", "description": sys.argv[2]}))' "$1" "$2" |
		curl -sSf -o /dev/null -X POST -H "Authorization: token $token" -d @- \
			"https://api.github.com/repos/johnservil/BLAKE3/statuses/$commit"
}
mkdir -p "$logs"
rm -rf "$tree"
git -C "$root" worktree prune
git -C "$root" worktree add -q --detach "$tree" "$commit"
status pending "running on the fork's VM"
cd "$tree"
verdict=passed state=success
{ pypy3 tools/verify/prove_sme2.py chunks chunks_at messages parents xof every parents_every xof_every messages_every \
		> "$logs/prove_sme2.txt" 2>&1 &&
	pypy3 tools/verify/cross_check.py > "$logs/cross_check.txt" 2>&1; } || { verdict=FAILED state=failure; }
hash=$(pypy3 -c 'import sys; sys.path.insert(0, "tools/verify"); import results
print(results.blake3(data="\n".join(results.blake3(sorted(sys.argv[1:]))).encode())[0][:16])' "$logs"/*.txt)
status "$state" "$verdict: prove_sme2, cross_check; logs' BLAKE3 $hash (VM, tmp/long-proofs/)"
echo "long proofs $verdict for $commit; logs in $logs, BLAKE3 $hash"
