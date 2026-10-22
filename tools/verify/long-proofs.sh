#!/bin/sh
# The proofs for one commit, on this VM, their result posted to GitHub as
# the commit's status "long proofs" (beside CI's checks): the Lean
# specification against C2SP's text and the proofs' definition from it;
# the generated hybrid file against its generator; the helpers; every
# hybrid kernel; every SME2 kernel at every group count; the x86-64
# kernels' compressions, hash_many and xof_many (prove_x86.py); the
# instruction models checked against the CPU; and the proofs' mutants.
# About an hour, in a worktree of the commit; nothing should measure
# meanwhile. The logs stay in tmp/long-proofs/COMMIT/, and
# the status names their SHA-256 and BLAKE3 hashes.
#
#     sh tools/verify/long-proofs.sh [COMMIT]     (default HEAD)
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
commit=$(git -C "$root" rev-parse "${1:-HEAD}")
token=$(cat "$root/ghtokenclassic.txt")
logs=$root/tmp/long-proofs/$commit
tree=/tmp/long-proofs-$commit
status() {
	python3 -c 'import json, sys; print(json.dumps({"state": sys.argv[1], "context": "long proofs", "description": sys.argv[2]}))' "$1" "$2" |
		curl -sSf -o /dev/null -X POST -H "Authorization: token $token" -d @- \
			"https://api.github.com/repos/johnservil/BLAKE3/statuses/$commit"
}
mkdir -p "$logs"
rm -rf "$tree"
git -C "$root" worktree prune
git -C "$root" worktree add -q --detach "$tree" "$commit"
status pending "running on the fork's VM"
cd "$tree"
export ELAN_HOME=${ELAN_HOME:-/root/.elan} PATH=/root/.elan/bin:$PATH
verdict=passed state=success
run() {  # name, command...: its log in $logs/name.txt; a failure ends the run
	name=$1; shift
	[ "$state" = success ] || return 0
	"$@" > "$logs/$name.txt" 2>&1 || { verdict="FAILED ($name)" state=failure; }
}
run lean_spec python3 c2sp/BLAKE3/check.py
run lean_emit sh -c 'python3 tools/verify/lean/emit.py && git diff --exit-code tools/verify/lean/compress.json tools/verify/lean/Generic.lean'
run generated sh -c 'python3 tools/gen_neon_hybrid.py | cmp - c/blake3_neon_hybrid_aarch64.S'
run helpers python3 -m unittest discover -s tools/verify -p 'test_*.py'
run prove_hybrid python3 tools/verify/prove_hybrid.py
run prove_sme2 python3 tools/verify/prove_sme2.py chunks chunks_at messages parents xof chunks_x2 every parents_every xof_every messages_every x2_every
run prove_x86 python3 tools/verify/prove_x86.py compress xof hash_many xof_many
run cross_check python3 tools/verify/cross_check.py
run mutants python3 tools/verify/mutants.py
b3=$(cat "$logs"/*.txt | cargo run -q --release --manifest-path b3sum/Cargo.toml -- --no-names)
sha=$(cat "$logs"/*.txt | sha256sum | cut -d' ' -f1)
# The status's description holds 140 characters: the logs' two hashes,
# each whole in base64url (RFC 4648, 43 characters for 256 bits), fit
# beside the verdict.
b64() { printf %s "$1" | tr a-f A-F | basenc --base16 -d | basenc --base64url | tr -d '='; }
description="$verdict; base64url SHA-256 $(b64 $sha) BLAKE3 $(b64 $b3)"
[ ${#description} -le 140 ] || { echo "long-proofs: the status description is ${#description} characters, over GitHub's 140: $description" >&2; exit 1; }
status "$state" "$description"
echo "long proofs $verdict for $commit; logs in $logs, SHA-256 $sha, BLAKE3 $b3 (hex)"
