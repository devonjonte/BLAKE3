#!/bin/sh
# The long proofs (.github/workflows/long-proofs.yml) on this VM, for the
# branch given: registers an ephemeral GitHub Actions runner labelled
# vm-long (installed under /root when absent), dispatches the workflow on
# the branch, and runs its one job; the runner exits when the job ends, so
# it is online only then. Nothing else should measure meanwhile.
#
#     sh tools/runner/long-proofs.sh candidate/<topic>
set -eu
branch=${1:?usage: long-proofs.sh BRANCH}
root=$(cd "$(dirname "$0")/../.." && pwd)
token=$(cat "$root/ghtokenclassic.txt")
api=https://api.github.com/repos/johnservil/BLAKE3
dir=/root/actions-runner
version=2.338.0
if [ ! -x "$dir/run.sh" ]; then
	mkdir -p "$dir"
	curl -sSfL "https://github.com/actions/runner/releases/download/v$version/actions-runner-linux-arm64-$version.tar.gz" | tar xz -C "$dir"
fi
registration=$(curl -sSf -X POST -H "Authorization: token $token" "$api/actions/runners/registration-token" |
	pypy3 -c 'import json, sys; print(json.load(sys.stdin)["token"])')
cd "$dir"
RUNNER_ALLOW_RUNASROOT=1 ./config.sh --unattended --ephemeral --replace --name vm-long --labels vm-long \
	--no-default-labels --url https://github.com/johnservil/BLAKE3 --token "$registration"
curl -sSf -X POST -H "Authorization: token $token" -d "{\"ref\": \"$branch\"}" "$api/actions/workflows/long-proofs.yml/dispatches"
RUNNER_ALLOW_RUNASROOT=1 exec ./run.sh
