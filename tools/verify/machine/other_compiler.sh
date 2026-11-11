#!/bin/sh
# The same source by another compiler: rustc 1.98.0 (and 1.97.0, the same bytes) compiles
# read_x86_features with two registers exchanged and three instructions in another order
# (other-compilers/Code-1.98.0.lean, as lift.py wrote it from that build). The theorem is built on that
# code with no edit of the proof. Exit status 0 only if it checks.
set -eu
here=$(cd "$(dirname "$0")" && pwd); work="$here/detection.other"
rm -rf "$work"; mkdir "$work"; trap 'rm -rf "$work"' EXIT
cp "$here"/*.lean "$here"/lakefile.toml "$here"/lean-toolchain "$here"/lake-manifest.json "$work/"
cp "$here/other-compilers/Code-1.98.0.lean" "$work/Code.lean"
if cmp -s "$work/Code.lean" "$here/Code.lean"; then echo "the other compiler's code is the same"; exit 1; fi
(cd "$work" && lake build > build.log 2>&1) || { grep -E "error" "$work/build.log" | head -n 5; echo "the theorem does not check for this code"; exit 1; }
grep -q "sorryAx" "$work/build.log" && { echo "sorry"; exit 1; }
echo "read_x86_features_is_the_rule checks for rustc 1.98.0's code, unedited"
