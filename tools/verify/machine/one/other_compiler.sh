#!/bin/sh
# The same source by another compiler: does merge's proof still check, and what had to be made again?
# rustc 1.98.0 compiles CvStack::merge to the same 100 instructions as 1.99.1 but for two stores, which it
# orders the other way round and emits as MOVUPS, not MOVAPS (other-compilers/merge-1.98.0.listing).
# This copies the folder, lifts that listing in place of 1.99.1's, and rebuilds everything about merge:
# the table and its lemmas (lift_one.py, recode.py), the trace of each part (leakgen.py asks Lean again),
# and every theorem. No proof text is edited. Exit status 0 only if merge_whole checks for the other code.
set -eu
here=$(cd "$(dirname "$0")" && pwd); listing=${1:-$here/other-compilers/merge-1.98.0.listing}
work="$here/../one.other"            # beside this folder, so that its relative paths hold; removed at the end
rm -rf "$work"; cp -R "$here" "$work"
trap 'rm -rf "$work"' EXIT
cd "$work"
python3 lift_one.py "$listing" merge 0x40000 Merge.lean Merge \
  --call blake3_servil_compress_in_place_avx512=0x30000 --call blake3_servil_compress_in_place_sse41=0x20000 --panics-from 0x1ba
python3 recode.py
lake build MergeSpec > spec.log 2>&1 || { grep -E "error" spec.log | head -n 10; echo "the result's proof does not check for this code"; exit 1; }
echo "merge_is_mergeN and merge_runs_mergeTo check for this code, unedited"
python3 leakgen.py probe
lake env lean LeakProbe.lean > probe.out 2>&1 || true
python3 leakgen.py extract
python3 leakgen.py final
lake build MergeAll > all.log 2>&1 || { grep -E "error" all.log | head -n 10; echo "the trace's proof does not check for this code"; exit 1; }
if diff -q MergeParts.lean "$here/MergeParts.lean" > /dev/null; then echo "the trace is the same"; else echo "the trace differs from 1.99.1's code's (as the code does), and merge_whole checks with it"; fi
echo "other compiler: checked"
