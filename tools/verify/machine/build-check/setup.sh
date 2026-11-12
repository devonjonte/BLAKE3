#!/bin/bash
# The independent-checker trial, step 1 (on the workhorse): build lean4export for the lab's Lean and nanoda.
# Usage: setup.sh WORKDIR ; writes WORKDIR/setup.txt
set -u
W=$1; mkdir -p "$W"; cd "$W" || exit 1
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
: > setup.txt
if [ ! -d lean4export ]; then
  timeout 120 git clone -q https://github.com/leanprover/lean4export lean4export || { echo "clone lean4export failed" >> setup.txt; exit 1; }
fi
( cd lean4export && git checkout -q v4.34.0-rc2 && echo "leanprover/lean4:v4.34.1" > lean-toolchain \
  && echo "lean4export $(git rev-parse HEAD) with $(cat lean-toolchain)" >> ../setup.txt \
  && timeout 900 lake build > ../lean4export-build.log 2>&1 < /dev/null; echo "lean4export build rc=$?" >> ../setup.txt )
ls -la lean4export/.lake/build/bin/ >> setup.txt 2>&1
if [ ! -d nanoda ]; then
  timeout 120 git clone -q https://github.com/ammkrn/nanoda_lib nanoda || { echo "clone nanoda failed" >> setup.txt; exit 1; }
fi
( cd nanoda && echo "nanoda $(git rev-parse HEAD)" >> ../setup.txt && (cargo --version; rustc --version) >> ../setup.txt 2>&1 \
  && timeout 900 cargo build --release > ../nanoda-build.log 2>&1 < /dev/null; echo "nanoda build rc=$?" >> ../setup.txt )
ls -la nanoda/target/release/nanoda_bin >> setup.txt 2>&1
echo done >> setup.txt
