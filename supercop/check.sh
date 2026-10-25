#!/bin/sh
# Usage: sh supercop/check.sh [SUPERCOP_VERSION]
# Runs this directory's rust_servil through a fresh SUPERCOP tree as eBASH
# does (./do-part init, then ./do-part crypto_hash blake3) and reports its
# checksums and SUPERCOP's choice among crypto_hash_blake3's
# implementations. Run it after make-tarball.sh, before sending a tarball.
# It downloads SUPERCOP (about 50 MB), compiles it with every compiler it
# finds (a minute with gcc alone, longer per compiler); its cycles count
# only from an idle machine.
set -e
v=${1:-20261004}
here=$(cd "$(dirname "$0")" && pwd)
w=${TMPDIR:-/tmp}/supercop-check
rm -rf "$w"; mkdir -p "$w"; cd "$w"
curl -sSfL "https://bench.cr.yp.to/supercop/supercop-$v.tar.xz" | tar -xJ
cd "supercop-$v"
cp -r "$here/crypto_hash/blake3/rust_servil" crypto_hash/blake3/
unset CARGO_TARGET_DIR     # SUPERCOP's Rust build chooses its own
# do-part's exit status says nothing about blake3 (init exits 1 when it has
# no errors to show); the data says it all.
./do-part init > ../init.log 2>&1 || true
./do-part crypto_hash blake3 > ../blake3.log 2>&1 || true
data=$(ls bench/*/data)
# A try line: ... try CHECKSUMS ok|fails CYCLES_AT_1536 ... IMPLEMENTATION COMPILER
python3 - "$data" <<'PY_END'
import sys
sums, bad, ours, chosen = set(), 0, 0, None
for line in open(sys.argv[1]):
    f = line.split()
    if len(f) > 13 and f[6] == "try":
        sums.add(f[7])
        bad += f[8] != "ok"
        if "rust_servil" in f[12]:
            ours += 1
            print(f"rust_servil {f[8]}, {f[9]} cycles at 1536 bytes ({f[13]})")
    elif len(f) > 7 and f[6] == "implementation":
        chosen = f[7]
print(f"checksums: {bad} failing, {len(sums)} distinct value(s) among all builds")
print(f"SUPERCOP chose: {chosen}")
if not ours or bad or len(sums) != 1:
    sys.exit("FAIL: rust_servil missing, a checksum failing, or the implementations disagreeing")
PY_END
echo "logs: $w/init.log, $w/blake3.log; data: $w/supercop-$v/$data"
