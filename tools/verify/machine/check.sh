#!/bin/sh
# Check the experiment: the library's machine code is what Code.lean holds, and the theorem builds
# on the three standard axioms and bv_decide's own. Needs cargo, llvm-objdump, python3, lake.
set -eu
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../../.." && pwd)
work=${MACHINE_WORK:-$(mktemp -d)}; mkdir -p "$work/x"
(cd "$root" && CARGO_TARGET_DIR="$work/target" CARGO_INCREMENTAL=0 cargo build --release >"$work/build.log" 2>&1)
cp "$work/target/release/libblake3_servil.rlib" "$work/x/" && (cd "$work/x" && ar x libblake3_servil.rlib)
python3 - "$work" <<'PY'
import glob, re, subprocess, sys
work = sys.argv[1]
want = {"blake3_servil::platform::read_x86_features": "features", "blake3_servil::platform::read_cpu_words": "words", "core::core_arch::x86::xsave::_xgetbv": "xgetbv"}
found = {}
for obj in sorted(glob.glob(work + "/x/*.o")):
    plain = subprocess.run(["nm", "--defined-only", obj], capture_output=True, text=True).stdout.splitlines()
    nice = subprocess.run(["nm", "-C", "--defined-only", obj], capture_output=True, text=True).stdout.splitlines()
    for p, n in zip(plain, nice):
        pf, nf = p.split(None, 2), n.split(None, 2)
        if len(pf) == 3 and len(nf) == 3 and pf[1] in "Tt" and nf[2] in want:
            assert nf[2] not in found, f"two definitions of {nf[2]}"
            found[nf[2]] = (obj, pf[2])
assert set(found) == set(want), f"missing: {set(want) - set(found)}"
for name, short in want.items():
    obj, mangled = found[name]
    text = subprocess.run(["llvm-objdump", "-d", "-r", "-M", "intel", f"--disassemble-symbols={mangled}", obj], capture_output=True, text=True, check=True).stdout
    open(f"{work}/{short}.s", "w").write(text)
PY
python3 "$here/lift.py" "$work/Code.lean" Code "0x1000:$work/features.s" "0x2000:$work/words.s" "0x3000:$work/xgetbv.s" >/dev/null
cmp "$work/Code.lean" "$here/Code.lean" || { echo "Code.lean is not this build's machine code" >&2; exit 1; }
echo "Code.lean is this build's machine code"
(cd "$here" && lake build 2>&1 | tee "$work/lake.log" | grep -E "depends on axioms|error" || true)
python3 - "$work/lake.log" <<'PY'
import re, sys
log = open(sys.argv[1]).read()
lists = re.findall(r"depends on axioms: \[([^\]]*)\]", log)
assert lists, "no axioms were printed"
for names in lists:
    for name in (n.strip() for n in names.split(",")):
        assert name in ("propext", "Classical.choice", "Quot.sound") or "._native.bv_decide.ax_" in name, f"another axiom: {name}"
PY
grep -q "Build completed successfully" "$work/lake.log"
echo "the theorem builds"
