#!/bin/bash
# The levels beside the stack: agreement with the crate, then what each costs.
# usage: run_levels.sh CRATE_DIR WORK_DIR   (CRATE_DIR: a checkout of blake3-servil-core; it is copied, and
# the copy gets ../lang/labshim.rs appended to its src/lib.rs). Needs lake, cargo, cc, llvm-objdump, python3.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); crate="$1"; work="$2"; mkdir -p "$work"
python3 "$here/model.py" 3000 | tee "$work/model.txt"
cd "$here/../lang"
timeout 900 lake build Lang > "$work/lake.log" 2>&1
python3 odec.py "$here/levels.ode" LevelsOde.lean | tee "$work/odec.txt"
timeout 300 lake env lean --run LevelsOde.lean asm l_ > "$work/levels.S"
python3 odec.py hasher.ode "$work/HasherOde.lean" > /dev/null; cp "$work/HasherOde.lean" HasherOdeForLevels.lean
timeout 300 lake env lean --run HasherOdeForLevels.lean asm b_ > "$work/stack.S"; rm -f HasherOdeForLevels.lean
rm -rf "$work/bench"; cp -R "$here/bench" "$work/bench"
rm -rf "$work/crate"; mkdir "$work/crate"; (cd "$crate" && git archive HEAD) | tar -x -C "$work/crate"
cat "$here/../lang/labshim.rs" >> "$work/crate/src/lib.rs"
(cd "$work/bench" && LAB_ASM="$work" CARGO_TARGET_DIR="$work/target" cargo build --release > "$work/cargo.log" 2>&1) || { tail -n 30 "$work/cargo.log"; exit 1; }
"$work/target/release/levelsbench" | tee "$work/bench.txt"
python3 - "$work" <<'COUNT_PY' | tee "$work/sizes.txt"
import re, subprocess, sys
work = sys.argv[1]
text = subprocess.run(["llvm-objdump", "-d", "--no-show-raw-insn", f"{work}/target/release/levelsbench"], capture_output=True, text=True).stdout
name, n, rows = None, 0, {}
for line in text.splitlines():
    m = re.match(r"^[0-9a-f]+ <(.+)>:$", line)
    if m:
        if name: rows[name] = n
        name, n = m.group(1), 0; continue
    if re.match(r"^\s+[0-9a-f]+:\s+\S", line) and not re.search(r"\s(nop|int3|ud2)\b", line): n += 1
if name: rows[name] = n
for k in ("b_push", "b_merge", "b_hash", "l_ladd", "l_lroot", "l_hash2"): print(f"{k}: {rows.get(k, '?')} instructions")
COUNT_PY
echo "levels compared"
