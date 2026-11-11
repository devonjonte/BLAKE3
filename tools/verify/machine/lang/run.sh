#!/bin/bash
# The same functions three ways (BLAKE3 #361): the crate's hand-written Rust, the Rust that Lean
# prints (compiled by rustc to assembly: way A), the assembly Lean prints itself (way B).
# usage: [LAB_SOURCE=ode] run.sh CRATE_DIR WORK_DIR   (CRATE_DIR: a checkout of blake3-servil-core; it is copied, and
# the copy gets labshim.rs appended to its src/lib.rs). Needs lake, cargo, rustc, cc, llvm-objdump.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); crate="$1"; work="$2"; mkdir -p "$work"
cd "$here"
lake build Lang > "$work/lake.log" 2>&1
# The functions: written as Lean values (Hasher.lean), or, with LAB_SOURCE=ode, in the language of our
# own (hasher.ode), which odec.py turns into Lean values first.
if [ "${LAB_SOURCE:-lean}" = ode ]; then
  python3 odec.py hasher.ode "$work/HasherOde.lean" | tee "$work/odec.txt"
  cp "$work/HasherOde.lean" HasherOde.lean; main=HasherOde.lean
else
  main=Hasher.lean
fi
lake env lean --run "$main" rust a_ > "$work/way_a.rs"
# LAB_OWN=1 (with the ode source): the assembly calls the kernels written in the source, not the crate's.
if [ "${LAB_OWN:-0}" = 1 ]; then lake env lean --run "$main" asm b_ own > "$work/way_b.S"; else lake env lean --run "$main" asm b_ > "$work/way_b.S"; fi
# Way A: the printed Rust, compiled once to assembly. No standard library, no panic machinery.
rustc --edition 2021 --crate-type lib --emit asm -C opt-level=3 -C panic=abort -C codegen-units=1 \
  -o "$work/way_a.raw.s" "$work/way_a.rs" 2> "$work/rustc.log"
# rustc's assembly is written for LLVM's assembler: GNU as does not know `.prefalign` (rustc 1.99).
# Here it becomes the plain alignment it prefers. (A shipped file would be printed from the proved
# bytes, not taken from rustc's text.)
python3 - "$work/way_a.raw.s" "$work/way_a.s" <<'ALIGN_PY'
import re, sys
text = open(sys.argv[1]).read()
text, n = re.subn(r"^\t\.prefalign\t(\d+),.*$", r"\t.p2align\t\1", text, flags=re.M)
with open(sys.argv[2], "w") as f: f.write(text)
print(n, "prefalign directives rewritten")
ALIGN_PY
rm -rf "$work/bench"; cp -R "$here/bench" "$work/bench"
rm -rf "$work/crate"; mkdir "$work/crate"; (cd "$crate" && git archive HEAD) | tar -x -C "$work/crate"
cat "$here/labshim.rs" >> "$work/crate/src/lib.rs"
features=""; grep -q "^b_compress_avx512:" "$work/way_b.S" && features="--features own_kernel"
(cd "$work/bench" && LAB_ASM="$work" CARGO_TARGET_DIR="$work/target" cargo build --release $features > "$work/cargo.log" 2>&1) || { tail -n 30 "$work/cargo.log"; exit 1; }
"$work/target/release/labbench" | tee "$work/bench.txt"
# What each way's code is: instructions a function.
python3 - "$work" <<'COUNT_PY' | tee "$work/sizes.txt"
import re, subprocess, sys
work = sys.argv[1]
text = subprocess.run(["llvm-objdump", "-d", "-C", "--no-show-raw-insn", f"{work}/target/release/labbench"], capture_output=True, text=True).stdout
want = {"a_push": "way A push", "b_push": "way B push", "a_merge": "way A merge", "b_merge": "way B merge", "a_to_hex": "way A to_hex", "b_to_hex": "way B to_hex", "a_hash": "way A hash", "b_hash": "way B hash"}
name, n, rows = None, 0, {}
for line in text.splitlines():
    m = re.match(r"^[0-9a-f]+ <(.+)>:$", line)
    if m:
        if name: rows[name] = n
        name, n = m.group(1), 0; continue
    if re.match(r"^\s+[0-9a-f]+:\s+\S", line) and not re.search(r"\s(nop|int3|ud2)\b", line): n += 1
if name: rows[name] = n
for k, v in want.items(): print(f"{v}: {rows.get(k, '?')} instructions")
for k, v in rows.items():
    if re.search(r"labshim::merge|Hash>::to_hex|CvStack>::merge|core::hash_serial$|hash_all_at_once|hasher::fill|hasher::feed|hasher::final_node", k): print(f"hand Rust {k[:70]}: {v} instructions")
COUNT_PY
echo "three ways compared"
