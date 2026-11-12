#!/bin/bash
# The build that checks its proof, tried: the crate as it is (tests must pass), then two changed copies
# (the build must fail). Usage: build-trial.sh CRATE OUT
export PATH="/opt/homebrew/opt/python@3.14/libexec/bin:/opt/homebrew/bin:$HOME/.cargo/bin:$PATH"
C=$1; O=$2; mkdir -p "$O"; : > "$O/result.txt"
S=$(mktemp -d); export CARGO_TARGET_DIR=$S/target
cp -R "$C" "$S/good"; cd "$S/good" || exit 1
( time cargo test --release ) > "$O/good.log" 2>&1; echo "unchanged: cargo test rc=$?" >> "$O/result.txt"
grep -h "proof checked\|test result\|^real" "$O/good.log" >> "$O/result.txt"
# again, with the checker already built: what the proof costs a build
touch build.rs; ( time cargo build --release ) > "$O/again.log" 2>&1; echo "again: cargo build rc=$?" >> "$O/result.txt"
grep -h "proof checked\|^real" "$O/again.log" >> "$O/result.txt"
# control 1: one instruction word changed in the proof's export
cp -R "$C" "$S/word"; cd "$S/word" || exit 1
python3 - <<'PY'
import gzip
with gzip.open("proof/push_arm_meets.ndjson.gz", "rt") as f: t = f.read()
old, new = '"natVal":"2852127728"', '"natVal":"2852127730"'
assert t.count(old) == 1 and new not in t
with gzip.open("proof/push_arm_meets.ndjson.gz", "wt") as f: f.write(t.replace(old, new))
PY
cargo build --release > "$O/word.log" 2>&1; echo "one instruction word changed in the export: cargo build rc=$?" >> "$O/result.txt"
grep -h "panicked\|assertion" "$O/word.log" | head -n 2 | cut -c1-200 >> "$O/result.txt"
# control 2: the statement a reader read is another
cp -R "$C" "$S/stmt"; cd "$S/stmt" || exit 1
python3 - <<'PY'
from pathlib import Path
p = Path("proof/push_arm_meets.statement.txt"); t = p.read_text()
assert t.count("Push.byteContract st cv new cvs") == 1
p.write_text(t.replace("Push.byteContract st cv new cvs", "Push.byteContract cv st new cvs"))
PY
cargo build --release > "$O/stmt.log" 2>&1; echo "the statement file changed: cargo build rc=$?" >> "$O/result.txt"
grep -h "is not the statement" "$O/stmt.log" | head -n 1 | cut -c1-200 >> "$O/result.txt"
rm -rf "$S"; echo done >> "$O/result.txt"
