#!/usr/bin/env python3
"""The independent-checker trial, step 3 (on the workhorse): controls.

    controls.py WORKDIR ARMLAB

The export of `push_arm_meets` that nanoda accepted is changed in one literal and checked again; each
changed copy must be refused. Then the checker prints the theorem's statement back from the export.
"""
import json, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import trial

W = Path(sys.argv[1])
SRC = W / "push_arm_meets.ndjson"
text = SRC.read_text()

def absent(n):
    """The first number above n that the export does not hold (its parser refuses a literal it has twice,
    which would be a refusal for the wrong reason)."""
    k = n + 1
    while f'"natVal":"{k}"' in text:
        k += 1
    return k


# The function's first instruction word, aa0003f0 (mov x16, x0), as the number the export holds.
FIRST = 0xAA0003F0
CASES = [("unchanged copy (must be accepted)", None, None)]
for what, n in (("the first instruction word, aa0003f0", FIRST), ("the stack's size in bytes, 1792", 1792),
                ("the stack's capacity, 55", 55), ("a chaining value's size, 32", 32)):
    k = absent(n)
    CASES.append((f"{what} as {k:x}" if n == FIRST else f"{what} as {k}", f'"natVal":"{n}"', f'"natVal":"{k}"'))
for i, (what, old, new) in enumerate(CASES):
    t = text
    if old is not None:
        n = t.count(old)
        if n == 0:
            print(f"control {i}: {what}: literal not in the export, NOT a control", flush=True)
            continue
        t = t.replace(old, new)
        what += f" ({n} place{'s' if n > 1 else ''})"
    p = W / f"control{i}.ndjson"
    with open(p, "w") as f:
        f.write(t)
    print(f"control {i}: {what}", flush=True)
    trial.check(f"control{i}", p, 16)
    p.unlink()

# The statement, printed back by the checker from what it checked.
cfg = W / "pp.json"
with open(cfg, "w") as f:
    json.dump({"export_file_path": str(SRC), "use_stdin": False, "num_threads": 16,
               "permitted_axioms": trial.THREE, "unpermitted_axiom_hard_error": True,
               "nat_extension": True, "string_extension": True, "print_success_message": True,
               "pp_declars": ["push_arm_meets", "push_arm_code"], "pp_to_stdout": False,
               "pp_output_path": str(W / "statement.txt"),
               "pp_options": {"proofs": False, "width": 110}}, f)
with open(W / "statement.txt", "w"):
    pass
rc, secs, out = trial.run([str(trial.NANODA), str(cfg)], W, 600)
print(f"statement printed: rc={rc} {secs:.1f} s: {out.strip()[:300]}", flush=True)
print("done", flush=True)
