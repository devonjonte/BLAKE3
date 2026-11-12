"""The lifter's rows of a word-level function -> Code_NAME.lean: its table, the program that is this
function with the two kernels (one/KCode.lean), and one lemma an address (attribute ode_at).
usage: gen_code.py NAME ROWS OUT.lean"""
import sys
name, rows_path, out = sys.argv[1:4]
rows = [l.rstrip("\n").split("\t") for l in open(rows_path)]
t = ["import Machine", "import KCode", "import Cells", "open X86", "",
     f"/-! `{name}` as assembled: {len(rows)} instructions. Written from the lifter's rows. -/", "",
     "set_option maxRecDepth 100000", f"namespace Code_{name}", "", "def table : List (Nat × Instr × Nat) := ["]
t += [f"  (0x{at}, {ins}, 0x{nxt}){',' if i + 1 < len(rows) else ''}" for i, (at, nxt, ins) in enumerate(rows)]
t += ["]", "", "/-- This function's instructions and the two kernels' (one/KCode.lean) as one program. -/",
      "def prog (pc : Nat) : Option (Instr × Nat) := (KCode.prog pc).or (table.lookup pc)", "",
      "theorem has_kernels : ∀ pc x, KCode.prog pc = some x → prog pc = some x := by",
      "  intro pc x h; simp only [prog, h, Option.some_or]", ""]
t += [f"@[ode_at] theorem at_{at} : prog 0x{at} = some ({ins}, 0x{nxt}) := rfl" for at, nxt, ins in rows]
t += ["", f"end Code_{name}", ""]
with open(out, "w") as f: f.write("\n".join(t))
