"""The lifter's rows of a word-level function -> Code_NAME.lean: its table, the program it runs in, and one
lemma an address (attribute ode_at). The program is this function's instructions, after the two kernels'
(one/KCode.lean) if it calls anything, and after the instructions of each function of ours it calls
(`--with OTHER`: Code_OTHER.lean; `--with OTHER+k` if OTHER's own program has the kernels). Each of those
is shown to be in it unchanged (`has_kernels`, `has_OTHER`), so that a theorem about a callee in its own
program holds in this one.
usage: gen_code.py NAME ROWS OUT.lean [MORE_ROWS ...] [--with OTHER[+k] ...]   (more rows: the function's checked entry)"""
import sys
args = sys.argv[1:]
withs = [args[i + 1] for i, a in enumerate(args) if a == "--with"]
args = [a for i, a in enumerate(args) if a != "--with" and (i == 0 or args[i - 1] != "--with")]
name, rows_path, out = args[:3]
rows = [l.rstrip("\n").split("\t") for path in [rows_path] + args[3:] for l in open(path)]
calls = any(ins.startswith(".call") for _, _, ins in rows)      # a function that calls nothing is its own program
mods = [(w.split("+")[0], w.endswith("+k")) for w in withs]
t = ["import Machine"] + (["import KCode"] if calls else []) + ["import Cells"] + [f"import Code_{w}" for w, _ in mods] + ["open X86", "",
     f"/-! `{name}` as assembled: {len(rows)} instructions. Written from the lifter's rows. -/", "",
     "set_option maxRecDepth 100000", f"namespace Code_{name}", "", "def table : List (Nat × Instr × Nat) := ["]
t += [f"  (0x{at}, {ins}, 0x{nxt}){',' if i + 1 < len(rows) else ''}" for i, (at, nxt, ins) in enumerate(rows)]
t += ["]", ""]
if calls:
    # pre0 = the kernels; pre_i = pre_(i-1) ++ the i-th callee's instructions; whole = pre_n ++ this function's
    t += ["def pre0 : List (Nat × Instr × Nat) := KCode.table"]
    for i, (w, _) in enumerate(mods, 1):
        t += [f"def pre{i} : List (Nat × Instr × Nat) := pre{i - 1} ++ Code_{w}.table"]
    n = len(mods)
    t += ["", "/-- Every instruction of the program: the two kernels' (one/KCode.lean), " + "".join(f"`{w}`'s, " for w, _ in mods) + "then this function's. -/",
          f"def whole : List (Nat × Instr × Nat) := pre{n} ++ table", ""]
else:
    t += ["/-- Every instruction of the program: this function's (it calls nothing). -/",
          "def whole : List (Nat × Instr × Nat) := table", ""]
t += ["def prog (pc : Nat) : Option (Instr × Nat) := whole.lookup pc", "",
      "/-- The addresses the program has an instruction at. -/",
      "def keys : List Nat := whole.map (·.1)", "",
      "theorem keys_of : ∀ pc x, prog pc = some x → pc ∈ keys := fun pc x h => lookup_mem_keys whole pc x h", ""]
if calls:
    def lifted(i, inner):
        """What pre_i holds, the whole program holds: through each later table."""
        for j in range(i + 1, n + 1):
            inner = f"lookup_append_left pre{j - 1} Code_{mods[j - 1][0]}.table pc x ({inner})"
        return f"lookup_append_left pre{n} table pc x ({inner})"
    t += ["theorem has_kernels : ∀ pc x, KCode.prog pc = some x → prog pc = some x := by",
          "  intro pc x h", f"  exact {lifted(0, 'h')}", ""]
    for i, (w, k) in enumerate(mods, 1):
        t += [f"/-- `{w}`'s program is part of this one, unchanged. -/",
              f"theorem has_{w} : ∀ pc x, Code_{w}.prog pc = some x → prog pc = some x := by",
              "  intro pc x h"]
        if k:
            t += [f"  have h' : (KCode.table ++ Code_{w}.table).lookup pc = some x := h",
                  "  rw [lookup_append_or] at h'",
                  "  cases hk : KCode.table.lookup pc with",
                  "  | some y =>",
                  "    rw [hk] at h'; simp only [Option.some_or, Option.some.injEq] at h'; subst h'",
                  "    exact has_kernels pc y hk",
                  "  | none =>",
                  "    rw [hk] at h'; simp only [Option.none_or] at h'"]
            ind = "    "
        else:
            t += [f"  have h' : Code_{w}.table.lookup pc = some x := h"]
            ind = "  "
        t += [f"{ind}have apart : ∀ p ∈ Code_{w}.table.map (·.1), ((pre{i - 1}.lookup p).isNone) = true := by decide +kernel",
              f"{ind}have none := Option.isNone_iff_eq_none.mp (apart pc (lookup_mem_keys _ pc x h'))",
              f"{ind}have here : pre{i}.lookup pc = some x := by",
              f"{ind}  show (pre{i - 1} ++ Code_{w}.table).lookup pc = some x",
              f"{ind}  rw [lookup_append_or, none]; exact h'",
              f"{ind}exact {lifted(i, 'here')}", ""]
t += [f"@[ode_at] theorem at_{at} : prog 0x{at} = some ({ins}, 0x{nxt}) := rfl" for at, nxt, ins in rows]
t += ["", f"end Code_{name}", ""]
with open(out, "w") as f: f.write("\n".join(t))
