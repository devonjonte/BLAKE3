"""The lifter's rows of a word-level function -> Code_NAME.lean: its table, the program it runs in, and one
lemma an address (attribute ode_at). The program is this function's instructions, after the two kernels'
(one/KCode.lean) if it calls anything, and after the instructions of each function of ours it calls
(`--with OTHER`: Code_OTHER.lean; `--with OTHER+k` if OTHER's own program has the kernels). Each of those
is shown to be in it unchanged (`has_kernels`, `has_OTHER`), so that a theorem about a callee in its own
program holds in this one. A callee that itself calls functions of ours brings their instructions too
(read from its Code_OTHER.lean): every table once, and each callee's whole program shown to be in this one.
`--ext`: the program is these instructions over any others (`prog ext`: where this table has no instruction,
`ext`'s): for a function that calls code this model does not hold (a kernel called by a contract its caller
assumes). A function that calls such a function is such a function (seen in the callee's Code file).
usage: gen_code.py NAME ROWS OUT.lean [MORE_ROWS ...] [--with OTHER[+k] ...] [--ext]   (more rows: the function's checked entry)"""
import sys
args = sys.argv[1:]
EXT = "--ext" in args
args = [a for a in args if a != "--ext"]
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
import os, re
def code_of(w):
    return open(os.path.join(os.path.dirname(os.path.abspath(out)), f"Code_{w}.lean")).read()
EXT_CALLEES = [w for w in dict.fromkeys(x.split("+")[0] for x in withs) if re.search(r"^def prog \(ext ", code_of(w), re.M)]
EXT = EXT or bool(EXT_CALLEES)
PROGDEF = (["def prog (ext : Nat → Option (Instr × Nat)) (pc : Nat) : Option (Instr × Nat) := (whole.lookup pc).or (ext pc)", "",
            "/-- What this table holds, the program holds, whatever else it holds. -/",
            "theorem prog_of (ext : Nat → Option (Instr × Nat)) : ∀ pc x, whole.lookup pc = some x → prog ext pc = some x := by",
            "  intro pc x h; simp only [prog, h, Option.some_or]", ""] if EXT else
           ["def prog (pc : Nat) : Option (Instr × Nat) := whole.lookup pc", "",
            "/-- The addresses the program has an instruction at. -/",
            "def keys : List Nat := whole.map (·.1)", "",
            "theorem keys_of : ∀ pc x, prog pc = some x → pc ∈ keys := fun pc x h => lookup_mem_keys whole pc x h", ""])
P_ = "prog ext" if EXT else "prog"                 # the program, in a statement
BIND = "(ext : Nat → Option (Instr × Nat)) " if EXT else ""
def into(inner):
    """A fact `whole.lookup pc = some x` as a fact of the program."""
    return f"prog_of ext pc x ({inner})" if EXT else inner
def parts_of(w):
    """The tables of a callee's own program, in its order: the kernels', each function's it calls, its own."""
    txt = open(os.path.join(os.path.dirname(os.path.abspath(out)), f"Code_{w}.lean")).read()
    ps = ["KCode"] if re.search(r"^def pre0 .*:= KCode\.table", txt, re.M) else []
    return ps + re.findall(r"^def pre\d+ .*:= pre\d+ \+\+ Code_(\w+)\.table", txt, re.M) + [w]
NESTED = calls and (EXT or any(len([p for p in parts_of(w) if p != "KCode"]) > 1 for w, _ in mods))
if NESTED:
    # A callee that calls functions of ours itself: this program holds every table of every callee's program,
    # each once. P[0] is the kernels'; pre_i = pre_(i-1) ++ P[i]; whole = pre_n ++ this function's.
    P = ["KCode"]
    for w, _ in mods:
        P += [x for x in parts_of(w) if x not in P]
    tbl = lambda x: "KCode.table" if x == "KCode" else f"Code_{x}.table"
    n = len(P) - 1
    t = [l for l in t if not l.startswith("import Code_")]
    at = t.index("import Cells") + 1
    t[at:at] = [f"import Code_{x}" for x in P[1:]]
    t += ["def pre0 : List (Nat × Instr × Nat) := KCode.table"]
    t += [f"def pre{i} : List (Nat × Instr × Nat) := pre{i - 1} ++ {tbl(P[i])}" for i in range(1, n + 1)]
    t += ["", "/-- Every instruction of the program: the two kernels' (one/KCode.lean), " + "".join(f"`{x}`'s, " for x in P[1:]) + "then this function's. -/",
          f"def whole : List (Nat × Instr × Nat) := pre{n} ++ table", ""] + PROGDEF
    def lifted(i, inner):
        for j in range(i + 1, n + 1):
            inner = f"lookup_append_left pre{j - 1} {tbl(P[j])} pc x ({inner})"
        return into(f"lookup_append_left pre{n} table pc x ({inner})")
    t += [f"theorem has_kernels {BIND}: ∀ pc x, KCode.prog pc = some x → {P_} pc = some x := by",
          "  intro pc x h", f"  exact {lifted(0, 'h')}", ""]
    for i in range(1, n + 1):
        t += [f"/-- `{P[i]}`'s own instructions are in this program: no table before them has one at any of their addresses. -/",
              f"theorem in{i} {BIND}: ∀ pc x, {tbl(P[i])}.lookup pc = some x → {P_} pc = some x := by",
              "  intro pc x h",
              f"  have apart : ∀ p ∈ {tbl(P[i])}.map (·.1), ((pre{i - 1}.lookup p).isNone) = true := by decide +kernel",
              "  have none := Option.isNone_iff_eq_none.mp (apart pc (lookup_mem_keys _ pc x h))",
              f"  have here : pre{i}.lookup pc = some x := by",
              f"    show (pre{i - 1} ++ {tbl(P[i])}).lookup pc = some x",
              "    rw [lookup_append_or, none]; exact h",
              f"  exact {lifted(i, 'here')}", ""]
    for w, _ in mods:
        Q = parts_of(w)
        if not EXT:
            t += [f"/-- `{w}`'s program (its own instructions and those of what it calls) is part of this one, unchanged. -/",
                  f"theorem has_{w} : ∀ pc x, Code_{w}.prog pc = some x → prog pc = some x := by",
                  "  intro pc x h",
                  f"  have h' : ({' ++ '.join(tbl(q) for q in Q)}).lookup pc = some x := h"] + \
                 (["  simp only [lookup_append_or] at h'"] if len(Q) > 1 else [])
            ind = "  "
            for j, q in enumerate(Q):
                use = "has_kernels" if q == "KCode" else f"in{P.index(q)}"
                if j + 1 == len(Q):
                    t += [f"{ind}exact {use} pc x h'"]
                else:
                    t += [f"{ind}cases h{j} : {tbl(q)}.lookup pc with",
                          f"{ind}| some y =>",
                          f"{ind}  rw [h{j}] at h'; simp only [Option.some_or, Option.some.injEq] at h'; subst h'",
                          f"{ind}  exact {use} pc y h{j}",
                          f"{ind}| none =>",
                          f"{ind}  rw [h{j}] at h'; simp only [Option.none_or] at h'"]
                    ind += "  "
            t += [""]
            continue
        concat = " ++ ".join(tbl(q) for q in Q)
        E_ = " ext" if EXT else ""
        t += [f"/-- The tables of `{w}`'s program (its own instructions and those of what it calls) are in this one, unchanged. -/",
              f"theorem tables_{w} {BIND}: ∀ pc x, ({concat}).lookup pc = some x → {P_} pc = some x := by",
              "  intro pc x h'"] + \
             (["  simp only [lookup_append_or] at h'"] if len(Q) > 1 else [])
        ind = "  "
        for j, q in enumerate(Q):
            use = ("has_kernels" if q == "KCode" else f"in{P.index(q)}") + E_
            if j + 1 == len(Q):
                t += [f"{ind}exact {use} pc x h'"]
            else:
                t += [f"{ind}cases h{j} : {tbl(q)}.lookup pc with",
                      f"{ind}| some y =>",
                      f"{ind}  rw [h{j}] at h'; simp only [Option.some_or, Option.some.injEq] at h'; subst h'",
                      f"{ind}  exact {use} pc y h{j}",
                      f"{ind}| none =>",
                      f"{ind}  rw [h{j}] at h'; simp only [Option.none_or] at h'"]
                ind += "  "
        t += [""]
        if w in EXT_CALLEES:
            t += [f"/-- `{w}`'s program over this one is this one: a theorem about `{w}` over any program holds here. -/",
                  f"theorem has_{w} {BIND}: ∀ pc x, Code_{w}.prog ({P_}) pc = some x → {P_} pc = some x := by",
                  "  intro pc x h",
                  f"  have h0 : (({concat}).lookup pc).or ({P_} pc) = some x := h",
                  f"  cases hw : ({concat}).lookup pc with",
                  "  | none => rw [hw] at h0; simpa only [Option.none_or] using h0",
                  "  | some y =>",
                  "    rw [hw] at h0; simp only [Option.some_or, Option.some.injEq] at h0; subst h0",
                  f"    exact tables_{w}{E_} pc y hw", "",
                  f"/-- And this program is `{w}`'s over it: what is assumed of this program holds of that one. -/",
                  f"theorem over_{w} {BIND}: ∀ pc x, {P_} pc = some x → Code_{w}.prog ({P_}) pc = some x := by",
                  "  intro pc x h",
                  f"  show (({concat}).lookup pc).or ({P_} pc) = some x",
                  f"  cases hw : ({concat}).lookup pc with",
                  "  | none => simpa only [Option.none_or] using h",
                  "  | some y =>",
                  f"    have e := tables_{w}{E_} pc y hw",
                  "    rw [h] at e; rw [Option.some_or]; exact e.symm", ""]
        else:
            t += [f"/-- `{w}`'s program (its own instructions and those of what it calls) is part of this one, unchanged. -/",
                  f"theorem has_{w} {BIND}: ∀ pc x, Code_{w}.prog pc = some x → {P_} pc = some x :=",
                  f"  fun pc x h => tables_{w}{E_} pc x h", ""]
elif calls:
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
if not NESTED:
    t += ["def prog (pc : Nat) : Option (Instr × Nat) := whole.lookup pc", "",
          "/-- The addresses the program has an instruction at. -/",
          "def keys : List Nat := whole.map (·.1)", "",
          "theorem keys_of : ∀ pc x, prog pc = some x → pc ∈ keys := fun pc x h => lookup_mem_keys whole pc x h", ""]
if calls and not NESTED:
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
t += [f"@[ode_at] theorem at_{at} {BIND}: {P_} 0x{at} = some ({ins}, 0x{nxt}) := rfl" for at, nxt, ins in rows]
t += ["", f"end Code_{name}", ""]
with open(out, "w") as f: f.write("\n".join(t))
