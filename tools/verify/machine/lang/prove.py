#!/usr/bin/env python3
"""The compiler's other output: the proof that a kernel's bytes meet its contract.

usage: prove.py SOURCE.ode NAME LIFTED.lean.rows BASE OUTDIR

For a `kernel NAME` of the source with a `contract NAME { spec M; reads REG: v0, v1, ...; writes
REG: e0, e1, ... }` this writes, in OUTDIR:

  Code_NAME.lean    the instructions as the lifter read them from the assembled object (LIFTED.rows),
                    with one lemma an address;
  Proof_NAME.lean   the theorem and its proof: from any state with the vectors v0, v1, ... at REG and
                    16 * n bytes owned at the writes' REG, apart from the return address, the code
                    returns, the written vectors are e0, e1, ..., no other byte changes, the registers
                    a callee keeps are kept, and what an observer sees is one list fixed by the two
                    addresses, the stack pointer and the return address, whatever the vectors hold.

The proof is a recipe, the same for every straight-line kernel that loads before it stores: run the
instructions symbolically with the observer beside the machine, let `rfl` find the trace (it fails if
the trace mentions a secret), and give each written vector's equation to `bv_decide`. Lean checks the
result; nothing here is trusted."""
import re, sys

src, name, rows_path, base, out = sys.argv[1:6]
base = int(base, 0)
text = open(src).read()
m = re.search(r"^contract\s+" + name + r"\s*\{(.*?)^\}", text, re.M | re.S)
assert m, f"no contract for {name}"
contract = {}
for line in m.group(1).splitlines():
    line = line.split("//")[0].strip()
    if not line: continue
    key, rest = line.split(None, 1)
    if key == "spec": contract["spec"] = rest.strip()
    else:
        reg, items = rest.split(":", 1)
        contract[key] = (reg.strip(), [x.strip() for x in items.split(",")])
rreg, reads = contract["reads"]
wreg, writes = contract["writes"]
rows = [l.rstrip("\n").split("\t") for l in open(rows_path)]
n = len(rows)
cap = name.capitalize()

# ---- the code ----
code = [f"import Machine", "import Lean", "", f"/-! The kernel `{name}` as assembled: {n} instructions at 0x{base:X}. Written by prove.py from the lifter's rows. -/", "",
        f"/-- The lemmas that say which instruction of `{name}` is at which address. -/", f"register_simp_attr {name}_at", ""]
code_defs = ["import Machine", f"import Attr_{name}", "open X86", "", f"namespace Code_{name}", "", "def table : List (Nat × Instr × Nat) := ["]
code_defs += [f"  (0x{at}, {ins}, 0x{nxt}){',' if i + 1 < n else ''}" for i, (at, nxt, ins) in enumerate(rows)]
code_defs += ["]", "", "def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc", ""]
code_defs += [f"@[{name}_at] theorem at_{at} : prog 0x{at} = some ({ins}, 0x{nxt}) := rfl" for at, nxt, ins in rows]
code_defs += ["", f"end Code_{name}", ""]
with open(f"{out}/Attr_{name}.lean", "w") as f:
    f.write(f"import Lean\n\n/-- The lemmas that say which instruction of `{name}` is at which address. -/\nregister_simp_attr {name}_at\n")
with open(f"{out}/Code_{name}.lean", "w") as f:
    f.write("\n".join(code_defs))

# ---- the proof ----
k = len(writes)
vs = [f"v{i}" for i in range(k)]
def mem(upto, names=vs):
    t = "mem"
    for i in range(upto):
        t = f"({t}.put128 (out + {16 * i}) {names[i]})"
    return t
P = []
P += ["import Machine", "import MemLemmas", "import Observer", f"import {contract['spec']}", f"import Code_{name}", "open X86", "",
      f"/-! # The kernel `{name}` meets its contract", "",
      f"Written by prove.py from the contract in the source. The statement is the contract; the proof is the",
      "recipe for a straight-line kernel. Lean checks both. -/", "",
      "theorem vec_as {m : Mem} {a : BitVec 64} {v w : V} (h : Vec m a v) (e : v = w) : Vec m a w := e ▸ h", ""]
# the written vectors are where they were put, and nothing else changed
for j in range(k):
    P += [f"theorem put_{j} (mem : Mem) (out : BitVec 64) ({' '.join(vs)} : V) : Vec {mem(k)} (out + {16 * j}) v{j} := by"]
    step = f"vec_put128 {mem(j)} (out + {16 * j}) v{j}"
    for i in range(j + 1, k):
        step = f"vec_congr (fun x hx => put128_other _ _ _ x (by bv_omega)) ({step})"
    P += [f"  exact {step}", ""]
P += [f"theorem put_frame (mem : Mem) (out : BitVec 64) ({' '.join(vs)} : V) (x : BitVec 64) (hx : {16 * k} ≤ (x - out).toNat) :",
      f"    {mem(k)} x = mem x := by",
      "  rw [" + ", ".join("put128_other _ _ _ _ (by bv_omega)" for _ in range(k)) + "]", ""]
regs = "rax rcx rdx rbx rsp_ rbp rsi_ rdi_ r8 r9 r12 r13 r14 r15".split()
names = {"rdi": "rdi_", "rsi": "rsi_"}
P += ["set_option maxRecDepth 100000 in",
      f"macro \"run_{name}\" \"[\" hs:Lean.Parser.Tactic.simpLemma,* \"]\" : tactic => `(tactic|",
      "  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [stepsL_mk, stepsL_zero, stepL, touched, srcObs, opObs, branches,",
      f"    step, src, X86.read, write, State.get, State.set, State.xmm, State.setx, trunc, {name}_at,",
      "    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp, Option.isSome_some,",
      "    List.nil_append, List.cons_append, List.append_nil,",
      "    Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte, reduceCtorEq, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceEq, BitVec.reduceBEq,",
      "    BitVec.reduceAnd, BitVec.reduceSetWidth, Bool.false_eq_true, Bool.true_eq_false, Bool.false_and, Bool.true_and,",
      "    Bool.not_true, Bool.not_false, $hs,*])", ""]
rd = " → ".join(f"Vec s.mem (inp + {16 * i}) {v}" for i, v in enumerate(reads))
ow = " → ".join(f"Owned16 s.mem (out + {16 * i})" for i in range(k))
post_vecs = " ∧\n      ".join(f"Vec S.core.mem (out + {16 * j}) ({e})" for j, e in enumerate(writes))
P += ["set_option maxRecDepth 1000000 in", "set_option maxHeartbeats 0 in",
      f"/-- **The {n} instructions of `{name}` meet its contract.** Called with the address of {16 * len(reads)} bytes in {rreg.upper()} (the vectors",
      f"{', '.join(reads)}) and of {16 * k} owned bytes in {wreg.upper()}, the return address on the stack and apart from those {16 * k} bytes: it returns",
      f"there with the stack pointer popped and the registers a callee keeps as they were; the {16 * k} bytes are",
      f"{', '.join(writes)}; no other byte of memory changes;",
      f"and what an observer sees is `L`, a list fixed by the two addresses, the stack pointer and the return address,",
      f"whatever {', '.join(reads)} are. -/",
      f"theorem {name}_meets_its_contract (out inp rsp ra : BitVec 64) : ∃ L : List Obs, ∀ (s : State) ({' '.join(reads)} : V),",
      f"    s.pc = 0x{base:X} → s.{wreg} = out → s.{rreg} = inp → s.rsp = rsp →",
      f"    {rd} →", f"    {ow} →",
      f"    s.mem.read rsp 64 = some ra → (∀ x, (x - rsp).toNat < 8 → {16 * k} ≤ (x - out).toNat) →",
      f"    ∃ S, stepsL Code_{name}.prog {n} ⟨s, []⟩ = some S ∧ S.leak = L ∧",
      "      S.core.pc = ra.toNat ∧ S.core.rsp = rsp + 8 ∧",
      "      S.core.rbx = s.rbx ∧ S.core.rbp = s.rbp ∧ S.core.r12 = s.r12 ∧ S.core.r13 = s.r13 ∧ S.core.r14 = s.r14 ∧ S.core.r15 = s.r15 ∧",
      f"      {post_vecs} ∧",
      f"      (∀ x, {16 * k} ≤ (x - out).toNat → S.core.mem x = s.mem x) := by",
      "  refine ⟨?L, ?_⟩", "  rotate_left",
      f"  intro s {' '.join(reads)} hpc hout hinp hsp {' '.join(f'hr{i}' for i in range(len(reads)))} {' '.join(f'ho{i}' for i in range(k))} hret hapart",
      "  obtain ⟨rax, rcx, rdx, rbx, rsp_, rbp, rsi_, rdi_, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s",
      f"  simp only at hpc hout hinp hsp {' '.join(f'hr{i}' for i in range(len(reads)))} {' '.join(f'ho{i}' for i in range(k))} hret hapart",
      f"  subst pc {names[wreg]} {names[rreg]} rsp_"]
for i in range(len(reads)):
    P += [f"  have r{i} := read_vec hr{i}"]
for j in range(k):
    binders = " ".join(vs[:j] + ["v"])
    own = f"ho{j}"
    for _ in range(j):
        own = f"(owned16_put128 _ _ _ _ {own})"
    P += [f"  have w{j} : ∀ {binders} : V, {mem(j)}.write128 (out + {16 * j}) v = some ({mem(j)}.put128 (out + {16 * j}) v) :=",
          f"    fun {binders} => write_vec {own} v"]
P += [f"  have rr : ∀ {' '.join(vs)} : V, {mem(k)}.read rsp 64 = some ra := by",
      f"    intro {' '.join(vs)}",
      "    rw [read_congr (m := mem) _ (fun x hx => by",
      "      have := hapart x hx",
      "      rw [" + ", ".join("put128_other _ _ _ _ (by bv_omega)" for _ in range(k)) + "])]",
      "    exact hret",
      f"  run_{name} [{', '.join([f'r{i}' for i in range(len(reads))] + [f'w{j}' for j in range(k)] + ['rr'])}]",
      "  refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, " + ", ".join("?_" for _ in range(k)) + ", ?_⟩",
      "  · simp only []", "    rfl"]
for j in range(k):
    P += [f"  · refine vec_as (put_{j} _ _ " + " ".join("_" for _ in range(k)) + ") ?_",
          "    simp only [Hex.hex8, Hex.hi, Hex.lo, Hex.hexc, paddb, pcmpgtb, gtb, punpcklbw, punpckhbw, psrlw, by8, w16]",
          "    bv_decide (config := { timeout := 900 })"]
P += ["  · intro x hx", "    exact put_frame _ _ " + " ".join("_" for _ in range(k)) + " x hx", "",
      f"#print axioms {name}_meets_its_contract", ""]
with open(f"{out}/Proof_{name}.lean", "w") as f:
    f.write("\n".join(P))
print(f"{name}: {n} instructions; wrote Attr_{name}.lean, Code_{name}.lean, Proof_{name}.lean")
