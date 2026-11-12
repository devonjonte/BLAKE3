#!/usr/bin/env python3
"""The compiler's proofs for an AArch64 kernel, on Google DeepMind's model (their repository unchanged).

    gen_arm.py SOURCE NAME WORDS OUTDIR

SOURCE is the source file (hasher.ode) holding `kernel NAME on aarch64 { ... }` and its `contract NAME {
spec FILE; reads REG: v, ...; writes REG: EXPR, ... }`: 16-byte vectors read at REG and written at REG,
one after another. WORDS is a file of the assembled kernel's instruction words (hexadecimal, as the
object holds them). Writes into OUTDIR:

    Quiet_NAME.lean   the words, what the model's decoder makes of each (checked by Lean's kernel), and
                      NAME_quiet, NAME_observed: what an observer sees does not depend on what memory
                      holds or on the vector registers (Observer.lean)
    Proof_NAME.lean   NAME_spec (the contract's clauses as a Spec of their logic) and NAME_ok:
                      subroutineOk of their logic, by their tactics and bit-blasting for the values

A kind of instruction with no recipe here stops the generator: nothing is written. Needs `lake` in this
folder (to ask the model's decoder what each word is)."""
import re, subprocess, sys, tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
sys.path.insert(0, str(here.parent / "lang"))
import odec  # the source's reader


def decoded(words):
    """Each word as the model's decoder reads it, as a Lean term."""
    body = "import Arm64\nopen Arm64\n#eval IO.println (String.intercalate \"\\n@@\\n\" ([" + ", ".join(f"0x{w}#32" for w in words) + \
        "].map fun w => match decode w with | some i => s!\"{repr i}\" | none => \"NONE\"))\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=here, delete=False) as f:
        f.write(body); name = f.name
    try:
        r = subprocess.run(["lake", "env", "lean", name], cwd=here, capture_output=True, text=True, timeout=900)
    finally:
        Path(name).unlink(missing_ok=True)
    if r.returncode != 0:
        sys.exit("the decoder could not be asked:\n" + r.stdout[-2000:] + r.stderr[-2000:])
    out = [re.sub(r"\s+", " ", x).strip() for x in r.stdout.split("@@")]
    if len(out) != len(words) or "NONE" in out:
        sys.exit(f"the model's decoder does not decode word {out.index('NONE') if 'NONE' in out else '?'}")
    return out


REG_ONLY = ("Arm64.Instr.simdImmShift ", "Arm64.Instr.simdThreeSame ", "Arm64.Instr.simdPermute ")
PAIR = re.compile(r"Arm64\.Instr\.(ldpSimd|stpSimd) \(Arm64\.SimdMemSize\.Q128\) \S+ \S+ \(Arm64\.AddrMode\.Offset \(Arm64\.Reg\.gpr \S+\) \S+\)$")


def quiet(name, words, ins):
    t = f"""import Observer
open Arm64

/-! # `{name}` shows nothing of what memory holds or of the vector registers

Written by `gen_arm.py` from the assembled kernel's {len(words)} instruction words. To be read: `{name}_words`
and the two theorems' statements; `Observer.lean` says what an observer sees. Axioms: Lean's three. -/

set_option maxRecDepth 100000

/-- The kernel's instruction words, as assembled. -/
def {name}_words : List (BitVec 32) := [{', '.join('0x' + w for w in words)}]

"""
    steps, seen = [], []
    for k, (w, i) in enumerate(zip(words, ins)):
        t += f"theorem {name}.d{k} : decode 0x{w}#32 = some ({i}) := by decide +kernel\n"
        last = k == len(words) - 1
        if i.startswith(REG_ONLY) and not last:
            t += f"theorem {name}.p{k} : RegOnly ({i}) := fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩\n"
            steps.append(f"  refine cons_reg {name}.d{k} {name}.p{k} (fun _ => rfl) h ?_; intro s s' h\n")
        elif PAIR.match(i) and not last:
            steps.append(f"  refine cons_{'ldp' if 'ldpSimd' in i else 'stp'} {name}.d{k} h ?_; intro s s' h\n")
        elif i.startswith("Arm64.Instr.ret ") and last:
            steps.append(f"  exact cons_ret {name}.d{k} h\n")
        else:
            sys.exit(f"{name}: no recipe for instruction {k} ({i}): nothing written")
        seen.append(f"  refine seen_cons {name}.d{k} (fun _ => rfl) ?_\n")
    t += f"""
/-- **While `{name}` runs, two machines that agree on everything but what memory holds and the vector
registers show the same.** -/
theorem {name}_quiet (s s' : State) (h : Agree s s') : runObs {name}_words s = runObs {name}_words s' := by
  unfold {name}_words
{''.join(steps)}
/-- **The observer has an account of every one of its instructions**: something is always seen, so the
theorem above is not about two runs both unobserved. -/
theorem {name}_observed : ∀ s : State, (runObs {name}_words s).isSome := by
  unfold {name}_words
{''.join(seen)}  exact fun _ => rfl

#print axioms {name}_quiet
#print axioms {name}_observed
"""
    return t


def cells(base, k, value, lo="BitVec.extractLsb' 0 64", hi="BitVec.extractLsb' 64 64"):
    """A 16-byte vector at `base + 16 k`, as the two 64-bit cells their logic steps on."""
    a = base if k == 0 else f"({base} + {16 * k}#64)"
    return f"({a} ↦₆₄ {lo} {value} ∗ ({a} + 8#64) ↦₆₄ {hi} {value})"


def proof(name, words, contract):
    rreg, reads = contract["reads"]
    wreg, writes = contract["writes"]
    olds = [f"d{k}" for k in range(len(writes))]
    sub = lambda e: re.sub(r"\b(" + "|".join(reads) + r")\b", r"x.\1", e)
    v128 = lambda base, k, v: f"({base if k == 0 else f'({base} + {16 * k}#64)'} ↦₁₂₈ {v})"
    pre = " ∗\n    ".join([f"⌜s0.readReg64 .{wreg} = x.dst ∧ s0.readReg64 .{rreg} = x.src⌝"] +
                           [v128("x.src", k, f"x.{v}") for k, v in enumerate(reads)] +
                           [v128("x.dst", k, f"x.{v}") for k, v in enumerate(olds)])
    post = " ∗\n    ".join([v128("x.src", k, f"x.{v}") for k, v in enumerate(reads)] +
                            [v128("x.dst", k, f"({sub(e)})") for k, e in enumerate(writes)])
    target = " ∗\n    ".join([cells("x.src", k, f"x.{v}") for k, v in enumerate(reads)] +
                              [cells("x.dst", k, f"({sub(e)})") for k, e in enumerate(writes)])
    gens = "\n".join(f"      generalize x.{v} = {v}" for v in reads)
    fields = "\n".join(f"  {f} : BitVec {n}" for f, n in [("dst", 64), ("src", 64)] + [(v, 128) for v in reads + olds])
    return f"""import Arm64
import ProofLib
import WpKernel
import {contract["spec"]}
open Arm64 ProofLib

/-! # `{name}` meets its contract, on Google DeepMind's AArch64 model

Written by `gen_arm.py` from the source's contract clauses and the assembled kernel's {len(words)} words. To be
read: `{name}_spec` and the theorem's statement. `{name}_ok`: in any program holding these words at the
symbol, their `subroutineOk`: a call returns to its caller, the stack pointer and callee-saved registers
as they were, memory as the contract says and otherwise as it was. Their tactics run the instructions;
the values are settled by unfolding the specification (`kernel_spec`) and `bv_decide`. -/

set_option maxRecDepth 200000

structure {name}_args where
{fields}

/-- The contract's clauses: vectors read at `{rreg}`, written at `{wreg}`. -/
abbrev {name}_spec : Spec {name}_args where
  pre := fun x s0 =>
    {pre}
  post := fun x _ _ =>
    {post}

def {name}_code : FnCode :=
  .ofFn "b3l_{name}"
    "{' '.join(words)}"

set_option maxHeartbeats 4000000 in
theorem {name}_ok (prog : Program) (h_code : {name}_code.holds prog) :
    prog.subroutineOk "b3l_{name}" {name}_spec := by
  wp_init x s0
  simp only [pointsTo128] at hpre ⊢
  wp_steps
  refine SepWP.of_eq (P' :=
    {target}) ?values ?rest
  case values =>
    repeat' (first | with_reducible rfl | apply sepConj_congr | apply pointsTo64_congr_val)
    all_goals (
      simp only [forIn_range8_yield, bind_pure, Id.run_pure, Nat.reduceMul, Nat.reduceAdd, kernel_spec]
{gens}
      bv_decide)
  case rest =>
    wp_done

#print axioms {name}_ok
"""


def main():
    src, name, wordfile, outdir = sys.argv[1:5]
    words = Path(wordfile).read_text().split()
    odec.kernels(odec.contracts_of(Path(src).read_text())[2])
    contract = [c for c in odec.contracts if c["name"] == name]
    if len(contract) != 1 or not all(k in contract[0] for k in ("spec", "reads", "writes")):
        sys.exit(f"{src}: no `contract {name}` with spec, reads and writes")
    ins = decoded(words)
    q, p = quiet(name, words, ins), proof(name, words, contract[0])
    with open(Path(outdir) / f"Quiet_{name}.lean", "w") as f:
        f.write(q)
    with open(Path(outdir) / f"Proof_{name}.lean", "w") as f:
        f.write(p)
    print(f"{name}: {len(words)} instructions; wrote Quiet_{name}.lean and Proof_{name}.lean")


if __name__ == "__main__":
    main()
