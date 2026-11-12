#!/usr/bin/env python3
"""Try a function on its examples: run the machine model on each and compare with the contract.

usage: try_fn.py SOURCE.ode NAME ROWS      (after `lake build Code_NAME Example_NAME Checks`)

The function's contract (Lean, `Spec_NAME.lean`) is read in parts by `#pieces` (Checks.lean); its examples
are `NAMESPACE.examples` in `Example_NAME.lean`, tuples of the contract's parameters. For each example
this builds a memory holding what the contract's pieces say, checks that the example meets what the
contract requires, runs the assembled function in the machine model, and checks what the contract
ensures. A layout `X.layout` is put into memory and tested by `X.sample` (`Sample_*.lean`).

One line an example:
    example I: meets the contract (N instructions)
    example I: REFUTED: WHAT (the code, or the contract, is wrong: this input shows it)
    example I: NOT AN EXAMPLE: WHAT (it does not meet what the contract requires)
    example I: NO VERDICT: ...
and a last line: `tried: A meet, B refuted, C not examples`. Exit status 0 only if at least one example
meets the contract's requirements and none is refuted. This is a test by running, not a proof."""
import re, subprocess, sys
import odec

src, name, rows_path = sys.argv[1:4]
clauses, _, _ = odec.contracts_of(open(src).read())
CNAME = re.match(r"[\w.]+", next(r for w, r in clauses[name]["head"] if w == "meets")).group(0)
NS = CNAME.rsplit(".", 1)[0]
ENTRY = int(open(rows_path).readline().split("\t")[0], 16)
with open(f"{name}.pieces.lean", "w") as f:
    f.write(f"import Checks\nimport Spec_{name}\n#pieces {CNAME}\n")
out = subprocess.run(["lake", "env", "lean", f"{name}.pieces.lean"], capture_output=True, text=True).stdout
params, pieces, accepts, returns = [], [], None, None
for line in out.splitlines():
    if line.startswith("param "): n, ty = line[6:].split(" : ", 1); params.append((n, ty))
    elif line.startswith("accepts "): accepts = line[8:]
    elif line.startswith(("read |", "update |")): pieces.append([x.strip() for x in line.split("|")])
    elif line.startswith("returns "): returns = [x.strip() for x in line[8:].split("|", 1)]
assert params and accepts is not None and returns, f"could not read {CNAME}:\n{out}"
sample = lambda layout: re.sub(r"\.layout$", ".sample", layout)
q = lambda s: s.replace("\\", "\\\\").replace('"', '\\"')
names = ", ".join(n for n, _ in params)
types = " × ".join(t for _, t in params)
pre = [f'("it accepts the arguments: {q(accepts)}", decide ({accepts}))', '("the stack and its pieces of memory are apart", Try.apart c)'] + \
      [f'("at the call {q(l)} at {q(a)} holds {q(v)}", {sample(l)}.check s0.mem ({a}) ({v}))' for _, l, a, v, _ in pieces]
def post_of(mem):
    return [f'("it returns what the contract says: {q(returns[1])}", decide ({returns[1]}))'] + \
       [f'("at the return {q(l)} at {q(a)} holds {q(w)}", {sample(l)}.check {mem} ({a}) ({w}))' for kind, l, a, _, w in pieces if kind == "update"]
post = post_of("s'.mem")
puts = "".join(f"    let m0 := {sample(l)}.put m0 ({a}) ({v})\n" for _, l, a, v, _ in pieces)
L = f"""import Try
import TrySem
import HasherOde
import Code_{name}
import Example_{name}
open X86

/-! Written by try_fn.py from what `#pieces {CNAME}` read in the contract. A test by running, not a proof. -/

namespace Try_{name}

/-- The same example through the source's meaning: who is at fault when the assembled code breaks the contract. -/
def blame : {types} → Mem → String
  | ({names}), m0 =>
    let c := {CNAME} {' '.join(n for n, _ in params)}
    match Try.source Ode.{name} c.args m0 with
    | none => "The source traps on it too (or does not end): the source or the contract is wrong."
    | some ({returns[0]}, m') =>
      let m0' : Mem := fun x => some ((m0 x).getD 0)
      let post : List (String × Bool) := [{', '.join(post_of("m'"))}] ++
        [("memory the function only reads is unchanged", c.reads.all fun p => Try.sameBytes m0' m' p.addr p.size.toNat),
         ("the bytes beside its pieces are unchanged", c.regions.all fun r => Try.sameBytes m0' m' (r.1 - 64#64) 64 && Try.sameBytes m0' m' (r.1 + r.2) 64)]
      match Try.firstFailure post with
      | some f => s!"The source breaks the contract on it too (not so: {{f}}): the source or the contract is wrong."
      | none => "The source keeps the contract on it: the code the compiler made is wrong."

def one (i : Nat) : {types} → String
  | ({names}) =>
    let c := {CNAME} {' '.join(n for n, _ in params)}
    let m0 : Mem := fun _ => none
{puts}    let s0 := Try.start c 0x{ENTRY:X} m0
    let pre : List (String × Bool) := [{', '.join(pre)}]
    match Try.firstFailure pre with
    | some f => s!"example {{i}}: NOT AN EXAMPLE: not so: {{f}}"
    | none =>
      match Try.run Code_{name}.prog Try.returnAddress.toNat (Try.owned c) 100000 0 s0 with
      | .faulted pc n => s!"example {{i}}: REFUTED: after {{n}} instructions {{Try.why Code_{name}.prog pc}}. {{blame ({names}) s0.mem}}"
      | .outOfFuel _ => s!"example {{i}}: NO VERDICT: still running after 100000 instructions (a loop that does not end?)"
      | .returned s' n =>
        let {returns[0]} := s'.rax
        let post : List (String × Bool) := Try.returnChecks c s0 s' ++ [{', '.join(post)}]
        match Try.firstFailure post with
        | some f => s!"example {{i}}: REFUTED: not so: {{f}} (it returned after {{n}} instructions). {{blame ({names}) s0.mem}}"
        | none => s!"example {{i}}: meets the contract ({{n}} instructions)"

/-- Each example in turn; the first that does not meet the contract is enough. -/
def all : List ({types}) → Nat → IO Unit
  | [], _ => pure ()
  | e :: rest, i => do
    let line := one i e
    IO.println line
    if (line.splitOn "meets the contract").length > 1 || (line.splitOn "NOT AN EXAMPLE").length > 1 then all rest (i + 1)

#eval all {NS}.examples 0

end Try_{name}
"""
with open(f"Try_{name}.lean", "w") as f: f.write(L)
pr = subprocess.Popen(["lake", "env", "lean", f"Try_{name}.lean"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
try:
    so, se = pr.communicate(timeout=240)
except subprocess.TimeoutExpired:
    import os, signal
    os.killpg(pr.pid, signal.SIGKILL); pr.communicate()
    print("tried: NO VERDICT: the examples ran for more than 240 s"); sys.exit(1)
class r: stdout, stderr, returncode = so, se, pr.returncode
lines = [l for l in r.stdout.splitlines() if l.startswith("example ")]
for l in r.stdout.splitlines() + r.stderr.splitlines():
    if l.startswith("example ") or "error" in l: print(l)
meet = sum("meets the contract" in l for l in lines); ref = sum("REFUTED" in l for l in lines); bad = sum("NOT AN EXAMPLE" in l for l in lines)
print(f"tried: {meet} meet, {ref} refuted, {bad} not examples" + ("" if lines else " (the examples did not run)"))
sys.exit(0 if (meet > 0 and ref == 0 and r.returncode == 0) else 1)
