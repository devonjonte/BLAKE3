#!/usr/bin/env python3
"""Where does a generated proof stop? Every goal it leaves, in one run of Lean.

    trace_proof.py NAME [CONTEXT]        (after prove_fn.sh NAME has written Proof_NAME.lean; run from lang/)

A generated proof settles what a lemma or a callee's contract asks with one tactic for all of it
(`apply LEMMA <;> mem_auto`, `all_goals (first | ...)`), so when Lean refuses, the message is that tactic's
last attempt on some goal, often a solver's counterexample that says nothing of which goal it was. This writes
Trace_NAME.lean, the same proof with each such place changed to: try the tactic on every goal, and where it
does not settle one, print that goal and go on. Then it runs Lean once and prints, for each goal left: the
line of the proof, the goal, and the hypotheses that mention what the goal mentions (CONTEXT of them at most,
12 unless said). Nothing is proved by this: the traced proof has `sorry` where it stopped."""
import re, subprocess, sys

name = sys.argv[1]
context = int(sys.argv[2]) if len(sys.argv) > 2 else 12
src = open(f"Proof_{name}.lean").read().splitlines()
out = []
for line in src:
    m = re.match(r"^(\s*)((?:· )?)apply ([\w.]+) <;> mem_auto\s*$", line)
    if m:
        ind, dot, lemma = m.groups()
        body = ind + ("  " if dot else "")
        out += [f"{ind}{dot}apply {lemma}", f"{body}all_goals first | (mem_auto; done) | (trace_state; sorry)"]
        continue
    m = re.match(r"^(\s*)all_goals \(first \| mem_auto \| \(apply_frame <;> mem_auto\) \| .*\)\s*$", line)
    if m:
        # what a callee's contract asks of memory: where no way settles a goal, the lemma is applied all the same
        # and the goals it leaves are printed (the one that fails is then named, not the whole)
        ind = m.group(1)
        out.append(f"{ind}all_goals first | (({line.strip()[len('all_goals ('):-1]}); done) | "
                   f"((first | apply_frame | apply_intro | skip); all_goals first | ((first | mem_auto | (apply_frame <;> mem_auto)); done) | (trace_state; sorry))")
        continue
    m = re.match(r"^(\s*)all_goals \((first \| .*)\)\s*$", line)
    if m:
        out.append(f"{m.group(1)}all_goals first | (({m.group(2)}); done) | (trace_state; sorry)")
        continue
    m = re.match(r"^(\s*)all_goals bv_decide\s*$", line)
    if m:
        out.append(f"{m.group(1)}all_goals first | (bv_decide; done) | (trace_state; sorry)")
        continue
    m = re.match(r"^(\s*)((?:· )?)first \| \(apply .*\)\s*$", line)       # `by A | B`: none applied
    if m:
        out.append(f"{m.group(1)}{m.group(2)}first | ({line.strip().removeprefix('· ')}) | (trace_state; sorry)")
        continue
    out.append(line.replace(f"namespace Proof_{name}", f"namespace Trace_{name}").replace(f"end Proof_{name}", f"end Trace_{name}"))
with open(f"Trace_{name}.lean", "w") as f:
    f.write("\n".join(out) + "\n")
r = subprocess.run(["lake", "env", "lean", f"Trace_{name}.lean"], capture_output=True, text=True)
text = r.stdout + r.stderr
with open(f"Trace_{name}.out", "w") as f: f.write(text)       # Lean's whole answer, to look into
# Lean prints an error with its place (FILE:LINE:COL: error: ...) and a trace_state as the goal alone: its
# hypotheses, one a name, then "⊢ goal". Both end at the next message or the next goal's first hypothesis.
lines = text.split("\n")
HEAD = re.compile(r"^Trace_\w+\.lean:(\d+):\d+: (error|warning)")
IGNORE = {"BitVec", "true", "false", "some", "x", "Mem", "error", "lean", "hypothesis", "of", "could", "not", "be", "shown", "m",
          "Tactic", "failed", "Trace_" + name}
def names(s): return set(re.findall(r"[A-Za-z_][\w.]*", s)) - IGNORE
def hyps_before(k):
    """The hypotheses above line k (a goal's `⊢`), each joined to one line."""
    j = k
    while j > 0 and lines[j - 1].strip() and not HEAD.match(lines[j - 1]) and not lines[j - 1].startswith("⊢"): j -= 1
    items = []
    for l in lines[j:k]:
        if re.match(r"^[^\s:]+(?: [^\s:]+)* :( |$)", l) or l.startswith("case "): items.append(l)
        elif items: items[-1] += " " + l.strip()
    return [h for h in items if not h.startswith("case ")]
def show(hyps, about):
    near = [h for h in hyps if names(h.split(" : ", 1)[-1]) & about and not re.match(r"^(x\d+|sv|fb|ra|zf|cf|[a-z]\w*( \w+)+) :", h)]
    for h in near[-context:]: print("    " + " ".join(h.split())[:300])
left, k = 0, 0
while k < len(lines):
    l = lines[k]
    m = HEAD.match(l)
    if m and m.group(2) == "error" and "sorry" not in l:
        # an error stops its branch: its text (to the hypotheses), then the hypotheses that mention what it names
        e = k + 1
        while e < len(lines) and lines[e].strip() and not HEAD.match(lines[e]) and not re.match(r"^[^\s:]+(?: [^\s:]+)* : ", lines[e]) and not lines[e].startswith("case "): e += 1
        print("\n".join(x[:300] for x in lines[k:e]))
        g = e
        while g < len(lines) and not lines[g].startswith("⊢") and not HEAD.match(lines[g]): g += 1
        if g < len(lines) and lines[g].startswith("⊢"):
            print("  " + lines[g][:300]); show(hyps_before(g), names(" ".join(lines[k:e]) + lines[g]))
            k = g
        print()
    elif l.startswith("⊢"):
        e = k + 1
        while e < len(lines) and lines[e].startswith(" "): e += 1
        goal = " ".join(x.strip() for x in lines[k:e])
        left += 1
        print(f"--- goal {left} left:\n{goal[:1200]}"); show(hyps_before(k), names(goal)); print()
        k = e - 1
    k += 1
print(f"{name}: {left} goal(s) left by the generated proof" + ("" if left else " (Lean's errors, if any, are above)"))
