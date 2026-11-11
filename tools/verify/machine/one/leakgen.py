#!/usr/bin/env python3
"""Write the observer's versions of merge's segment lemmas from the proved ones (MergeTurn.lean,
MergeWhole.lean): the same hypotheses and the same symbolic run, with the trace recorded. Pass 1
(`probe`) asks Lean what each segment shows; pass 2 (`final`) states it as a definition, which
compiles only if the trace mentions public values alone, and proves it.
usage: leakgen.py probe; lake env lean LeakProbe.lean > probe.out; leakgen.py extract; leakgen.py final"""
import re, subprocess, sys, pathlib
here = pathlib.Path(__file__).resolve().parent
SEG = {  # name: (file, steps, public arguments of the trace)
    "pre_avx": ("MergeTurn.lean", 52, "self arr keyp fp len"),
    "pre_sse": ("MergeTurn.lean", 52, "self arr keyp fp len"),
    "post_avx": ("MergeTurn.lean", 12, "self arr fp oL"),
    "post_sse": ("MergeTurn.lean", 13, "self arr fp oL"),
    "prologue": ("MergeWhole.lean", 24, "self p rsp0 fp"),
    "epilogue": ("MergeWhole.lean", 8, "rsp0 ra"),
}

def theorem(text, name):
    """(binders, conclusion, body) of `theorem name ... : concl := by body`."""
    a = text.index(f"theorem {name} ")
    b = min(x for x in (text.find("\nset_option", a), text.find("\n/--", a), text.find("\nend MergeCode", a), text.find("\n#print", a), len(text)) if x > 0)
    block = text[a:b]
    i = block.index(" :\n    ∃ s', steps Code.prog")
    j = block.index(":= by\n", i)
    return block[len(f"theorem {name} "):i], block[i + 3:j].strip(), block[j + 6:]

def state_of(concl):
    m = re.match(r"∃ s', steps Code\.prog (\d+) (⟨.*?⟩) = some s' ∧", concl, re.S)
    return int(m.group(1)), m.group(2)

def body_for_leak(body, closing, steps):
    """The original proof up to its run, with the observer's run and `closing` after it."""
    out, cases = [], body.count("  by_cases hz : n - 1#64 = 0#64")
    lines = body.rstrip("\n").split("\n")
    k = 0
    while k < len(lines):
        line = lines[k]
        if line.strip().startswith("show ∃ s', steps Code.prog"):
            # the state with the memory folded into `mm`: the same for the recorded run
            m = re.search(r"(⟨.*⟩) = some s' ∧ _", line)
            out.append(line[:len(line) - len(line.lstrip())] + f"show ∃ S, stepsL Code.prog {steps} ⟨{m.group(1)}, []⟩ = some S ∧ _")
        elif line.strip().startswith("rw [if_pos hz]") or line.strip().startswith("rw [if_neg hz]"):
            pass
        elif line.strip().startswith("rw [hm]"):
            out.append(line)
        elif line.strip().startswith("run_merge ["):
            ind = line[:len(line) - len(line.lstrip())]
            out.append(line.replace("run_merge [", "run_merge_leak ["))
            out += [ind + c for c in closing]
            # skip the original closing of this branch
            k += 1
            while k < len(lines) and not lines[k].startswith("  · ") and not (lines[k].startswith("  ") and not lines[k].startswith("   ") and cases == 0 and False):
                if cases and lines[k].startswith("  · "): break
                k += 1
            continue
        else:
            out.append(line)
        k += 1
    return "\n".join(out) + "\n"

def main():
    mode = sys.argv[1]
    texts = {f: (here / f).read_text() for f in ("MergeTurn.lean", "MergeWhole.lean")}
    lists = {}
    if mode == "final":
        for line in (here / "leak-probe.txt").read_text().splitlines():
            name, lst = line.split("\t", 1); lists.setdefault(name, []).append(lst)
    out = ["import MergeWhole", "import Leak", "open X86", "", "namespace MergeCode", "",
           "/-! What each part of `merge` shows an observer. Written by leakgen.py from the proved parts. -/", "",
           "set_option maxRecDepth 100000 in",
           "/-- `run_merge`, with the observer. -/",
           'macro "run_merge_leak" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|',
           "  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) (disch := decide) only [stepsL_mk, stepsL_zero, stepL, touched, srcObs, opObs, branches,",
           "    List.nil_append, List.cons_append, List.append_nil,",
           "    steps_mk, steps_zero, step, src,",
           "    X86.read, write, State.get, State.set, State.xmm, State.setx, trunc, merge_at,",
           "    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp, Option.isSome_some,",
           "    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq,",
           "    Mem.read8, Mem.write8, upd_apply, none_apply, Option.some_or, Option.none_or,",
           "    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceEq,",
           "    BitVec.reduceBEq, BitVec.reduceULT, BitVec.reduceSetWidth, BitVec.reduceShiftLeft, BitVec.reduceHShiftLeft, BitVec.xor_self,",
           "    BitVec.or_zero, BitVec.zero_or,",
           "    Nat.reduceAdd, Nat.reduceMul, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, Bool.or_false, Bool.false_or,",
           "    Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_self,",
           "    zmask8, zmask8', byte_zext, cat_by8, unbyte64, BitVec.reduceNeg, Option.isSome_or, Bool.true_or, Bool.or_true, and_self, and_true, $hs,*])", ""]
    if mode == "probe":
        out += ["def hideL (l : List Obs) : List Obs := l", ""]
    for name, (f, steps, public) in SEG.items():
        binders, concl, body = theorem(texts[f], name)
        n, state = state_of(concl)
        assert n == steps, (name, n)
        post = name.startswith("post")
        if mode == "probe":
            closing = ["refine ⟨_, rfl, ?_⟩", "simp only []", "trace_state", "rfl"]
            out += ["set_option maxRecDepth 1000000 in", "set_option maxHeartbeats 0 in", "set_option pp.deepTerms true in", "set_option pp.maxSteps 10000000 in", "set_option pp.oneline false in",
                    f"theorem {name}_probe {binders} :\n    ∃ S, stepsL Code.prog {steps} ⟨{state}, []⟩ = some S ∧ S.leak = hideL S.leak := by",
                    body_for_leak(body, closing, steps)]
        else:
            ls = lists[name]
            args = " ".join(public.split())
            if post:
                assert len(ls) == 2
                out += [f"/-- What this part shows: `last` when no turn is left. -/",
                        f"def {name}_shows ({args} : BitVec 64) (last : Bool) : List Obs :=\n  if last then {ls[0]}\n  else {ls[1]}", ""]
                target = f"{name}_shows {args} (decide (n - 1#64 = 0#64))"
            else:
                assert len(ls) == 1
                out += [f"/-- What this part shows. -/", f"def {name}_shows ({args} : BitVec 64) : List Obs :=\n  {ls[0]}", ""]
                target = f"{name}_shows {args}"
            closing = ["refine ⟨_, rfl, ?_⟩", f"simp only [{name}_shows, hz, decide_true, decide_false, ↓reduceIte, if_true, if_false, Bool.false_eq_true]" if post else f"simp only [{name}_shows]", "try rfl"]
            out += ["set_option maxRecDepth 1000000 in", "set_option maxHeartbeats 0 in",
                    f"theorem {name}_leak {binders} :\n    ∃ S, stepsL Code.prog {steps} ⟨{state}, []⟩ = some S ∧ S.leak = {target} := by",
                    body_for_leak(body, closing, steps)]
    out += ["end MergeCode", ""]
    target = "LeakProbe.lean" if mode == "probe" else "MergeParts.lean"
    (here / target).write_text("\n".join(out))
    print("wrote", target)

def extract():
    """Lean's answer to the probe (`lake env lean LeakProbe.lean > probe.out`) -> leak-probe.txt: one line a
    goal, the part's name and the list it shows. A part that ends in a branch has two goals."""
    raw = (here / "probe.out").read_text()
    goals = [re.sub(r"\s+", " ", g).strip() for g in re.findall(r"^⊢ (\[.*?\]) =\n\s+hideL", raw, re.M | re.S)]
    names = [n for n in SEG for _ in range(2 if n.startswith("post") else 1)]
    assert len(goals) == len(names), (len(goals), len(names))
    (here / "leak-probe.txt").write_text("".join(f"{n}\t{g}\n" for n, g in zip(names, goals)))
    print("wrote leak-probe.txt:", len(goals), "lists")

if len(sys.argv) > 1 and sys.argv[1] == "extract":
    extract()
else:
    main()
