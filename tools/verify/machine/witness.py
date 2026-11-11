#!/usr/bin/env python3
"""A counterexample the prover names, run on the model. usage: witness.py BUILD.log > Witness.lean; lake env lean Witness.lean
bv_decide, when the theorem fails, prints an assignment of the CPU's words. This writes a Lean file that
builds that CPU and runs the code on it (`agrees` of Defs.lean): "false" there is a refutation that
does not rest on the prover, a CPU on which these bytes return something else."""
import re, sys
log = open(sys.argv[1]).read()
m = re.search(r"Consider the following assignment:\n((?:cpu\.\S+ = \d+#\d+\n)+)", log)
if not m:
    print("-- no assignment in the log"); print('#eval "no witness"'); sys.exit(0)
v = {k: int(x) for k, x in re.findall(r"cpu\.(\S+) = (\d+)#\d+", m.group(1))}
g = lambda k: v.get(k, 0)
leaf = lambda n: "⟨" + ", ".join(str(g(f"leaf{n}.{r}")) for r in ("eax", "ebx", "ecx", "edx")) + "⟩"
print("import Defs\nopen X86\n")
print(f"def witness : Cpu := ⟨{leaf(0)}, {leaf(1)}, {leaf(7)}, {g('xcr0')}⟩")
print('#eval s!"witness agrees: {agrees witness}; code and rule: {result witness}; leaf1.eax {witness.leaf1.eax} leaf1.ecx {witness.leaf1.ecx} leaf7.ebx {witness.leaf7.ebx} xcr0 {witness.xcr0} amd {(words witness).amd}"')
