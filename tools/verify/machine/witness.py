#!/usr/bin/env python3
"""The counterexamples the prover names, run on the model.
usage: witness.py BUILD.log > Witness.lean; lake env lean Witness.lean
bv_decide, where a goal of the theorem fails, prints an assignment of the CPU's words. This writes a Lean
file that builds each such CPU and runs the code on it (`agrees` of Defs.lean): "false" there is a
refutation that does not rest on the prover, a CPU on which these bytes return something else."""
import re, sys
log = open(sys.argv[1]).read()
blocks = re.findall(r"Consider the following assignment:\n((?:cpu\.\S+ = \d+#\d+\n)+)", log)
print("import Defs\nopen X86\n")
if not blocks: print('#eval "no witness"')
seen = set()
for n, block in enumerate(blocks):
    v = {k: int(x) for k, x in re.findall(r"cpu\.(\S+) = (\d+)#\d+", block)}
    g = lambda k: v.get(k, 0)
    leaf = lambda i: "⟨" + ", ".join(str(g(f"leaf{i}.{r}")) for r in ("eax", "ebx", "ecx", "edx")) + "⟩"
    cpu = f"⟨{leaf(0)}, {leaf(1)}, {leaf(7)}, {g('xcr0')}⟩"
    if cpu in seen: continue
    seen.add(cpu)
    print(f"def witness{n} : Cpu := {cpu}")
    print(f'#eval s!"witness agrees: {{agrees witness{n}}}; code and rule: {{result witness{n}}}; leaf1.eax {{witness{n}.leaf1.eax}} leaf1.ecx {{witness{n}.leaf1.ecx}} leaf7.ebx {{witness{n}.leaf7.ebx}} xcr0 {{witness{n}.xcr0}} amd {{(words witness{n}).amd}}"')
