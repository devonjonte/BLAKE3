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
# and four real CPUs (Defs.lean's): an EPYC 9255, a Xeon 6330, an EPYC 7443, a Core 2. A failure on one of
# them is a refutation too, of the kind a test gives, where the prover named no CPU that confirms.
REAL = ["amd 0x00B00F21 0x7EDA320B 0xF1BF97A9 0xE7", "intel 0x000606A6 0x7FFEFBFF 0xF3BFB7EF 0xE7", "amd 0x00A00F11 0x7EDA320B 0x219C97A9 0x7", "intel 0x000106A5 0x0098E3BD 0 0"]
for n, cpu in enumerate(REAL):
    print(f"def real{n} : Cpu := {cpu}")
    print(f'#eval s!"witness agrees: {{agrees real{n}}}; code and rule: {{result real{n}}}; leaf1.eax {{real{n}.leaf1.eax}} leaf1.ecx {{real{n}.leaf1.ecx}} leaf7.ebx {{real{n}.leaf7.ebx}} xcr0 {{real{n}.xcr0}} amd {{(words real{n}).amd}} (a real CPU)"')

