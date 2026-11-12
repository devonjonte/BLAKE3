#!/usr/bin/env python3
"""The compiler's proof of a function, about its contract in bytes directly.

    direct_fn.py NAME OWN BYTES STACK MODULE FACT...

Proof_NAME.lean (written by prove_fn.py) proves `Abi.Meets … (OWN args)`, OWN being the model's own contract
(Spec_NAME.lean). This writes Direct_NAME.lean: the same proof text with `Abi.ofBytes (BYTES args) STACK`
(the contract that names no machine, ../spec, read for this machine) in OWN's place, and where the proof
unfolds the contract, `Abi.ofBytes`, BYTES and the FACTs (how a layout in bytes opens as the model's:
`X.opens` gives `X.opens.keeps`, `.turns`, `.fills`; any other name is used as it is) beside. MODULE holds
the facts. If Lean accepts it, the model's own contract was not needed: a trial of the way for it to go
(DESIGN.md, "Two architectures")."""
import re, sys
from pathlib import Path

name, own, bytes_, stack, module = sys.argv[1:6]
facts = []
for f in sys.argv[6:]:
    facts += [f"{f}.keeps", f"{f}.turns", f"{f}.fills"] if f.endswith(".opens") else [f]
text = Path(f"Proof_{name}.lean").read_text()
esc = re.escape(own)
text, n = re.subn(r"\(" + esc + r" ([^()]*)\)", lambda m: f"(Abi.ofBytes ({bytes_} {m.group(1)}) {stack}#64)", text)
unfold = ", ".join(["Abi.ofBytes", bytes_] + facts)
text, k = re.subn(r"simp only \[" + esc + r"([,\]])", lambda m: f"simp only [{unfold}{m.group(1)}", text)
text, d = re.subn(r"dsimp only \[" + esc + r"\]", f"dsimp only [Abi.ofBytes, {bytes_}]", text)
left = [l for l in text.split("\n") if re.search(esc + r"\b", l) and not l.lstrip().startswith(("/-", "--")) and "`" not in l]
if left:
    sys.exit(f"{name}: {len(left)} lines still name {own}: {left[0][:120]}")
text = text.replace(f"namespace Proof_{name}", f"namespace Direct_{name}").replace(f"end Proof_{name}", f"end Direct_{name}")
lines = text.split("\n")
last = max(i for i, l in enumerate(lines) if l.startswith("import "))
lines.insert(last + 1, f"import {module}")
text = "\n".join(lines).replace("/-! #", f"/-! (Written by direct_fn.py from Proof_{name}.lean: about `{bytes_}`, the contract in bytes.)\n\n#", 1)
Path(f"Direct_{name}.lean").write_text(text)
print(f"{name}: {n} statements and {k + d} unfoldings now of {bytes_}; wrote Direct_{name}.lean")
