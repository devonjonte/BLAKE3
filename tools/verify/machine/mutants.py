import subprocess, time, re
from pathlib import Path
p = Path("Code.lean"); good = p.read_text()
# Each is a change to one instruction of the lifted program: (address, old, new).
muts = [
 ("0x1016", ".shr 32 (.reg .rax) 19", ".shr 32 (.reg .rax) 18"),          # SSE4.1 from the wrong bit
 ("0x1020", "(.imm 0x1C000000)", "(.imm 0x14000000)"),                   # OSXSAVE not required
 ("0x1026", ".jcc .ne", ".jcc .e"),
 ("0x1034", ".shr 8 (.reg .rsi) 3", ".shr 8 (.reg .rsi) 2"),              # AVX2 from the wrong bit
 ("0x103E", "(.imm 0x6)", "(.imm 0x4)"),                                 # XMM state not required
 ("0x1047", ".cmovcc .ne", ".cmovcc .e"),
 ("0x104D", "(.imm 0xE6)", "(.imm 0xE4)"),
 ("0x1053", "(.imm 0x80010000)", "(.imm 0x10000)"),                      # AVX-512 without VL
 ("0x1059", ".or 32", ".and 32"),
 ("0x105B", ".jcc .ne", ".jcc .e"),
 ("0x1065", "(.imm 0xF00)", "(.imm 0x700)"),
 ("0x1074", "(.imm 0xA00001)", "(.imm 0xA00002)"),                      # family 0x1A itself excluded
 ("0x1074", "(.imm 0xA00001)", "(.imm 0x900001)"),                      # family 0x19 admitted
 ("0x107A", ".setcc .ae", ".setcc .e"),
 ("0x1083", ".shl 8 (.reg .rdx) 4", ".shl 8 (.reg .rdx) 3"),
 ("0x1088", "(.imm 0x8)", "(.imm 0x0)"),
 ("0x101E", "(.imm 0xFFFFFFFFFFFFFF80)", "(.imm 0x0)"),                  # READ never set
 ("0x108D", "(.imm 0x18)", "(.imm 0x10)"),                               # the stack left unbalanced
 ("0x2022", "(.imm 0x1C000000)", "(.imm 0x14000000)"),                   # XGETBV without OSXSAVE: a fault on old systems
 ("0x2036", "(.imm 0x7)", "(.imm 0x6)"),                                 # the wrong CPUID leaf
 ("0x2054", "(.imm 0x68747541)", "(.imm 0x68747540)"),                   # a different vendor string
 ("0x2068", ".or 32", ".and 32"),
 ("0x2051", "(.mem .rbx 0xC)", "(.mem .rbx 0x8)"),                       # leaf 7 EBX stored over XCR0
 ("0x206E", ".pop .rbx", ".pop .rsi"),                                   # RBX not restored
 ("0x3000", ".xor 32 (.reg .rcx) (.reg .rcx)", ".mov 32 (.reg .rcx) (.imm 0x1)"),  # the wrong extended control register
]
rows = []; t0 = time.time()
for at, old, new in muts:
    lines = good.splitlines(keepends=True); hit = [i for i, l in enumerate(lines) if l.lstrip().startswith(f"({at},")]
    assert len(hit) == 1 and old in lines[hit[0]], (at, old)
    lines[hit[0]] = lines[hit[0]].replace(old, new, 1)
    # the per-address lemma must change with it, as lift.py would write it
    lem = [i for i, l in enumerate(lines) if l.startswith(f"@[code_at] theorem at_{at[2:]} ")]
    assert len(lem) == 1 and old in lines[lem[0]]
    lines[lem[0]] = lines[lem[0]].replace(old, new, 1)
    p.write_text("".join(lines)); t = time.time()
    r = subprocess.run(["lake", "build"], capture_output=True, text=True)
    verdict = "rejected" if r.returncode != 0 else "ACCEPTED"
    rows.append(f"{verdict}\t{time.time()-t:.1f}s\t{at}\t{old} -> {new}")
p.write_text(good)
Path("mutants.tsv").write_text("\n".join(rows) + "\n")
print(sum(r.startswith("rejected") for r in rows), "of", len(rows), "rejected in", round(time.time() - t0), "s")
print("\n".join(r for r in rows if not r.startswith("rejected")))
