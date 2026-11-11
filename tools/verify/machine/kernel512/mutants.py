import subprocess, time
from pathlib import Path
p = Path("Code.lean"); good = p.read_text()
muts = [("0x3772", ".vprord 3 (.x 3) 16", ".vprord 3 (.x 3) 15"), ("0x3783", ".vprord 1 (.x 1) 12", ".vprord 1 (.x 1) 13"),
        ("0x37A9", ".vprord 1 (.x 1) 7", ".vprord 1 (.x 1) 8"), ("0x3764", ".vpaddd 0 0 (.x 4)", ".vpaddd 0 0 (.x 5)"),
        ("0x376C", ".vpxor 3 3 (.x 0)", ".vpxor 3 3 (.x 1)"), ("0x37B0", ".pshufd 0 (.x 0) 147", ".pshufd 0 (.x 0) 57"),
        ("0x3762", ".movb .rax 7", ".movb .rax 6"), ("0x3833", ".vpblendd 9 9 (.x 8) 170", ".vpblendd 9 9 (.x 8) 168"),
        ("0x381E", ".vshufps 8 4 (.x 5) 214", ".vshufps 8 4 (.x 5) 215"), ("0x3863", ".vpxor 0 0 (.x 2)", ".vpxor 0 0 (.x 3)"),
        ("0x3709", ".movzx8 .rax .r8", ".movzx8 .rax .rdx"), ("0x3710", ".shl64 .rax 32", ".shl64 .rax 31"),
        ("0x3725", "0xA54FF53A3C6EF372BB67AE856A09E667#128", "0xA54FF53A3C6EF372BB67AE856A09E666#128"), ("0x3736", ".vshufps 4 8 (.x 9) 136", ".vshufps 4 8 (.x 9) 221")]
rows = []
for at, old, new in muts:
    lines = good.splitlines(keepends=True)
    hit = [i for i, l in enumerate(lines) if l.lstrip().startswith(f"({at},") or l.startswith(f"theorem at_{at[2:]} ")]
    assert len(hit) == 2 and all(old in lines[i] for i in hit), (at, old)
    for i in hit: lines[i] = lines[i].replace(old, new, 1)
    p.write_text("".join(lines)); t = time.time()
    r = subprocess.run(["lake", "build", "Main"], capture_output=True, text=True)
    rows.append(f"{'rejected' if r.returncode else 'ACCEPTED'}\t{time.time()-t:.1f}s\t{at}\t{old} -> {new}")
    print(rows[-1], flush=True)
p.write_text(good)
Path("mutants.tsv").write_text("\n".join(rows) + "\n")
print(sum(r.startswith("rejected") for r in rows), "of", len(rows), "rejected")
