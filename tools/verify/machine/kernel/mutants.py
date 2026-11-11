import subprocess, time
from pathlib import Path
p = Path("Code.lean"); good = p.read_text()
muts = [("0x264C", ".pslld 1 20", ".pslld 1 19"), ("0x2651", ".psrld 11 12", ".psrld 11 13"), ("0x2639", ".pshufb 3 (.x 15)", ".pshufb 3 (.x 14)"),
        ("0x268B", ".pshufd 0 (.x 0) 147", ".pshufd 0 (.x 0) 57"), ("0x2690", ".pshufd 3 (.x 3) 78", ".pshufd 3 (.x 3) 147"),
        ("0x262D", ".paddd 0 (.x 4)", ".paddd 0 (.x 5)"), ("0x2635", ".pxor 3 (.x 0)", ".pxor 3 (.x 1)"), ("0x262B", ".movb .rax 7", ".movb .rax 6"),
        ("0x272B", ".pblendw 9 (.x 8) 204", ".pblendw 9 (.x 8) 200"), ("0x2710", ".shufps 8 (.x 5) 214", ".shufps 8 (.x 5) 215"),
        ("0x2765", ".pxor 0 (.x 2)", ".pxor 0 (.x 3)"), ("0x2770", ".storev .rdi 0x10 1", ".storev .rdi 0x10 0"),
        ("0x25CE", ".shl64 .r8 32", ".shl64 .r8 31"), ("0x25C7", "0xA54FF53A3C6EF372BB67AE856A09E667#128", "0xA54FF53A3C6EF372BB67AE856A09E666#128"),
        ("0x261B", "0x0C0F0E0D080B0A090407060500030201#128", "0x0C0F0E0D080B0A090407060500030202#128"), ("0x25EE", ".shufps 4 (.x 5) 136", ".shufps 4 (.x 5) 221")]
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
