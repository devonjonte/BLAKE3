import subprocess, time
from pathlib import Path
p = Path("Code.lean"); good = p.read_text()
muts = [("0x1033", ".rol32 .rax 5", ".rol32 .rax 6"), ("0x1036", ".xor 32 (.reg .rax) (.memi .rdi .rcx)", ".add 32 (.reg .rax) (.memi .rdi .rcx)"),
        ("0x1039", "(.memi .rdi .rcx) (.reg .rax)", "(.memi .rdi .rcx) (.reg .rdx)"), ("0x103C", "(.imm 0x4)", "(.imm 0x8)"),
        ("0x1043", ".jcc .ne 0x1033", ".jcc .ne 0x1036"), ("0x102D", ".shl 64 (.reg .rsi) 2", ".shl 64 (.reg .rsi) 3"),
        ("0x1027", ".jcc .e 0x1046", ".jcc .e 0x1045"), ("0x1045", ".pop .rbp", ".pop .rbx"), ("0x1022", "(.reg .rdx)", "(.reg .rsi)"),
        ("0x1039", ".mov 32 (.memi .rdi .rcx) (.reg .rax)", ".mov 64 (.memi .rdi .rcx) (.reg .rax)"),
        ("0x1031", ".xor 32 (.reg .rcx) (.reg .rcx)", ".mov 32 (.reg .rcx) (.imm 0x4)")]
rows = []
for at, old, new in muts:
    lines = good.splitlines(keepends=True)
    hit = [i for i, l in enumerate(lines) if l.lstrip().startswith(f"({at},") or l.startswith(f"@[simp] theorem at_{at[2:]} ")]
    assert len(hit) == 2 and all(old in lines[i] for i in hit), (at, old)
    for i in hit: lines[i] = lines[i].replace(old, new, 1)
    p.write_text("".join(lines)); t = time.time()
    r = subprocess.run(["lake", "build", "Scan"], capture_output=True, text=True)
    rows.append(f"{'rejected' if r.returncode else 'ACCEPTED'}\t{time.time()-t:.1f}s\t{at}\t{old} -> {new}")
p.write_text(good)
print(sum(r.startswith("rejected") for r in rows), "of", len(rows), "rejected"); print("\n".join(r for r in rows if not r.startswith("rejected")))
