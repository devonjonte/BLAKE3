"""llvm-objdump's listing of one SSE4.1 kernel -> a Lean program for Simd.lean.

usage: lift_simd.py OBJECT FUNCTION OUT.lean NAMESPACE
A RIP-relative load is resolved to the 16 bytes its relocation names in the object's data.
An instruction or operand form this does not know stops it: nothing is skipped but NOPs
after the function's last instruction."""
import re, subprocess, sys, os

OD = os.environ.get("OBJDUMP", "llvm-objdump")
obj, func, out, ns = sys.argv[1:5]
listing = subprocess.run([OD, "-d", "-r", "-M", "intel", obj], capture_output=True, text=True, check=True).stdout
symbols = {}
for line in subprocess.run([OD, "-t", obj], capture_output=True, text=True, check=True).stdout.splitlines():
    f = line.split()
    if len(f) >= 5 and re.fullmatch(r"[0-9a-f]{16}", f[0]):
        symbols[f[-1]] = int(f[0], 16)
data = {}
for line in subprocess.run([OD, "-s", obj], capture_output=True, text=True, check=True).stdout.splitlines():
    m = re.match(r"^\s*([0-9a-f]+) ((?:[0-9a-f]+ )+)", line)
    if m:
        at = int(m.group(1), 16)
        for i, b in enumerate(bytes.fromhex(m.group(2).replace(" ", ""))):
            data[at + i] = b

def const(sym):
    at = symbols[sym]
    return "0x" + "".join(f"{data[at + i]:02X}" for i in reversed(range(16)))

REG = {r: r for r in "rax rcx rdx rsi rdi r8 rsp".split()}
def xmm(t):
    m = re.fullmatch(r"xmm(\d+)", t.strip()); assert m, t; return int(m.group(1))
def src(t, reloc):
    t = t.strip()
    if re.fullmatch(r"xmm\d+", t): return f"(.x {xmm(t)})"
    if t == "xmmword ptr [rip]": assert reloc, "a RIP-relative load without a relocation"; return f"(.c {const(reloc)}#128)"
    m = re.fullmatch(r"xmmword ptr \[(\w+)(?: \+ (0x[0-9a-f]+))?\]", t); assert m, t
    return f"(.m .{REG[m.group(1)]} {m.group(2) or '0x0'})"

rows, inside, insns = [], False, []
for line in listing.splitlines():
    m = re.match(r"^[0-9a-f]+ <(.+)>:$", line)
    if m: inside = m.group(1) == func; continue
    if not inside: continue
    m = re.match(r"^\s+([0-9a-f]+):((?: [0-9a-f]{2})+)\s+(\S+)\s*([^#]*)", line)
    if m: insns.append([int(m.group(1), 16), len(m.group(2).split()), m.group(3), m.group(4).strip(), None, m.group(2).strip()]); continue
    m = re.match(r"^\s+[0-9a-f]+:\s+X86_64_RELOC_SIGNED\s+(\S+)$", line)
    if m: insns[-1][4] = m.group(1)
base = insns[0][0]
ended = False
for at, size, op, args, reloc, raw in insns:
    a = [x.strip() for x in args.split(",")] if args else []
    if ended: assert op == "nop", f"code after the return: {op}"; continue
    if op in ("movups", "movaps", "movdqa", "vmovups", "vmovaps", "vmovdqa", "vmovdqu"):
        if re.fullmatch(r"xmm\d+", a[0]): ins = f".movv {xmm(a[0])} {src(a[1], reloc)}"
        else:
            m = re.fullmatch(r"xmmword ptr \[(\w+)(?: \+ (0x[0-9a-f]+))?\]", a[0]); assert m, args
            ins = f".storev .{REG[m.group(1)]} {m.group(2) or '0x0'} {xmm(a[1])}"
    elif op in ("movq", "vmovq"): ins = f".movq {xmm(a[0])} .{REG[a[1]]}"
    elif op in ("paddd", "pxor", "por", "pshufb", "punpcklqdq", "punpckldq", "punpckhdq"): ins = f".{op} {xmm(a[0])} {src(a[1], reloc)}"
    elif op in ("pslld", "psrld"): ins = f".{op} {xmm(a[0])} {int(a[1], 16)}"
    elif op in ("pshufd", "shufps", "pblendw"): ins = f".{op} {xmm(a[0])} {src(a[1], reloc)} {int(a[2], 16)}"
    elif op == "vpshufd": ins = f".pshufd {xmm(a[0])} {src(a[1], reloc)} {int(a[2], 16)}"
    elif op in ("vpaddd", "vpxord", "vpxor", "vpunpcklqdq", "vpunpckldq", "vpunpckhdq"): ins = f".{op.replace('vpxord', 'vpxor')} {xmm(a[0])} {xmm(a[1])} {src(a[2], reloc)}"
    elif op == "vprord": ins = f".vprord {xmm(a[0])} {src(a[1], reloc)} {int(a[2], 16)}"
    elif op in ("vshufps", "vpblendd"): ins = f".{op} {xmm(a[0])} {xmm(a[1])} {src(a[2], reloc)} {int(a[3], 16)}"
    elif op == "movzx":
        r8 = dict(r8b="r8", dl="rdx"); r32 = dict(eax="rax", edx="rdx"); ins = f".movzx8 .{r32[a[0]]} .{r8[a[1]]}"
    elif op == "shl": assert a[0] in REG; ins = f".shl64 .{a[0]} {int(a[1], 16)}"
    elif op == "add": assert a[0] in REG and a[1] in REG; ins = f".add64 .{a[0]} .{a[1]}"
    elif op == "mov": assert a[0] == "al"; ins = f".movb .rax {int(a[1], 16)}"
    elif op == "dec": assert a[0] == "al"; ins = ".decb .rax"
    elif op in ("je", "jmp"): ins = f".{op} 0x{int(a[0].split()[0], 16):X}"
    elif op == "ret": ins = ".ret"; ended = True
    else: raise SystemExit(f"unknown instruction: {op} {args}")
    rows.append((at, at + size, ins, f"{raw:<24} {op} {args}"))
text = ["import Simd", "", f"/-! `{func}` of {os.path.basename(obj)}, as llvm-objdump reads it. Written by lift_simd.py. -/", "",
        "set_option maxRecDepth 100000", f"namespace {ns}", "open Simd", "", f"def entry : Nat := 0x{base:X}", "", "def table : List (Nat × Instr × Nat) := ["]
text += [f"  (0x{at:X}, {ins}, 0x{nxt:X}){',' if i + 1 < len(rows) else ''}  -- {s}" for i, (at, nxt, ins, s) in enumerate(rows)]
text += ["]", "", "def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc", ""]
text += [f"theorem at_{at:X} : prog 0x{at:X} = some ({ins}, 0x{nxt:X}) := rfl" for at, nxt, ins, _ in rows]
text += ["", f"end {ns}", ""]
open(out, "w").write("\n".join(text))
print(len(rows), "instructions")
