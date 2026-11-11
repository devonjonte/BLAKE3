import Std.Tactic.BVDecide

/-! # One small x86-64 for the kernels and the compiled Rust around them

Fourteen general registers, sixteen XMM registers, ZF and CF, and memory as the bytes the
program owns: `mem a = none` is a byte it does not own, and reading or writing one is a fault.
An aligned vector load or store (MOVAPS, MOVDQA) at an address that is not a multiple of 16 is
a fault too. Whatever is not modelled is a fault. -/

namespace X86

abbrev V := BitVec 128

/-- Doubleword `i` of a vector (0 is the lowest). -/
def dw (v : V) (i : Nat) : BitVec 32 := v.extractLsb' (32 * i) 32
/-- A vector from its doublewords, lowest first. -/
def mk4 (a b c e : BitVec 32) : V := e ++ c ++ b ++ a
def by8 (v : V) (i : Nat) : BitVec 8 := v.extractLsb' (8 * i) 8
def w16 (v : V) (i : Nat) : BitVec 16 := v.extractLsb' (16 * i) 16

def map2 (f : BitVec 32 → BitVec 32 → BitVec 32) (x y : V) : V :=
  mk4 (f (dw x 0) (dw y 0)) (f (dw x 1) (dw y 1)) (f (dw x 2) (dw y 2)) (f (dw x 3) (dw y 3))
def map1 (f : BitVec 32 → BitVec 32) (x : V) : V := mk4 (f (dw x 0)) (f (dw x 1)) (f (dw x 2)) (f (dw x 3))

/-- PSHUFB: byte `i` of the result is 0 where the mask byte's top bit is set, and otherwise the
byte of `x` its low four bits name. -/
def shufb1 (x m : V) (i : Nat) : BitVec 8 :=
  if (by8 m i).getLsbD 7 then 0 else (x >>> (((by8 m i) &&& 15).setWidth 128 <<< 3)).setWidth 8
def pshufb (x m : V) : V :=
  shufb1 x m 15 ++ shufb1 x m 14 ++ shufb1 x m 13 ++ shufb1 x m 12 ++ shufb1 x m 11 ++ shufb1 x m 10 ++ shufb1 x m 9 ++
    shufb1 x m 8 ++ shufb1 x m 7 ++ shufb1 x m 6 ++ shufb1 x m 5 ++ shufb1 x m 4 ++ shufb1 x m 3 ++ shufb1 x m 2 ++
    shufb1 x m 1 ++ shufb1 x m 0
/-- PSHUFD: doubleword `i` of the result is the doubleword of `y` that bits `2i+1:2i` of `imm` name. -/
def pshufd (y : V) (imm : Nat) : V :=
  mk4 (dw y (imm % 4)) (dw y (imm / 4 % 4)) (dw y (imm / 16 % 4)) (dw y (imm / 64 % 4))
/-- SHUFPS: the low two doublewords from `x`, the high two from `y`, each named by two bits of `imm`. -/
def shufps (x y : V) (imm : Nat) : V :=
  mk4 (dw x (imm % 4)) (dw x (imm / 4 % 4)) (dw y (imm / 16 % 4)) (dw y (imm / 64 % 4))
/-- PBLENDW: word `i` from `y` where bit `i` of `imm` is set, else from `x`. -/
def blend1 (x y : V) (imm i : Nat) : BitVec 16 := if imm / 2 ^ i % 2 = 1 then w16 y i else w16 x i
def pblendw (x y : V) (imm : Nat) : V :=
  blend1 x y imm 7 ++ blend1 x y imm 6 ++ blend1 x y imm 5 ++ blend1 x y imm 4 ++ blend1 x y imm 3 ++
    blend1 x y imm 2 ++ blend1 x y imm 1 ++ blend1 x y imm 0
/-- VPBLENDD: doubleword `i` from `y` where bit `i` of `imm` is set, else from `x`. -/
def blendd1 (x y : V) (imm i : Nat) : BitVec 32 := if imm / 2 ^ i % 2 = 1 then dw y i else dw x i
def vpblendd (x y : V) (imm : Nat) : V := mk4 (blendd1 x y imm 0) (blendd1 x y imm 1) (blendd1 x y imm 2) (blendd1 x y imm 3)
def punpcklqdq (x y : V) : V := y.extractLsb' 0 64 ++ x.extractLsb' 0 64
def punpckldq (x y : V) : V := mk4 (dw x 0) (dw y 0) (dw x 1) (dw y 1)
def punpckhdq (x y : V) : V := mk4 (dw x 2) (dw y 2) (dw x 3) (dw y 3)

inductive Reg | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi | r8 | r9 | r12 | r13 | r14 | r15
  deriving DecidableEq

/-- The bytes this program owns. -/
abbrev Mem := BitVec 64 → Option (BitVec 8)

structure State where
  rax : BitVec 64
  rcx : BitVec 64
  rdx : BitVec 64
  rbx : BitVec 64
  rsp : BitVec 64
  rbp : BitVec 64
  rsi : BitVec 64
  rdi : BitVec 64
  r8 : BitVec 64
  r9 : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64
  zf : Option Bool
  cf : Option Bool
  x0 : V
  x1 : V
  x2 : V
  x3 : V
  x4 : V
  x5 : V
  x6 : V
  x7 : V
  x8 : V
  x9 : V
  x10 : V
  x11 : V
  x12 : V
  x13 : V
  x14 : V
  x15 : V
  mem : Mem
  pc : Nat

def State.get (s : State) : Reg → BitVec 64
  | .rax => s.rax | .rcx => s.rcx | .rdx => s.rdx | .rbx => s.rbx | .rsp => s.rsp | .rbp => s.rbp | .rsi => s.rsi | .rdi => s.rdi | .r8 => s.r8 | .r9 => s.r9 | .r12 => s.r12 | .r13 => s.r13 | .r14 => s.r14 | .r15 => s.r15

def State.set (s : State) (r : Reg) (v : BitVec 64) : State :=
  match r with
  | .rax => { s with rax := v } | .rcx => { s with rcx := v } | .rdx => { s with rdx := v } | .rbx => { s with rbx := v }
  | .rsp => { s with rsp := v } | .rbp => { s with rbp := v } | .rsi => { s with rsi := v } | .rdi => { s with rdi := v }
  | .r8 => { s with r8 := v } | .r9 => { s with r9 := v } | .r12 => { s with r12 := v } | .r13 => { s with r13 := v }
  | .r14 => { s with r14 := v } | .r15 => { s with r15 := v }

def State.xmm (s : State) : Nat → V
  | 0 => s.x0 | 1 => s.x1 | 2 => s.x2 | 3 => s.x3 | 4 => s.x4 | 5 => s.x5 | 6 => s.x6 | 7 => s.x7
  | 8 => s.x8 | 9 => s.x9 | 10 => s.x10 | 11 => s.x11 | 12 => s.x12 | 13 => s.x13 | 14 => s.x14
  | _ => s.x15

def State.setx (s : State) (i : Nat) (v : V) : State :=
  match i with
  | 0 => { s with x0 := v } | 1 => { s with x1 := v } | 2 => { s with x2 := v } | 3 => { s with x3 := v }
  | 4 => { s with x4 := v } | 5 => { s with x5 := v } | 6 => { s with x6 := v } | 7 => { s with x7 := v }
  | 8 => { s with x8 := v } | 9 => { s with x9 := v } | 10 => { s with x10 := v } | 11 => { s with x11 := v }
  | 12 => { s with x12 := v } | 13 => { s with x13 := v } | 14 => { s with x14 := v }
  | _ => { s with x15 := v }

def trunc (w : Nat) (v : BitVec 64) : BitVec 64 :=
  match w with
  | 8 => v &&& 0xFF
  | 32 => v &&& 0xFFFFFFFF
  | _ => v

def byte (v : BitVec 64) (i : Nat) : BitVec 8 := (v >>> (8 * i)).setWidth 8

def Mem.read8 (m : Mem) (a : BitVec 64) : Option (BitVec 64) := (m a).map (BitVec.setWidth 64)

/-- `w` bits at `a`, little-endian (w is 8, 32 or 64). -/
def Mem.read (m : Mem) (a : BitVec 64) : Nat → Option (BitVec 64)
  | 8 => m.read8 a
  | 32 => do
    let b0 ← m.read8 a; let b1 ← m.read8 (a + 1); let b2 ← m.read8 (a + 2); let b3 ← m.read8 (a + 3)
    pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24))
  | _ => do
    let b0 ← m.read8 a; let b1 ← m.read8 (a + 1); let b2 ← m.read8 (a + 2); let b3 ← m.read8 (a + 3)
    let b4 ← m.read8 (a + 4); let b5 ← m.read8 (a + 5); let b6 ← m.read8 (a + 6); let b7 ← m.read8 (a + 7)
    pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56))

/-- The sixteen bytes at `a`, as a vector. -/
def Mem.read128 (m : Mem) (a : BitVec 64) : Option V := do
  let b0 ← m (a + 0); let b1 ← m (a + 1); let b2 ← m (a + 2); let b3 ← m (a + 3); let b4 ← m (a + 4); let b5 ← m (a + 5); let b6 ← m (a + 6); let b7 ← m (a + 7); let b8 ← m (a + 8); let b9 ← m (a + 9); let b10 ← m (a + 10); let b11 ← m (a + 11); let b12 ← m (a + 12); let b13 ← m (a + 13); let b14 ← m (a + 14); let b15 ← m (a + 15);
  pure (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)

/-- One byte put at `a`, whoever owns it. -/
def Mem.put8 (m : Mem) (a : BitVec 64) (v : BitVec 8) : Mem := fun x => if x = a then some v else m x

/-- One byte written at `a`: a fault unless the program owns it. -/
def Mem.write8 (m : Mem) (a : BitVec 64) (v : BitVec 8) : Option Mem :=
  if (m a).isSome then some (m.put8 a v) else none

def Mem.write (m : Mem) (a : BitVec 64) (v : BitVec 64) : Nat → Option Mem
  | 8 => m.write8 a (byte v 0)
  | 32 => do
    let m ← m.write8 a (byte v 0); let m ← m.write8 (a + 1) (byte v 1)
    let m ← m.write8 (a + 2) (byte v 2); m.write8 (a + 3) (byte v 3)
  | _ => do
    let m ← m.write8 a (byte v 0); let m ← m.write8 (a + 1) (byte v 1)
    let m ← m.write8 (a + 2) (byte v 2); let m ← m.write8 (a + 3) (byte v 3)
    let m ← m.write8 (a + 4) (byte v 4); let m ← m.write8 (a + 5) (byte v 5)
    let m ← m.write8 (a + 6) (byte v 6); m.write8 (a + 7) (byte v 7)

def Mem.write128 (m : Mem) (a : BitVec 64) (v : V) : Option Mem := do
  let m ← m.write8 (a + 0) (by8 v 0)
  let m ← m.write8 (a + 1) (by8 v 1)
  let m ← m.write8 (a + 2) (by8 v 2)
  let m ← m.write8 (a + 3) (by8 v 3)
  let m ← m.write8 (a + 4) (by8 v 4)
  let m ← m.write8 (a + 5) (by8 v 5)
  let m ← m.write8 (a + 6) (by8 v 6)
  let m ← m.write8 (a + 7) (by8 v 7)
  let m ← m.write8 (a + 8) (by8 v 8)
  let m ← m.write8 (a + 9) (by8 v 9)
  let m ← m.write8 (a + 10) (by8 v 10)
  let m ← m.write8 (a + 11) (by8 v 11)
  let m ← m.write8 (a + 12) (by8 v 12)
  let m ← m.write8 (a + 13) (by8 v 13)
  let m ← m.write8 (a + 14) (by8 v 14)
  m.write8 (a + 15) (by8 v 15)

/-- A general-register operand. -/
inductive Opnd
  | reg (r : Reg)
  | mem (base : Reg) (disp : BitVec 64)
  | imm (v : BitVec 64)

/-- A vector operand: a register, sixteen bytes of memory, or a constant the code names (a
RIP-relative load of read-only data, which the lifter resolves). -/
inductive Src
  | x (i : Nat)
  | m (base : Reg) (disp : BitVec 64)
  | c (v : V)

inductive Instr
  -- vector moves; `aligned` is MOVAPS and MOVDQA, which fault at an address not a multiple of 16
  | movv (aligned : Bool) (dst : Nat) (src : Src)
  | storev (aligned : Bool) (base : Reg) (disp : BitVec 64) (src : Nat)
  | movq (dst : Nat) (r : Reg)
  -- SSE forms
  | paddd (dst : Nat) (src : Src)
  | pxor (dst : Nat) (src : Src)
  | por (dst : Nat) (src : Src)
  | pshufb (dst : Nat) (src : Src)
  | pslld (dst : Nat) (n : Nat)
  | psrld (dst : Nat) (n : Nat)
  | pshufd (dst : Nat) (src : Src) (imm : Nat)
  | shufps (dst : Nat) (src : Src) (imm : Nat)
  | pblendw (dst : Nat) (src : Src) (imm : Nat)
  | punpcklqdq (dst : Nat) (src : Src)
  | punpckldq (dst : Nat) (src : Src)
  | punpckhdq (dst : Nat) (src : Src)
  -- three-operand (VEX and EVEX) forms on XMM registers
  | vpaddd (dst a : Nat) (src : Src)
  | vpxor (dst a : Nat) (src : Src)
  | vprord (dst : Nat) (src : Src) (n : Nat)
  | vshufps (dst a : Nat) (src : Src) (imm : Nat)
  | vpblendd (dst a : Nat) (src : Src) (imm : Nat)
  | vpunpcklqdq (dst a : Nat) (src : Src)
  | vpunpckldq (dst a : Nat) (src : Src)
  | vpunpckhdq (dst a : Nat) (src : Src)
  -- general registers
  | mov (w : Nat) (dst src : Opnd)
  /-- MOVZX r32, r/m8 -/
  | movzx8 (dst : Reg) (src : Opnd)
  | or (w : Nat) (dst src : Opnd)
  | add (w : Nat) (dst src : Opnd)
  | sub (w : Nat) (dst src : Opnd)
  | cmp (w : Nat) (a b : Opnd)
  | shl64 (r : Reg) (n : Nat)
  | decb (r : Reg)
  | push (r : Reg)
  | pop (r : Reg)
  | je (target : Nat)
  | jne (target : Nat)
  | jmp (target : Nat)
  | call (target : Nat)
  | ret

def read (s : State) (w : Nat) : Opnd → Option (BitVec 64)
  | .reg r => some (trunc w (s.get r))
  | .imm v => some (trunc w v)
  | .mem b d => s.mem.read (s.get b + d) w

/-- Writing 32 bits of a register clears its upper half; writing 8 keeps the other 56. -/
def write (s : State) (w : Nat) (o : Opnd) (v : BitVec 64) : Option State :=
  match o with
  | .reg r => some (s.set r (match w with
      | 8 => (s.get r &&& ~~~(0xFF : BitVec 64)) ||| (v &&& 0xFF)
      | 32 => v &&& 0xFFFFFFFF
      | _ => v))
  | .imm _ => none
  | .mem b d => (s.mem.write (s.get b + d) v w).map fun m => { s with mem := m }

/-- Is this address a multiple of 16? -/
def aligned16 (a : BitVec 64) : Bool := a &&& 15 == 0

def src (s : State) (aligned : Bool) : Src → Option V
  | .x i => some (s.xmm i)
  | .m b d => if aligned && !aligned16 (s.get b + d) then none else s.mem.read128 (s.get b + d)
  | .c v => some v

/-- One instruction at `s.pc`, the next one at `next` unless it jumps. -/
def step (i : Instr) (next : Nat) (s : State) : Option State :=
  let s := { s with pc := next }
  match i with
  | .movv al d x => do some (s.setx d (← src s al x))
  | .storev al b disp x =>
    if al && !aligned16 (s.get b + disp) then none
    else (s.mem.write128 (s.get b + disp) (s.xmm x)).map fun m => { s with mem := m }
  | .movq d r => some (s.setx d ((s.get r).setWidth 128))
  | .paddd d x => do some (s.setx d (map2 (· + ·) (s.xmm d) (← src s false x)))
  | .pxor d x => do some (s.setx d (s.xmm d ^^^ (← src s false x)))
  | .por d x => do some (s.setx d (s.xmm d ||| (← src s false x)))
  | .pshufb d x => do some (s.setx d (pshufb (s.xmm d) (← src s false x)))
  | .pslld d n => some (s.setx d (map1 (· <<< n) (s.xmm d)))
  | .psrld d n => some (s.setx d (map1 (· >>> n) (s.xmm d)))
  | .pshufd d x imm => do some (s.setx d (pshufd (← src s false x) imm))
  | .shufps d x imm => do some (s.setx d (shufps (s.xmm d) (← src s false x) imm))
  | .pblendw d x imm => do some (s.setx d (pblendw (s.xmm d) (← src s false x) imm))
  | .punpcklqdq d x => do some (s.setx d (punpcklqdq (s.xmm d) (← src s false x)))
  | .punpckldq d x => do some (s.setx d (punpckldq (s.xmm d) (← src s false x)))
  | .punpckhdq d x => do some (s.setx d (punpckhdq (s.xmm d) (← src s false x)))
  | .vpaddd d a x => do some (s.setx d (map2 (· + ·) (s.xmm a) (← src s false x)))
  | .vpxor d a x => do some (s.setx d (s.xmm a ^^^ (← src s false x)))
  | .vprord d x n => do some (s.setx d (map1 (·.rotateRight n) (← src s false x)))
  | .vshufps d a x imm => do some (s.setx d (shufps (s.xmm a) (← src s false x) imm))
  | .vpblendd d a x imm => do some (s.setx d (vpblendd (s.xmm a) (← src s false x) imm))
  | .vpunpcklqdq d a x => do some (s.setx d (punpcklqdq (s.xmm a) (← src s false x)))
  | .vpunpckldq d a x => do some (s.setx d (punpckldq (s.xmm a) (← src s false x)))
  | .vpunpckhdq d a x => do some (s.setx d (punpckhdq (s.xmm a) (← src s false x)))
  | .mov w d x => do write s w d (← read s w x)
  | .movzx8 d x => do some (s.set d (← read s 8 x))
  | .or w d x => do
    let v := (← read s w d) ||| (← read s w x)
    write { s with zf := some (trunc w v == 0), cf := some false } w d v
  | .add w d x => do
    let a ← read s w d; let b ← read s w x; let v := trunc w (a + b)
    write { s with zf := some (v == 0), cf := some (v.ult a) } w d v
  | .sub w d x => do
    let a ← read s w d; let b ← read s w x; let v := trunc w (a - b)
    write { s with zf := some (v == 0), cf := some (a.ult b) } w d v
  | .cmp w a b => do
    let a ← read s w a; let b ← read s w b
    some { s with zf := some (trunc w (a - b) == 0), cf := some (a.ult b) }
  -- A shift's carry is the last bit out; left unmodelled, so nothing may branch on it.
  | .shl64 r n => some ({ s with zf := some (s.get r <<< n == 0), cf := none }.set r (s.get r <<< n))
  -- DEC leaves CF as it was.
  | .decb r =>
    let v := (s.get r).setWidth 8 - 1
    some ({ s with zf := some (v == 0) }.set r ((s.get r &&& ~~~(0xFF : BitVec 64)) ||| v.setWidth 64))
  | .push r => (s.mem.write (s.rsp - 8) (s.get r) 64).map fun m => { s with rsp := s.rsp - 8, mem := m }
  | .pop r => (s.mem.read s.rsp 64).map fun v => { s with rsp := s.rsp + 8 }.set r v
  | .je t => s.zf.map fun z => if z then { s with pc := t } else s
  | .jne t => s.zf.map fun z => if z then s else { s with pc := t }
  | .jmp t => some { s with pc := t }
  | .call t => (s.mem.write (s.rsp - 8) (BitVec.ofNat 64 next) 64).map fun m => { s with rsp := s.rsp - 8, mem := m, pc := t }
  | .ret => (s.mem.read s.rsp 64).map fun to => { s with rsp := s.rsp + 8, pc := to.toNat }

/-- Exactly `k` instructions. -/
def steps (prog : Nat → Option (Instr × Nat)) : Nat → State → Option State
  | 0, s => some s
  | k + 1, s =>
    match prog s.pc with
    | none => none
    | some (i, next) => (step i next s).bind (steps prog k)

theorem steps_mk (prog : Nat → Option (Instr × Nat)) (k : Nat) (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V) (mem : Mem) (pc : Nat) :
    steps prog (k + 1) ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ =
      match prog pc with
      | none => none
      | some (i, next) => (step i next ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩).bind (steps prog k) := rfl

theorem steps_zero (prog : Nat → Option (Instr × Nat)) (s : State) : steps prog 0 s = some s := rfl

theorem steps_add (prog : Nat → Option (Instr × Nat)) (a b : Nat) (s : State) :
    steps prog (a + b) s = (steps prog a s).bind (steps prog b) := by
  induction a generalizing s with
  | zero => simp [steps]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp only [steps]
    cases prog s.pc with
    | none => rfl
    | some x =>
      obtain ⟨i, next⟩ := x
      simp only []
      cases step i next s with
      | none => rfl
      | some s1 => simp only [Option.bind_some, ih]

end X86
