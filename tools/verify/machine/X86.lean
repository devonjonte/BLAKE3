import Std.Tactic.BVDecide

/-! # A small x86-64: the instructions the compiled detection uses, and what each does

Everything trusted about the machine is in this file: a state (eight registers, two flags,
the bytes written so far), the instructions, and one step. Whatever is not modelled is a
fault (`none`): reading a byte never written, branching on a flag an instruction left
undefined, CPUID for a leaf not listed, XGETBV where the OS has not enabled it. A proof that
a program returns `some` result is so also a proof that it does none of those. -/

namespace X86

inductive Reg | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  deriving DecidableEq, Repr

/-- The four words CPUID gives for one leaf. -/
structure Leaf where
  eax : BitVec 32
  ebx : BitVec 32
  ecx : BitVec 32
  edx : BitVec 32

/-- A CPU, as far as these programs can see it: three CPUID leaves and XCR0. -/
structure Cpu where
  leaf0 : Leaf
  leaf1 : Leaf
  leaf7 : Leaf
  xcr0 : BitVec 64

structure State where
  rax : BitVec 64
  rcx : BitVec 64
  rdx : BitVec 64
  rbx : BitVec 64
  rsp : BitVec 64
  rbp : BitVec 64
  rsi : BitVec 64
  rdi : BitVec 64
  /-- ZF and CF, or `none` where the last instruction to touch them left them unmodelled. -/
  zf : Option Bool
  cf : Option Bool
  /-- The bytes written, newest first. A byte never written cannot be read. -/
  mem : List (BitVec 64 × BitVec 8)
  pc : Nat

def State.get (s : State) : Reg → BitVec 64
  | .rax => s.rax | .rcx => s.rcx | .rdx => s.rdx | .rbx => s.rbx
  | .rsp => s.rsp | .rbp => s.rbp | .rsi => s.rsi | .rdi => s.rdi

def State.set (s : State) (r : Reg) (v : BitVec 64) : State :=
  match r with
  | .rax => { s with rax := v } | .rcx => { s with rcx := v } | .rdx => { s with rdx := v } | .rbx => { s with rbx := v }
  | .rsp => { s with rsp := v } | .rbp => { s with rbp := v } | .rsi => { s with rsi := v } | .rdi => { s with rdi := v }

/-- A value cut to an operand's width in bits (8, 32 or 64); values travel as 64-bit words. -/
def trunc (w : Nat) (v : BitVec 64) : BitVec 64 :=
  match w with
  | 8 => v &&& 0xFF
  | 32 => v &&& 0xFFFFFFFF
  | _ => v

inductive Opnd
  | reg (r : Reg)
  | mem (base : Reg) (disp : BitVec 64)
  | imm (v : BitVec 64)

inductive Cond | e | ne | ae | b

inductive Instr
  | mov (w : Nat) (dst src : Opnd)
  | movzx (ws : Nat) (dst : Reg) (src : Opnd)
  | lea (dst base : Reg) (disp : BitVec 64)
  /-- `lea r32, [base + disp]` and `lea r32, [base + index]`: arithmetic only; the upper half is cleared. -/
  | lea32 (dst base : Reg) (disp : BitVec 64)
  | lea32i (dst base index : Reg)
  | xchg (a b : Reg)
  | not (w : Nat) (dst : Opnd)
  | and (w : Nat) (dst src : Opnd)
  | or (w : Nat) (dst src : Opnd)
  | xor (w : Nat) (dst src : Opnd)
  | add (w : Nat) (dst src : Opnd)
  | sub (w : Nat) (dst src : Opnd)
  | test (w : Nat) (a b : Opnd)
  | cmp (w : Nat) (a b : Opnd)
  | shr (w : Nat) (dst : Opnd) (n : Nat)
  | shl (w : Nat) (dst : Opnd) (n : Nat)
  | setcc (c : Cond) (dst : Opnd)
  | cmovcc (c : Cond) (dst : Reg) (src : Opnd)
  | jcc (c : Cond) (target : Nat)
  | call (target : Nat)
  | ret
  | push (r : Reg)
  | pop (r : Reg)
  | cpuid
  | xgetbv

def byteAt (m : List (BitVec 64 × BitVec 8)) (a : BitVec 64) : Option (BitVec 64) :=
  (m.lookup a).map (BitVec.setWidth 64)

/-- `n` bytes at `a`, little-endian (n is 1, 4 or 8). -/
def load (m : List (BitVec 64 × BitVec 8)) (a : BitVec 64) : Nat → Option (BitVec 64)
  | 8 => byteAt m a
  | 32 => do
    let b0 ← byteAt m a; let b1 ← byteAt m (a + 1); let b2 ← byteAt m (a + 2); let b3 ← byteAt m (a + 3)
    pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24))
  | _ => do
    let b0 ← byteAt m a; let b1 ← byteAt m (a + 1); let b2 ← byteAt m (a + 2); let b3 ← byteAt m (a + 3)
    let b4 ← byteAt m (a + 4); let b5 ← byteAt m (a + 5); let b6 ← byteAt m (a + 6); let b7 ← byteAt m (a + 7)
    pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56))

def byte (v : BitVec 64) (i : Nat) : BitVec 8 := (v >>> (8 * i)).setWidth 8

def store (m : List (BitVec 64 × BitVec 8)) (a : BitVec 64) (v : BitVec 64) : Nat → List (BitVec 64 × BitVec 8)
  | 8 => (a, byte v 0) :: m
  | 32 => (a, byte v 0) :: (a + 1, byte v 1) :: (a + 2, byte v 2) :: (a + 3, byte v 3) :: m
  | _ => (a, byte v 0) :: (a + 1, byte v 1) :: (a + 2, byte v 2) :: (a + 3, byte v 3)
      :: (a + 4, byte v 4) :: (a + 5, byte v 5) :: (a + 6, byte v 6) :: (a + 7, byte v 7) :: m

def read (s : State) (w : Nat) : Opnd → Option (BitVec 64)
  | .reg r => some (trunc w (s.get r))
  | .mem b d => load s.mem (s.get b + d) w
  | .imm v => some (trunc w v)

/-- Writing 32 bits of a register clears its upper half; writing 8 keeps the other 56. -/
def write (s : State) (w : Nat) (o : Opnd) (v : BitVec 64) : Option State :=
  match o with
  | .reg r => some (s.set r (match w with
      | 8 => (s.get r &&& ~~~(0xFF : BitVec 64)) ||| (v &&& 0xFF)
      | 32 => v &&& 0xFFFFFFFF
      | _ => v))
  | .mem b d => some { s with mem := store s.mem (s.get b + d) v w }
  | .imm _ => none

def holds (s : State) : Cond → Option Bool
  | .e => s.zf
  | .ne => s.zf.map (!·)
  | .ae => s.cf.map (!·)
  | .b => s.cf

/-- A logical result's flags: ZF by the result, CF clear. -/
def logic (s : State) (w : Nat) (v : BitVec 64) : State :=
  { s with zf := some (trunc w v == 0), cf := some false }

/-- CPUID for the leaf in EAX (and subleaf in ECX): leaves 0, 1, and 7 subleaf 0. -/
def cpuidOf (cpu : Cpu) (a c : BitVec 64) : Option Leaf :=
  if a = 0 then some cpu.leaf0 else if a = 1 then some cpu.leaf1 else if a = 7 ∧ c = 0 then some cpu.leaf7 else none

/-- One instruction at `s.pc`, the next one at `next` unless it jumps. -/
def step (cpu : Cpu) (i : Instr) (next : Nat) (s : State) : Option State :=
  let s := { s with pc := next }
  match i with
  | .mov w d x => do write s w d (← read s w x)
  | .movzx ws d x => do write s 32 (.reg d) (← read s ws x)
  | .lea d b disp => some (s.set d (s.get b + disp))
  | .lea32 d b disp => some (s.set d (trunc 32 (s.get b + disp)))
  | .lea32i d b i => some (s.set d (trunc 32 (s.get b + s.get i)))
  | .xchg a b => some ((s.set a (s.get b)).set b (s.get a))
  | .not w d => do write s w d (~~~(← read s w d))
  | .and w d x => do let v := (← read s w d) &&& (← read s w x); write (logic s w v) w d v
  | .or w d x => do let v := (← read s w d) ||| (← read s w x); write (logic s w v) w d v
  | .xor w d x => do let v := (← read s w d) ^^^ (← read s w x); write (logic s w v) w d v
  | .test w a b => do let v := (← read s w a) &&& (← read s w b); some (logic s w v)
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
  | .shr w d n => do let v := (← read s w d) >>> n; write { s with zf := some (trunc w v == 0), cf := none } w d v
  | .shl w d n => do let v := trunc w ((← read s w d) <<< n); write { s with zf := some (v == 0), cf := none } w d v
  | .setcc c d => do write s 8 d (if (← holds s c) then 1 else 0)
  | .cmovcc c d x => do let v ← read s 32 x; write s 32 (.reg d) (if (← holds s c) then v else trunc 32 (s.get d))
  | .jcc c t => do some (if (← holds s c) then { s with pc := t } else s)
  | .call t => some { s with rsp := s.rsp - 8, mem := store s.mem (s.rsp - 8) (BitVec.ofNat 64 next) 64, pc := t }
  | .ret => do some { s with rsp := s.rsp + 8, pc := (← load s.mem s.rsp 64).toNat }
  | .push r => some { s with rsp := s.rsp - 8, mem := store s.mem (s.rsp - 8) (s.get r) 64 }
  | .pop r => do some ({ s with rsp := s.rsp + 8 }.set r (← load s.mem s.rsp 64))
  | .cpuid => do
    let l ← cpuidOf cpu (trunc 32 s.rax) (trunc 32 s.rcx)
    some { s with rax := l.eax.setWidth 64, rbx := l.ebx.setWidth 64, rcx := l.ecx.setWidth 64, rdx := l.edx.setWidth 64 }
  -- XGETBV faults (#UD) unless the OS set CR4.OSXSAVE, which CPUID leaf 1 reports in ECX bit 27;
  -- XCR0 is register 0.
  | .xgetbv =>
    if cpu.leaf1.ecx.getLsbD 27 ∧ trunc 32 s.rcx = 0 then
      some { s with rax := trunc 32 cpu.xcr0, rdx := cpu.xcr0 >>> 32 }
    else none

/-- The program counter a top-level `ret` returns to: reaching it ends the run. -/
def done : Nat := 0

/-- Run to the end: at most `fuel` instructions. -/
def run (prog : Nat → Option (Instr × Nat)) (cpu : Cpu) : Nat → State → Option State
  | 0, _ => none
  | fuel + 1, s =>
    if s.pc = done then some s
    else match prog s.pc with
      | none => none
      | some (i, next) => (step cpu i next s).bind (run prog cpu fuel)

end X86
