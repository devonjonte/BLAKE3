import Bytes

/-! # A small x86-64 for a function of the crate

Ten registers, three vector registers, ZF and CF, memory as the bytes the program owns (Bytes.lean), and what an observer of
time and cache may learn. Anything not modelled is a fault. -/

namespace X86

inductive Reg | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi | r8 | r9
  deriving DecidableEq, Repr

/-- What an observer of time and cache may learn from one instruction: an address it reads or
writes, and where a conditional jump or a return goes. (Every instruction modelled here takes
the same time whatever its operands' values; one that does not, a division, is not modelled.) -/
inductive Obs
  | addr (a : BitVec 64)
  | pc (n : Nat)

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
  x0 : BitVec 128
  x1 : BitVec 128
  x2 : BitVec 128
  zf : Option Bool
  cf : Option Bool
  mem : Mem
  pc : Nat
  /-- Everything observed so far, newest first. -/
  leak : List Obs

def State.get (s : State) : Reg → BitVec 64
  | .rax => s.rax | .rcx => s.rcx | .rdx => s.rdx | .rbx => s.rbx
  | .rsp => s.rsp | .rbp => s.rbp | .rsi => s.rsi | .rdi => s.rdi | .r8 => s.r8 | .r9 => s.r9

def State.set (s : State) (r : Reg) (v : BitVec 64) : State :=
  match r with
  | .rax => { s with rax := v } | .rcx => { s with rcx := v } | .rdx => { s with rdx := v } | .rbx => { s with rbx := v }
  | .rsp => { s with rsp := v } | .rbp => { s with rbp := v } | .rsi => { s with rsi := v } | .rdi => { s with rdi := v }
  | .r8 => { s with r8 := v } | .r9 => { s with r9 := v }

def State.xmm (s : State) : Nat → BitVec 128
  | 0 => s.x0 | 1 => s.x1 | _ => s.x2

def State.setx (s : State) (i : Nat) (v : BitVec 128) : State :=
  match i with
  | 0 => { s with x0 := v } | 1 => { s with x1 := v } | _ => { s with x2 := v }

def trunc (w : Nat) (v : BitVec 64) : BitVec 64 :=
  match w with
  | 8 => v &&& 0xFF
  | 32 => v &&& 0xFFFFFFFF
  | _ => v

inductive Opnd
  | reg (r : Reg)
  | mem (base : Reg) (disp : BitVec 64)
  /-- `[base + index]` -/
  | memi (base index : Reg)
  /-- `[base + scale*index + disp]` -/
  | mems (base index : Reg) (scale disp : BitVec 64)
  | imm (v : BitVec 64)

inductive Cond | e | ne

inductive Instr
  | mov (w : Nat) (dst src : Opnd)
  | xor (w : Nat) (dst src : Opnd)
  | and (w : Nat) (dst src : Opnd)
  | or (w : Nat) (dst src : Opnd)
  | add (w : Nat) (dst src : Opnd)
  | test (w : Nat) (a b : Opnd)
  | cmp (w : Nat) (a b : Opnd)
  | shl (w : Nat) (dst : Opnd) (n : Nat)
  | shr (w : Nat) (dst : Opnd) (n : Nat)
  | jmp (target : Nat)
  /-- Any length of NOP: padding before a loop. -/
  | nop
  | not (w : Nat) (dst : Opnd)
  /-- `lea r32, [base + index + disp]`: arithmetic only, no memory is touched. -/
  | lea32 (dst base index : Reg) (disp : BitVec 64)
  /-- MOVZX r32, r/m8 -/
  | movzx8 (dst : Reg) (src : Opnd)
  /-- MOVUPS xmm, m128 and MOVUPS m128, xmm -/
  | loadv (dst : Nat) (src : Opnd)
  | storev (dst : Opnd) (src : Nat)
  | rol32 (dst : Reg) (n : Nat)
  | jcc (c : Cond) (target : Nat)
  | ret
  | push (r : Reg)
  | pop (r : Reg)

def byte (v : BitVec 64) (i : Nat) : BitVec 8 := (v >>> (8 * i)).setWidth 8

def _root_.Mem.read8 (m : Mem) (a : BitVec 64) : Option (BitVec 64) := (m a).map (BitVec.setWidth 64)

/-- `w` bits at `a`, little-endian (w is 8, 32 or 64). -/
def _root_.Mem.read (m : Mem) (a : BitVec 64) : Nat → Option (BitVec 64)
  | 8 => m.read8 a
  | 32 => do
    let b0 ← m.read8 a; let b1 ← m.read8 (a + 1); let b2 ← m.read8 (a + 2); let b3 ← m.read8 (a + 3)
    pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24))
  | _ => do
    let b0 ← m.read8 a; let b1 ← m.read8 (a + 1); let b2 ← m.read8 (a + 2); let b3 ← m.read8 (a + 3)
    let b4 ← m.read8 (a + 4); let b5 ← m.read8 (a + 5); let b6 ← m.read8 (a + 6); let b7 ← m.read8 (a + 7)
    pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56))

/-- One byte written at `a`: a fault unless the program owns it. -/
def _root_.Mem.write8 (m : Mem) (a : BitVec 64) (v : BitVec 8) : Option Mem :=
  if (m a).isSome then some (m.put8 a v) else none

def _root_.Mem.write (m : Mem) (a : BitVec 64) (v : BitVec 64) : Nat → Option Mem
  | 8 => m.write8 a (byte v 0)
  | 32 => do
    let m ← m.write8 a (byte v 0); let m ← m.write8 (a + 1) (byte v 1)
    let m ← m.write8 (a + 2) (byte v 2); m.write8 (a + 3) (byte v 3)
  | _ => do
    let m ← m.write8 a (byte v 0); let m ← m.write8 (a + 1) (byte v 1)
    let m ← m.write8 (a + 2) (byte v 2); let m ← m.write8 (a + 3) (byte v 3)
    let m ← m.write8 (a + 4) (byte v 4); let m ← m.write8 (a + 5) (byte v 5)
    let m ← m.write8 (a + 6) (byte v 6); m.write8 (a + 7) (byte v 7)

/-- The sixteen bytes at `a`, as a vector. -/
def _root_.Mem.read128 (m : Mem) (a : BitVec 64) : Option (BitVec 128) := do
  let b0 ← m (a + 0); let b1 ← m (a + 1); let b2 ← m (a + 2); let b3 ← m (a + 3); let b4 ← m (a + 4); let b5 ← m (a + 5); let b6 ← m (a + 6); let b7 ← m (a + 7)
  let b8 ← m (a + 8); let b9 ← m (a + 9); let b10 ← m (a + 10); let b11 ← m (a + 11); let b12 ← m (a + 12); let b13 ← m (a + 13); let b14 ← m (a + 14); let b15 ← m (a + 15)
  pure (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)

def by8 (v : BitVec 128) (i : Nat) : BitVec 8 := v.extractLsb' (8 * i) 8

def _root_.Mem.write128 (m : Mem) (a : BitVec 64) (v : BitVec 128) : Option Mem := do
  let m ← m.write8 (a + 0) (by8 v 0); let m ← m.write8 (a + 1) (by8 v 1); let m ← m.write8 (a + 2) (by8 v 2); let m ← m.write8 (a + 3) (by8 v 3)
  let m ← m.write8 (a + 4) (by8 v 4); let m ← m.write8 (a + 5) (by8 v 5); let m ← m.write8 (a + 6) (by8 v 6); let m ← m.write8 (a + 7) (by8 v 7)
  let m ← m.write8 (a + 8) (by8 v 8); let m ← m.write8 (a + 9) (by8 v 9); let m ← m.write8 (a + 10) (by8 v 10); let m ← m.write8 (a + 11) (by8 v 11)
  let m ← m.write8 (a + 12) (by8 v 12); let m ← m.write8 (a + 13) (by8 v 13); let m ← m.write8 (a + 14) (by8 v 14); m.write8 (a + 15) (by8 v 15)

def addr (s : State) : Opnd → BitVec 64
  | .mem b d => s.get b + d
  | .memi b i => s.get b + s.get i
  | .mems b i sc d => s.get b + s.get i * sc + d
  | _ => 0

def read (s : State) (w : Nat) : Opnd → Option (BitVec 64)
  | .reg r => some (trunc w (s.get r))
  | .imm v => some (trunc w v)
  | o => s.mem.read (addr s o) w

/-- Writing 32 bits of a register clears its upper half; writing 8 keeps the other 56. -/
def write (s : State) (w : Nat) (o : Opnd) (v : BitVec 64) : Option State :=
  match o with
  | .reg r => some (s.set r (match w with
      | 8 => (s.get r &&& ~~~(0xFF : BitVec 64)) ||| (v &&& 0xFF)
      | 32 => v &&& 0xFFFFFFFF
      | _ => v))
  | .imm _ => none
  | o => do some { s with mem := (← s.mem.write (addr s o) v w) }

/-- The address an operand names, as an observation. -/
def seen (s : State) : Opnd → List Obs
  | .mem b d => [.addr (s.get b + d)]
  | .memi b i => [.addr (s.get b + s.get i)]
  | .mems b i sc d => [.addr (s.get b + s.get i * sc + d)]
  | _ => []

/-- The addresses an instruction touches, from the state before it. -/
def touched (s : State) : Instr → List Obs
  | .mov _ d x | .xor _ d x | .and _ d x | .or _ d x | .add _ d x | .test _ d x | .cmp _ d x => seen s d ++ seen s x
  | .shl _ d _ | .shr _ d _ | .not _ d | .storev d _ => seen s d
  | .movzx8 _ x | .loadv _ x => seen s x
  | .rol32 _ _ | .jcc _ _ | .jmp _ | .lea32 _ _ _ _ | .nop => []
  | .ret | .pop _ => [.addr s.rsp]
  | .push _ => [.addr (s.rsp - 8)]

def holds (s : State) : Cond → Option Bool
  | .e => s.zf
  | .ne => s.zf.map (!·)

def logic (s : State) (w : Nat) (v : BitVec 64) : State :=
  { s with zf := some (trunc w v == 0), cf := some false }

/-- One instruction at `s.pc`, the next one at `next` unless it jumps. -/
def step (i : Instr) (next : Nat) (s : State) : Option State :=
  let s := { s with pc := next, leak := touched s i ++ s.leak }
  match i with
  | .mov w d x => do write s w d (← read s w x)
  | .xor w d x => do let v := (← read s w d) ^^^ (← read s w x); write (logic s w v) w d v
  | .and w d x => do let v := (← read s w d) &&& (← read s w x); write (logic s w v) w d v
  | .or w d x => do let v := (← read s w d) ||| (← read s w x); write (logic s w v) w d v
  | .test w a b => do let v := (← read s w a) &&& (← read s w b); some (logic s w v)
  | .add w d x => do
    let a ← read s w d; let b ← read s w x; let v := trunc w (a + b)
    write { s with zf := some (v == 0), cf := some (v.ult a) } w d v
  | .cmp w a b => do
    let a ← read s w a; let b ← read s w b
    some { s with zf := some (trunc w (a - b) == 0), cf := some (a.ult b) }
  | .shl w d n => do let v := trunc w ((← read s w d) <<< n); write { s with zf := some (v == 0), cf := none } w d v
  -- A shift right's CF is the last bit out: left unmodelled.
  | .shr w d n => do let v := trunc w (← read s w d) >>> n; write { s with zf := some (v == 0), cf := none } w d v
  | .jmp t => some { s with pc := t }
  | .nop => some s
  | .movzx8 r x => do some (s.set r (← read s 8 x))
  | .loadv i x => do some (s.setx i (← s.mem.read128 (addr s x)))
  | .storev d i => do some { s with mem := (← s.mem.write128 (addr s d) (s.xmm i)) }
  | .not w d => do write s w d (~~~ (← read s w d))
  | .lea32 d b i disp => some (s.set d ((s.get b + s.get i + disp) &&& 0xFFFFFFFF))
  -- A rotate leaves ZF alone; CF is the bit rotated in, left unmodelled.
  | .rol32 r n => some ({ s with cf := none }.set r ((((s.get r).setWidth 32).rotateLeft n).setWidth 64))
  | .jcc c t => do some (if (← holds s c) then { s with pc := t, leak := .pc t :: s.leak } else { s with leak := .pc next :: s.leak })
  | .ret => do
    let to := (← s.mem.read s.rsp 64).toNat
    some { s with rsp := s.rsp + 8, pc := to, leak := .pc to :: s.leak }
  | .push r => do some { s with rsp := s.rsp - 8, mem := (← s.mem.write (s.rsp - 8) (s.get r) 64) }
  | .pop r => do some ({ s with rsp := s.rsp + 8 }.set r (← s.mem.read s.rsp 64))

/-- The program counter a top-level `ret` returns to: reaching it ends the run. -/
def done : Nat := 0

/-- Exactly `k` instructions. -/
def steps (prog : Nat → Option (Instr × Nat)) : Nat → State → Option State
  | 0, s => some s
  | k + 1, s =>
    match prog s.pc with
    | none => none
    | some (i, next) => (step i next s).bind (steps prog k)

/-- The program, started in `s`, returns in `s'`. -/
def Returns (prog : Nat → Option (Instr × Nat)) (s s' : State) : Prop :=
  ∃ k, steps prog k s = some s' ∧ s'.pc = done

end X86
