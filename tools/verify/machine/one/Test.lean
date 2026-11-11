import Machine
import Code
import Spec32
open X86

/-! The model run on one input, beside the specification (no proof: a check that the model,
the lifted code and the layout assumed below agree before anything is proved). -/

def bytesOf (v : V) : List (BitVec 8) := (List.range 16).map (by8 v)

/-- Memory from regions of bytes at fixed addresses. -/
def memOf (regions : List (BitVec 64 × List (BitVec 8))) : Mem := fun a =>
  regions.findSome? fun (base, bs) => if (a - base).toNat < bs.length then bs[(a - base).toNat]? else none

/-- Run until the return to address 0. -/
def run : Nat → State → Option State
  | 0, _ => none
  | fuel + 1, s => if s.pc = 0 then some s else
    match Code.prog s.pc with
    | none => none
    | some (i, next) => (step i next s).bind (run fuel)

def zeros (n : Nat) : List (BitVec 8) := List.replicate n 0
def st (pc : Nat) (rdi rsi rdx rcx r8 r9 : BitVec 64) (m : Mem) : State :=
  { rax := 0, rcx, rdx, rbx := 0xB, rsp := 0x7FF8, rbp := 0, rsi, rdi, r8, r9, r12 := 0, r13 := 0, r14 := 0, r15 := 0,
    zf := none, cf := none, x0 := 0, x1 := 0, x2 := 0, x3 := 0, x4 := 0, x5 := 0, x6 := 0, x7 := 0, x8 := 0, x9 := 0,
    x10 := 0, x11 := 0, x12 := 0, x13 := 0, x14 := 0, x15 := 0, mem := m, pc }

def vOf (f : Nat → Nat) : V := mk4 (BitVec.ofNat 32 (f 0)) (BitVec.ofNat 32 (f 1)) (BitVec.ofNat 32 (f 2)) (BitVec.ofNat 32 (f 3))
def l0 := vOf fun i => 0x11111111 * (i + 1)
def l1 := vOf fun i => 0x01020304 + 77 * i
def r0 := vOf fun i => 0xDEADBEEF - 1234567 * i
def r1 := vOf fun i => 0x0BADF00D + 99 * i
def k0 := vOf fun i => 0x6a09e667 + 5 * i
def k1 := vOf fun i => 0x510e527f + 7 * i

/-- parent_output(O = 0x3000; left 0x1000, right 0x1100, key 0x1200, flags, platform), then
chaining_value(out = 0x2000, O): the eight words left at 0x2000. -/
def parentRun (flags platform : BitVec 64) : Option (List (BitVec 32)) := do
  let m := memOf [(0x1000, bytesOf l0 ++ bytesOf l1), (0x1100, bytesOf r0 ++ bytesOf r1), (0x1200, bytesOf k0 ++ bytesOf k1),
    (0x2000, zeros 32), (0x3000, zeros 0x80), (0x7F00, zeros 0x100)]
  let s1 ← run 100 (st 0x10000 0x3000 0x1000 0x1100 0x1200 flags platform m)
  let s2 ← run 2000 (st 0x11000 0x2000 0x3000 0 0 0 0 s1.mem)
  let a ← s2.mem.read128 0x2000; let b ← s2.mem.read128 0x2010
  some [dw a 0, dw a 1, dw a 2, dw a 3, dw b 0, dw b 1, dw b 2, dw b 3]

#eval parentRun 0x10 5
#eval parentRun 0x10 2
#eval (parentCv (cvWords k0 k1) l0 l1 r0 r1 0x10).toList
