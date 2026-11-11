import Simd
import Code
import Generic
open Simd

/-- The specification's text (Generic.lean) at 32-bit words. -/
instance : Blake3Generic.Rotr (BitVec 32) := ⟨fun x n => x.rotateRight n⟩
instance : Blake3Generic.Halves (BitVec 64) (BitVec 32) := ⟨fun t => t.setWidth 32, fun t => (t >>> 32).setWidth 32⟩

def specCv (h : Vector (BitVec 32) 8) (m : Vector (BitVec 32) 16) (t : BitVec 64) (len flags : BitVec 32) : Vector (BitVec 32) 8 :=
  Vector.ofFn fun i => (Blake3Generic.BLAKE3_COMPRESS h m t len flags)[Blake3.lo i]

/-- A call: the chaining value's two cells at RDI, the block's four at RSI, the length in RDX,
the counter in RCX, the flags in R8. -/
def call (cv0 cv1 b0 b1 b2 b3 : V) (len counter flags : BitVec 64) : State :=
  { rax := 0, rcx := counter, rdx := len, rsi := 0x2000, rdi := 0x1000, r8 := flags, rsp := 0x8000, zf := none,
    x0 := 0, x1 := 0, x2 := 0, x3 := 0, x4 := 0, x5 := 0, x6 := 0, x7 := 0, x8 := 0, x9 := 0, x10 := 0, x11 := 0,
    x12 := 0, x13 := 0, x14 := 0, x15 := 0,
    mem := fun a => if a = 0x1000 then some cv0 else if a = 0x1010 then some cv1 else if a = 0x2000 then some b0
      else if a = 0x2010 then some b1 else if a = 0x2020 then some b2 else if a = 0x2030 then some b3 else none,
    ra := 0, pc := Code.entry }

def vec (ws : List (BitVec 32)) : V := match ws with | [a, b, c, e] => mk4 a b c e | _ => 0

/-- The model run on one input: the chaining value it leaves. -/
def runCv (h : Vector (BitVec 32) 8) (m : Vector (BitVec 32) 16) (t : BitVec 64) (len flags : BitVec 32) : Option (List (BitVec 32) × Nat) :=
  (run Code.prog 1000 0 (call (mk4 h[0] h[1] h[2] h[3]) (mk4 h[4] h[5] h[6] h[7]) (mk4 m[0] m[1] m[2] m[3]) (mk4 m[4] m[5] m[6] m[7])
    (mk4 m[8] m[9] m[10] m[11]) (mk4 m[12] m[13] m[14] m[15]) (len.setWidth 64) t (flags.setWidth 64))).bind fun (s, n) => do
    let a ← s.mem 0x1000; let b ← s.mem 0x1010
    some ([dw a 0, dw a 1, dw a 2, dw a 3, dw b 0, dw b 1, dw b 2, dw b 3], n)

def h0 : Vector (BitVec 32) 8 := Blake3Generic.IV
def m0 : Vector (BitVec 32) 16 := Vector.ofFn fun i => BitVec.ofNat 32 (0x01010101 * (i.val + 1) + 7 * i.val)
#eval runCv h0 m0 0x123456789 64 0x0b
#eval (specCv h0 m0 0x123456789 64 0x0b).toList
