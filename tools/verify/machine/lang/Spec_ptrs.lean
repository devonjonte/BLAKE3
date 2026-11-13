import Abi
open X86

/-! # The addresses a wide kernel is given: 32 of them in memory

A wide kernel hashes many inputs at once and takes their addresses in a table of 32 (the 16-lane kernels
read the first 16). Definitions only. -/

/-- The table a caller of ours fills: lane `j` of the first `n` is given `base + stride * j`, and every
lane past them is given `base` again (it hashes the first input once more, and its result is not used). -/
def Ptrs.spread (base n stride : BitVec 64) (j : Nat) : BitVec 64 :=
  if j < n.toNat then base + stride * BitVec.ofNat 64 j else base

/-- The 32 addresses `f 0`, ..., `f 31` are in memory at `a`, eight bytes each. -/
def Ptrs.At (m : Mem) (a : BitVec 64) (f : Nat → BitVec 64) : Prop :=
  ∀ j : Nat, j < 32 → Quad m (a + BitVec.ofNat 64 (8 * j)) (f j)

/-- A table of 32 addresses in memory: 256 bytes. -/
@[abi] def Ptrs.layout : Abi.Layout (Nat → BitVec 64) := ⟨256#64, Ptrs.At⟩
