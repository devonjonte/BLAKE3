import Abi
open X86

/-! # Plain bytes in memory

Definitions only. -/

/-- The bytes `bs` are at `a`, one after another. -/
def Bytes.At (m : Mem) (a : BitVec 64) (bs : List (BitVec 8)) : Prop :=
  ∀ (i : Nat) (h : i < bs.length), m (a + BitVec.ofNat 64 i) = some bs[i]

/-- `n` bytes in memory. -/
@[abi] def Bytes.layout (n : Nat) : Abi.Layout (List (BitVec 8)) :=
  ⟨BitVec.ofNat 64 n, fun m a bs => bs.length = n ∧ Bytes.At m a bs⟩
