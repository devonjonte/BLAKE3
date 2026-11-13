import Abi
import Spec_stack
open X86

/-! # Chaining values one after another in memory: what the wide kernels read and write

Definitions only. -/

/-- The chaining values `l` are in memory from `a` on, 32 bytes each, the first lowest. -/
def Cvl.At (m : Mem) : BitVec 64 → List Blake3.CV → Prop
  | _, [] => True
  | a, cv :: rest => Cv.At m a cv ∧ Cvl.At m (a + 32#64) rest

/-- Sixteen chaining values at `a`: 512 bytes. -/
def Cvs16.At (m : Mem) (a : BitVec 64) (l : List Blake3.CV) : Prop := l.length = 16 ∧ Cvl.At m a l
@[abi] def Cvs16.layout : Abi.Layout (List Blake3.CV) := ⟨512#64, Cvs16.At⟩

/-- Thirty-two chaining values at `a`: 1024 bytes. -/
def Cvs32.At (m : Mem) (a : BitVec 64) (l : List Blake3.CV) : Prop := l.length = 32 ∧ Cvl.At m a l
@[abi] def Cvs32.layout : Abi.Layout (List Blake3.CV) := ⟨1024#64, Cvs32.At⟩

/-- `n` pairs of chaining values at `a` (each pair is a parent's 64-byte block; at most 16 pairs): `64 n` bytes. -/
def Pairs.At (n : BitVec 64) (m : Mem) (a : BitVec 64) (l : List Blake3.CV) : Prop :=
  n ≤ 16#64 ∧ l.length = 2 * n.toNat ∧ Cvl.At m a l
@[abi] def Pairs.layout (n : BitVec 64) : Abi.Layout (List Blake3.CV) := ⟨n <<< 6, Pairs.At n⟩
