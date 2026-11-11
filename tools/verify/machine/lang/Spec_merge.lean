import Abi
import Code_merge
import ParentSpec
import Stack
open X86

/-! # `merge`: what is claimed

The statement only. Its proof is in `Meets_merge.lean`; nothing there need be read. -/

/-- The 32 bytes at `a` are the chaining value `cv`: its eight words, little-endian. -/
def Cv.At (m : Mem) (a : BitVec 64) (cv : Blake3.CV) : Prop :=
  ∃ v0 v1 : V, Vec m a v0 ∧ Vec m (a + 16#64) v1 ∧ words8 v0 v1 = cv

/-- Chaining values in memory: the first at `a`, each next one 32 bytes lower. -/
def Cvs.At (m : Mem) : BitVec 64 → List Blake3.CV → Prop
  | _, [] => True
  | a, cv :: rest => Cv.At m a cv ∧ Cvs.At m (a - 32#64) rest

/-- **Memory holds, at `st`, the hasher's stack of chaining values `cvs`, the newest first:** 1792 bytes
the program may use; the count in the first eight; the values from byte 32, 32 bytes each, the
newest highest; at most 55 of them. -/
def Stack.At (m : Mem) (st : BitVec 64) (cvs : List Blake3.CV) : Prop :=
  cvs.length ≤ 55 ∧ Cells.Region m st 1792#64 ∧ Quad m st (BitVec.ofNat 64 cvs.length) ∧
  Cvs.At m (st + 32#64 * BitVec.ofNat 64 cvs.length) cvs

/-- **`merge(st, key, flags, plat, target)`.** With a stack of chaining values at `st` and the key at
`key`: on return the stack is the specification's `mergeTo` of it (while it holds more than `target`
values, the two newest become their parent node's chaining value) and the result is its count.
`plat` chooses the kernel and changes nothing else. -/
def Merge.statement : Prop :=
  ∀ (st key flags plat target : BitVec 64) (k : Blake3.CV) (cvs : List Blake3.CV),
    1#64 ≤ target → flags < 256#64 →
    Abi.Meets Code_merge.prog 0x60000 {
      args := [st, key, flags, plat, target]
      stack := 176#64
      regions := [(st, 1792#64), (key, 32#64)]
      requires := fun m => Stack.At m st cvs ∧ Cv.At m key k
      ensures := fun result m =>
        Stack.At m st (Blake3.mergeTo k ⟨flags.setWidth 32⟩ target.toNat cvs) ∧
        result.toNat = (Blake3.mergeTo k ⟨flags.setWidth 32⟩ target.toNat cvs).length
      modifies := [(st, 1792#64)] }
