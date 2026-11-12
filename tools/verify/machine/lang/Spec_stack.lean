import Machine
import MemLemmas
import Cells
import ParentSpec
import Stack
open X86

/-! # The hasher's stack in memory: what the statements of `push` and `merge` speak of

Definitions only. -/

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
