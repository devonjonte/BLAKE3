import Stack
import Contract

/-! # The hasher's stack as bytes

What it means for bytes to hold a chaining value, or the hasher's stack of them. Definitions only; no
machine and no memory are named, so a contract written with these says the same of the code for any
architecture: each machine model adds only "these bytes are at this address". -/

namespace Bytes

/-- The eight bytes of a count, lowest first. -/
def le64 (n : Nat) : List (BitVec 8) := (List.range 8).map fun i => (BitVec.ofNat 64 n).extractLsb' (8 * i) 8

/-- The four bytes of a word, lowest first. -/
def le32 (w : Blake3.Word) : List (BitVec 8) := (List.range 4).map fun i => w.toBitVec.extractLsb' (8 * i) 8

end Bytes

/-- The 32 bytes of a chaining value: its eight words, each lowest byte first. -/
def Cv.bytes (cv : Blake3.CV) : List (BitVec 8) := cv.toList.flatMap Bytes.le32

/-- **The bytes `b` hold the hasher's stack of chaining values `cvs`, the newest first:** 1792 bytes; the
count in the first eight; 24 bytes not used; then the values, 32 bytes each, the oldest first; the bytes
after them not used. At most 55 values. -/
def Stack.Holds (b : List (BitVec 8)) (cvs : List Blake3.CV) : Prop :=
  cvs.length ≤ 55 ∧ b.length = 1792 ∧
  ∃ unused after : List (BitVec 8), unused.length = 24 ∧
    b = Bytes.le64 cvs.length ++ unused ++ cvs.reverse.flatMap Cv.bytes ++ after

/-- A chaining value in memory: 32 bytes. -/
def Cv.byteLayout : Bytes.Layout Blake3.CV := ⟨32, fun b cv => b = Cv.bytes cv⟩

/-- The hasher's stack in memory: 1792 bytes. -/
def Stack.byteLayout : Bytes.Layout (List Blake3.CV) := ⟨1792, Stack.Holds⟩
