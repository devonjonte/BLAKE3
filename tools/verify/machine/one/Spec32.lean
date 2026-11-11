import Machine
import Generic
open X86

/-! The specification's text (Generic.lean) at 32-bit words, and the parent node's chaining value. -/

instance : Blake3Generic.Rotr (BitVec 32) := ⟨fun x n => x.rotateRight n⟩
instance : Blake3Generic.Halves (BitVec 64) (BitVec 32) := ⟨fun t => t.setWidth 32, fun t => (t >>> 32).setWidth 32⟩

/-- The first eight words of the specification's compression: a node's chaining value. -/
def specCv (h : Vector (BitVec 32) 8) (m : Vector (BitVec 32) 16) (t : BitVec 64) (len flags : BitVec 32) : Vector (BitVec 32) 8 :=
  Vector.ofFn fun i => (Blake3Generic.BLAKE3_COMPRESS h m t len flags)[Blake3.lo i]

/-- A chaining value's eight words, as two vectors of memory hold them. -/
def cvWords (c0 c1 : V) : Vector (BitVec 32) 8 :=
  #v[dw c0 0, dw c0 1, dw c0 2, dw c0 3, dw c1 0, dw c1 1, dw c1 2, dw c1 3]

/-- A block's sixteen words, as four vectors of memory hold them. -/
def blockWords (b0 b1 b2 b3 : V) : Vector (BitVec 32) 16 :=
  #v[dw b0 0, dw b0 1, dw b0 2, dw b0 3, dw b1 0, dw b1 1, dw b1 2, dw b1 3,
    dw b2 0, dw b2 1, dw b2 2, dw b2 3, dw b3 0, dw b3 1, dw b3 2, dw b3 3]

/-- Section 2.5 and 3.1 of the specification: a parent node's chaining value. Its block is the
left child's chaining value then the right's, its counter 0, its length 64, its flags PARENT
with the mode's. -/
def parentCv (key : Vector (BitVec 32) 8) (l0 l1 r0 r1 : V) (flags : BitVec 32) : Vector (BitVec 32) 8 :=
  specCv key (blockWords l0 l1 r0 r1) 0 64 (flags ||| 4)
