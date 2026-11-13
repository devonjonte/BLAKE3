import Try
import Sample_stack
import Spec_node
open X86

/-! # A node, for trying functions on examples

How to put one into memory and how to test that memory holds one. Test-side: not proved against `Node.At`. -/

/-- The 88 bytes after a node's `h`. -/
def Node.tailBytes (n : Blake3.Node) : List (BitVec 8) :=
  (n.m.toList.flatMap fun (w : UInt32) => (List.range 4).map fun i => BitVec.setWidth 8 (w.toBitVec >>> (8 * i))) ++
  Try.le64 n.t.toBitVec ++ Try.le64 (n.len.toBitVec.setWidth 64) ++ Try.le64 (n.flags.toBitVec.setWidth 64)

def Node.bytes (n : Blake3.Node) : List (BitVec 8) := Cv.bytes n.h ++ Node.tailBytes n

def NodeTail.sample : Try.Sample Blake3.Node where
  put := fun m a n => Try.fill m a (Node.tailBytes n).toArray
  check := fun m a n => decide (n.len.toBitVec ≤ 64#32) && decide (n.flags.toBitVec < 256#32) && Try.bytes? m a 88 == some (Node.tailBytes n)

def Node.sample : Try.Sample Blake3.Node where
  put := fun m a n => Try.fill m a (Node.bytes n).toArray
  check := fun m a n => decide (n.len.toBitVec ≤ 64#32) && decide (n.flags.toBitVec < 256#32) && Try.bytes? m a 120 == some (Node.bytes n)
