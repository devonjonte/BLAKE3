import Abi
import Spec_stack
open X86

/-! # A node of the tree in memory: what the statements of the whole hash's functions speak of

Definitions only. -/

/-- The 64 bytes at `a` are the block `b`: its sixteen words, little-endian. -/
def Block.At (m : Mem) (a : BitVec 64) (b : Vector Blake3.Word 16) : Prop :=
  ∃ v0 v1 v2 v3 : V, Vec m a v0 ∧ Vec m (a + 16#64) v1 ∧ Vec m (a + 32#64) v2 ∧ Vec m (a + 48#64) v3 ∧
    words8 v0 v1 ++ words8 v2 v3 = b

/-- The 88 bytes after a node's `h`: its block `m` in 64, then its counter `t`, its block length and its
flags, eight bytes each. The length is at most 64 and the flags are below 256. -/
def Node.Tail (m : Mem) (a : BitVec 64) (n : Blake3.Node) : Prop :=
  Block.At m a n.m ∧ Quad m (a + 64#64) n.t.toBitVec ∧
  Quad m (a + 72#64) (n.len.toBitVec.setWidth 64) ∧ Quad m (a + 80#64) (n.flags.toBitVec.setWidth 64) ∧
  n.len.toBitVec ≤ 64#32 ∧ n.flags.toBitVec < 256#32

/-- **Memory holds, at `a`, the node `n` of the tree** (the inputs of a compression: C2SP's BLAKE3,
section 4.3): 120 bytes. Its `h` in the first 32, and the rest (`Node.Tail`) in the 88 after them. -/
def Node.At (m : Mem) (a : BitVec 64) (n : Blake3.Node) : Prop := Cv.At m a n.h ∧ Node.Tail m (a + 32#64) n

/-- A node in memory: 120 bytes. -/
@[abi] def Node.layout : Abi.Layout Blake3.Node := ⟨120#64, Node.At⟩

/-- A node without its `h`: the 88 bytes after it. -/
@[abi] def NodeTail.layout : Abi.Layout Blake3.Node := ⟨88#64, Node.Tail⟩

/-- The first eight words of a node's compression with the flags `extra` besides its own. With none they
are the node's chaining value (`Blake3.Node.cv`); with `ROOT`, for a node whose counter is 0, they are the
first 32 bytes of its output (`Blake3.output`, sections 4.3.2 and 4.4). -/
def Node.out (n : Blake3.Node) (extra : Blake3.Word) : Blake3.CV :=
  Blake3.first8 (Blake3.BLAKE3_COMPRESS n.h n.m n.t n.len (n.flags ||| extra))
