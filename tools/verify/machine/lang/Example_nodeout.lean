import Sample_node
import Spec_nodeout

/-! # Examples for `node_out`

A node, where its value goes, the root flag or none, a platform. The tool runs the function on each and
compares the result with the contract (`try_fn.py`). -/

/-- A node made from a number, with a block length, a counter and flags. -/
def ExampleN.node (seed len : Nat) (t : UInt64) (flags : UInt32) : Blake3.Node :=
  { h := Vector.ofFn fun i => UInt32.ofNat (seed * 2654435761 + i.val * 40503 + 12345),
    m := Vector.ofFn fun i => UInt32.ofNat (seed * 97 + i.val * 65537), t := t, len := UInt32.ofNat len, flags := flags }

def NodeOut.examples : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Blake3.Node) := [
  -- a whole chunk's last block, not the root: both kernels
  (0x300000#64, 0x100000#64, 0#64, 5#64, ExampleN.node 1 64 7 2),
  (0x300000#64, 0x100000#64, 0#64, 3#64, ExampleN.node 1 64 7 2),
  -- a short only chunk, the root: both kernels; keyed
  (0x300000#64, 0x100000#64, 8#64, 5#64, ExampleN.node 2 5 0 3),
  (0x200000#64, 0x100000#64, 8#64, 3#64, ExampleN.node 3 0 0 19),
  -- a parent as the root
  (0x300000#64, 0x100000#64, 8#64, 4#64, ExampleN.node 4 64 0 4),
  -- not examples: a flag that is neither; a block length over 64
  (0x300000#64, 0x100000#64, 2#64, 5#64, ExampleN.node 1 64 7 2),
  (0x300000#64, 0x100000#64, 0#64, 5#64, ExampleN.node 1 65 7 2)]
