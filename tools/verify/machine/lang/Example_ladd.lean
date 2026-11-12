import Sample_levels
import Spec_ladd

/-! # Examples for `ladd`

Situations its contract covers, written by hand: the levels of some chunks, a key, flags, a platform, a
new chunk. The tool runs the function on each and compares the result with the contract (`try_fn.py`).
At least one must meet what the contract requires. -/

/-- A chaining value made from a number. -/
def ExampleL.cv (seed : Nat) : Blake3.CV :=
  Vector.ofFn fun i => UInt32.ofNat (seed * 2654435761 + i.val * 40503 + 12345)

/-- A chunk's node made from a number (any node will do: the levels use its chaining value alone). -/
def ExampleL.node (seed : Nat) : Blake3.Node :=
  { h := ExampleL.cv seed, m := Vector.ofFn fun i => UInt32.ofNat (seed * 97 + i.val), t := 0, len := 64, flags := 0 }

def ExampleL.nodes (n : Nat) : Array Blake3.Node := (Array.range n).map fun i => ExampleL.node (100 + i)

def Ladd.examples : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Blake3.CV × Array Blake3.Node × Blake3.Node) := [
  -- the first chunk: nothing to give upward
  (0x100000#64, 0x200000#64, 0#64, 5#64, 0x300000#64, ExampleL.cv 1, ExampleL.nodes 0, ExampleL.node 7),
  -- the second: it waits beside the first
  (0x100000#64, 0x200000#64, 0#64, 5#64, 0x300000#64, ExampleL.cv 1, ExampleL.nodes 1, ExampleL.node 7),
  -- the third: the first pair becomes a parent (AVX-512 kernel), then the same by the SSE4.1 kernel, keyed
  (0x100000#64, 0x200000#64, 0#64, 5#64, 0x300000#64, ExampleL.cv 1, ExampleL.nodes 2, ExampleL.node 7),
  (0x100000#64, 0x200000#64, 16#64, 3#64, 0x300000#64, ExampleL.cv 1, ExampleL.nodes 2, ExampleL.node 7),
  -- the fifth: two parents, one above the other
  (0x300000#64, 0x100000#64, 0#64, 5#64, 0x200000#64, ExampleL.cv 9, ExampleL.nodes 4, ExampleL.node 8),
  -- the sixth and seventh: none, then one beside a parent that waits
  (0x100000#64, 0x200000#64, 0#64, 3#64, 0x300000#64, ExampleL.cv 1, ExampleL.nodes 5, ExampleL.node 7),
  (0x100000#64, 0x200000#64, 0#64, 5#64, 0x300000#64, ExampleL.cv 1, ExampleL.nodes 6, ExampleL.node 7),
  -- the ninth: three parents
  (0x100000#64, 0x200000#64, 64#64, 5#64, 0x300000#64, ExampleL.cv 1, ExampleL.nodes 8, ExampleL.node 7),
  -- not an example, as the contract stands: flags of 256 or more
  (0x100000#64, 0x200000#64, 0x10000#64, 3#64, 0x300000#64, ExampleL.cv 1, ExampleL.nodes 2, ExampleL.node 7)]
