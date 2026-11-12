import Example_ladd
import Spec_lroot

/-! # Examples for `lroot`

The levels of some chunks, a key, flags, a platform, and where the root's output goes. The tool runs the
function on each and compares the result with the contract (`try_fn.py`). -/

def Lroot.examples : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Blake3.CV × Array Blake3.Node) := [
  -- two chunks: the bottom's pair is the root (AVX-512 kernel), then the same by the SSE4.1 kernel, keyed
  (0x300000#64, 0x100000#64, 0x200000#64, 0#64, 5#64, ExampleL.cv 1, ExampleL.nodes 2),
  (0x300000#64, 0x100000#64, 0x200000#64, 16#64, 3#64, ExampleL.cv 1, ExampleL.nodes 2),
  -- three: one waits, a parent above it
  (0x300000#64, 0x100000#64, 0x200000#64, 0#64, 5#64, ExampleL.cv 1, ExampleL.nodes 3),
  -- four, five, seven, eight
  (0x300000#64, 0x100000#64, 0x200000#64, 0#64, 3#64, ExampleL.cv 1, ExampleL.nodes 4),
  (0x200000#64, 0x300000#64, 0x100000#64, 0#64, 5#64, ExampleL.cv 9, ExampleL.nodes 5),
  (0x300000#64, 0x100000#64, 0x200000#64, 64#64, 5#64, ExampleL.cv 1, ExampleL.nodes 7),
  (0x300000#64, 0x100000#64, 0x200000#64, 0#64, 5#64, ExampleL.cv 1, ExampleL.nodes 8),
  -- not an example, as the contract stands: one chunk alone is its own root, made elsewhere
  (0x300000#64, 0x100000#64, 0x200000#64, 0#64, 5#64, ExampleL.cv 1, ExampleL.nodes 1)]
