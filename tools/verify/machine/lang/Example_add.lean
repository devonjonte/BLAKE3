import Sample_stack
import Spec_add

/-! # Examples for `add`

Situations its contract covers, written by hand: a stack, a key, flags, a platform, a value that arrives, a
target. The tool runs the function on each, through its calls, and compares the result with the contract
(`try_fn.py`). -/

/-- A chaining value made from a number. -/
def ExampleAdd.cv (seed : Nat) : Blake3.CV :=
  Vector.ofFn fun i => UInt32.ofNat (seed * 2654435761 + i.val * 40503 + 12345)

def Add.examples : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Blake3.CV × Blake3.CV × List Blake3.CV) := [
  -- the second chunk's value arrives: one value held, merged to one
  (0x100000#64, 0x200000#64, 0#64, 5#64, 0x300000#64, 1#64, ExampleAdd.cv 1, ExampleAdd.cv 2, [ExampleAdd.cv 3]),
  -- the third's: two held, kept apart (target 3)
  (0x100000#64, 0x200000#64, 0#64, 5#64, 0x300000#64, 3#64, ExampleAdd.cv 1, ExampleAdd.cv 2, [ExampleAdd.cv 3, ExampleAdd.cv 4]),
  -- keyed, by the SSE4.1 kernel: three held, merged to two
  (0x100000#64, 0x200000#64, 16#64, 3#64, 0x300000#64, 2#64, ExampleAdd.cv 1, ExampleAdd.cv 2, [ExampleAdd.cv 3, ExampleAdd.cv 4, ExampleAdd.cv 5]),
  -- onto an empty stack
  (0x100000#64, 0x200000#64, 0#64, 5#64, 0x300000#64, 1#64, ExampleAdd.cv 1, ExampleAdd.cv 2, []),
  -- not an example, as the contract stands: a full stack
  (0x100000#64, 0x200000#64, 0#64, 5#64, 0x300000#64, 1#64, ExampleAdd.cv 1, ExampleAdd.cv 2, (List.range 55).map fun i => ExampleAdd.cv (100 + i))]
