import Sample_stack
import Spec_push

/-! # Examples for `push`

Situations its contract covers, written by hand: a stack, a value to push. The tool runs the function on
each and compares the result with the contract (`try_fn.py`). -/

/-- A chaining value made from a number. -/
def ExamplePush.cv (seed : Nat) : Blake3.CV :=
  Vector.ofFn fun i => UInt32.ofNat (seed * 2654435761 + i.val * 40503 + 12345)

def Push.examples : List (BitVec 64 × BitVec 64 × Blake3.CV × List Blake3.CV) := [
  -- onto an empty stack
  (0x100000#64, 0x200000#64, ExamplePush.cv 1, []),
  -- onto three values
  (0x100000#64, 0x200000#64, ExamplePush.cv 1, [ExamplePush.cv 2, ExamplePush.cv 3, ExamplePush.cv 4]),
  -- the last place: onto 54 values
  (0x300000#64, 0x100000#64, ExamplePush.cv 7, (List.range 54).map fun i => ExamplePush.cv (100 + i)),
  -- not an example, as the contract stands: a full stack (the contract does not accept it)
  (0x100000#64, 0x200000#64, ExamplePush.cv 1, (List.range 55).map fun i => ExamplePush.cv (100 + i))]
