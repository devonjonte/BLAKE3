import Sample_stack
import Spec_merge

/-! # Examples for `merge`

Situations its contract covers, written by hand: a stack, a key, flags, a platform, a target. The tool
runs the function on each and compares the result with the contract (`try_fn.py`). At least one must
meet what the contract requires: a contract no example can meet is a contract nobody can use. -/

/-- A chaining value made from a number. -/
def Example.cv (seed : Nat) : Blake3.CV :=
  Vector.ofFn fun i => UInt32.ofNat (seed * 2654435761 + i.val * 40503 + 12345)

def Merge.examples : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Blake3.CV × List Blake3.CV) := [
  -- three values to one, by the AVX-512 kernel
  (0x100000#64, 0x200000#64, 0#64, 5#64, 1#64, Example.cv 1, [Example.cv 2, Example.cv 3, Example.cv 4]),
  -- the same by the SSE4.1 kernel, keyed
  (0x100000#64, 0x200000#64, 16#64, 3#64, 1#64, Example.cv 1, [Example.cv 2, Example.cv 3, Example.cv 4]),
  -- five values to two
  (0x300000#64, 0x100000#64, 0#64, 5#64, 2#64, Example.cv 9, [Example.cv 5, Example.cv 6, Example.cv 7, Example.cv 8, Example.cv 10]),
  -- nothing to do: two values, target two
  (0x100000#64, 0x200000#64, 0#64, 5#64, 2#64, Example.cv 1, [Example.cv 2, Example.cv 3]),
  -- fewer values than the target: one value, target three (the result is the count, not the target)
  (0x100000#64, 0x200000#64, 0#64, 5#64, 3#64, Example.cv 1, [Example.cv 2]),
  -- not examples, as the contract stands (it does not accept these arguments); they are here so that a
  -- contract that came to accept them would be tried on them: a target of zero, and flags of 256 or more
  (0x100000#64, 0x200000#64, 0#64, 5#64, 0#64, Example.cv 1, [Example.cv 2]),
  (0x100000#64, 0x200000#64, 0x10000#64, 3#64, 1#64, Example.cv 1, [Example.cv 2, Example.cv 3]),
  -- a full stack to one
  (0x100000#64, 0x200000#64, 64#64, 3#64, 1#64, Example.cv 1, (List.range 55).map fun i => Example.cv (100 + i))]
