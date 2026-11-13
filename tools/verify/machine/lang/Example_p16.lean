import Sample_cvl
import Sample_ptrs
import Spec_p16

/-! # Examples for the 16-lane parent kernel's contract

For a function that stands in for the kernel in this model (`p16s`): the table, one block, the key's address,
counter 0, the packed flags, where the 16 values go; then the key, where the pairs are, how many, the mode's
flags, the pairs. The tool runs the stand-in on each and compares the result with the contract (`try_fn.py`). -/

def ExampleT.cv (i : Nat) : Blake3.CV := Vector.ofFn fun j => UInt32.ofNat (i * 2654435761 + j.val * 40503 + 7)
def ExampleT.cvs (n : Nat) : List Blake3.CV := (List.range n).map fun i => ExampleT.cv (100 + i)

def P16.examples : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Blake3.CV × BitVec 64 × BitVec 64 × BitVec 64 × List Blake3.CV) := [
  (0x100000#64, 1#64, 0x200000#64, 0#64, 0x40000004#64, 0x300000#64, ExampleT.cv 1, 0x400000#64, 16#64, 0#64, ExampleT.cvs 32),
  (0x100000#64, 1#64, 0x200000#64, 0#64, 0x40000014#64, 0x300000#64, ExampleT.cv 2, 0x400000#64, 8#64, 16#64, ExampleT.cvs 16),
  (0x100000#64, 1#64, 0x200000#64, 0#64, 0x40000004#64, 0x300000#64, ExampleT.cv 3, 0x400000#64, 1#64, 0#64, ExampleT.cvs 2),
  -- not examples: two blocks an input; no pair
  (0x100000#64, 2#64, 0x200000#64, 0#64, 0x40000004#64, 0x300000#64, ExampleT.cv 1, 0x400000#64, 16#64, 0#64, ExampleT.cvs 32),
  (0x100000#64, 1#64, 0x200000#64, 0#64, 0x40000004#64, 0x300000#64, ExampleT.cv 1, 0x400000#64, 0#64, 0#64, [])]
