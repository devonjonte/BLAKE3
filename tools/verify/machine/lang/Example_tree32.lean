import Example_p16
import Spec_tree32

/-! # Examples for `tree32`

Where the sixteen values go, where the 32 are, the key's address, the mode's flags; then the key and the 32
values. The tool runs the function on each (the parent kernel's place taken by its stand-in) and compares the
result with the contract (`try_fn.py`). -/

def Tree32.examples : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Blake3.CV × List Blake3.CV) := [
  (0x100000#64, 0x200000#64, 0x300000#64, 0#64, ExampleT.cv 1, ExampleT.cvs 32),
  (0x100000#64, 0x200000#64, 0x300000#64, 16#64, ExampleT.cv 2, (ExampleT.cvs 32).reverse),
  -- not an example: flags of 256
  (0x100000#64, 0x200000#64, 0x300000#64, 256#64, ExampleT.cv 1, ExampleT.cvs 32)]
