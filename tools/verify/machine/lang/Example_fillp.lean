import Sample_ptrs
import Spec_fillp

/-! # Examples for `fillp`

Where the table goes, the first address, how many real lanes, and the step. The tool runs the function on
each and compares the result with the contract (`try_fn.py`). -/

def Fillp.examples : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) := [
  (0x100000#64, 0x200000#64, 32#64, 1024#64),
  (0x100000#64, 0x200000#64, 16#64, 64#64),
  (0x100000#64, 0x200000#64, 1#64, 64#64),
  (0x300000#64, 0x500000#64, 7#64, 1024#64),
  (0x100000#64, 0x200000#64, 0#64, 64#64),
  (0x100000#64, 0xFFFFFFFFFFFFF000#64, 40#64, 1024#64)]
