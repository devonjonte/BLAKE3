import Sample_bytes
import Spec_pad

/-! # Examples for `pad`

Where the block goes, where the bytes are, how many, and the bytes. The tool runs the function on each and
compares the result with the contract (`try_fn.py`). -/

def ExampleP.bytes (n : Nat) : List (BitVec 8) := (List.range n).map fun i => BitVec.ofNat 8 (7 * i + 3)

def Pad.examples : List (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) := [
  (0x100000#64, 0x200000#64, 0#64, ExampleP.bytes 0),
  (0x100000#64, 0x200000#64, 1#64, ExampleP.bytes 1),
  (0x100000#64, 0x200000#64, 5#64, ExampleP.bytes 5),
  (0x100000#64, 0x200000#64, 63#64, ExampleP.bytes 63),
  (0x300000#64, 0x100000#64, 64#64, ExampleP.bytes 64),
  -- not examples: a count that is not the bytes'; more than a block
  (0x100000#64, 0x200000#64, 4#64, ExampleP.bytes 5),
  (0x100000#64, 0x200000#64, 65#64, ExampleP.bytes 65)]
