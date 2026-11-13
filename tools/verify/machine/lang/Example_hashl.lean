import Sample_stack
import Sample_bytes
import Spec_hashl

/-! # Examples for `hashl`

Where the hash goes, where the message is, how long, where the key is, the mode's flags, a platform, the key
and the message. The tool runs the function on each and compares the result with the contract (`try_fn.py`).
The empty message's first is BLAKE3's test vector (the specification's IV as the key, no flags). -/

def ExampleH.bytes (n : Nat) : List (BitVec 8) := (List.range n).map fun i => BitVec.ofNat 8 (i % 251)

def ExampleH.key (seed : Nat) : Blake3.CV := Vector.ofFn fun i => UInt32.ofNat (seed * 2654435761 + i.val * 40503 + 12345)

def Hashl.examples : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Blake3.CV × List (BitVec 8)) := [
  -- the empty message and one byte, unkeyed
  (0x300000#64, 0x100000#64, 0#64, 0x200000#64, 0#64, 5#64, Blake3.IV, ExampleH.bytes 0),
  (0x300000#64, 0x100000#64, 1#64, 0x200000#64, 0#64, 3#64, Blake3.IV, ExampleH.bytes 1),
  -- a chunk; a chunk and a byte (two chunks: the levels' root); keyed
  (0x300000#64, 0x100000#64, 1024#64, 0x200000#64, 0#64, 5#64, Blake3.IV, ExampleH.bytes 1024),
  (0x300000#64, 0x100000#64, 1025#64, 0x200000#64, 0#64, 5#64, Blake3.IV, ExampleH.bytes 1025),
  (0x300000#64, 0x100000#64, 2048#64, 0x200000#64, 16#64, 3#64, ExampleH.key 2, ExampleH.bytes 2048),
  -- three chunks and a part; five chunks
  (0x300000#64, 0x100000#64, 3500#64, 0x200000#64, 0#64, 5#64, Blake3.IV, ExampleH.bytes 3500),
  (0x300000#64, 0x100000#64, 5120#64, 0x200000#64, 0#64, 3#64, Blake3.IV, ExampleH.bytes 5120),
  -- not an example: a count that is not the message's
  (0x300000#64, 0x100000#64, 7#64, 0x200000#64, 0#64, 5#64, Blake3.IV, ExampleH.bytes 8)]
