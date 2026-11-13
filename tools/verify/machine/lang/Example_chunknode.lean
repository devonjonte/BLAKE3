import Sample_node
import Sample_bytes
import Spec_chunknode

/-! # Examples for `chunk_node`

Where the node goes, where the chunk's bytes are, how many, the chunk's number, the mode's flags, a
platform, the key and the bytes. The tool runs the function on each and compares the result with the
contract (`try_fn.py`). -/

def ExampleC.bytes (n : Nat) : List (BitVec 8) := (List.range n).map fun i => BitVec.ofNat 8 (i % 251)

def ExampleC.key (seed : Nat) : Blake3.CV := Vector.ofFn fun i => UInt32.ofNat (seed * 2654435761 + i.val * 40503 + 12345)

def ChunkNode.examples : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Blake3.CV × List (BitVec 8)) := [
  -- an empty chunk; one byte; a block less one; a block; a block and one
  (0x100000#64, 0x200000#64, 0#64, 0#64, 0#64, 5#64, ExampleC.key 1, ExampleC.bytes 0),
  (0x100000#64, 0x200000#64, 1#64, 0#64, 0#64, 5#64, ExampleC.key 1, ExampleC.bytes 1),
  (0x100000#64, 0x200000#64, 63#64, 0#64, 0#64, 3#64, ExampleC.key 1, ExampleC.bytes 63),
  (0x100000#64, 0x200000#64, 64#64, 2#64, 0#64, 5#64, ExampleC.key 1, ExampleC.bytes 64),
  (0x100000#64, 0x200000#64, 65#64, 0#64, 16#64, 3#64, ExampleC.key 2, ExampleC.bytes 65),
  -- two blocks; a whole chunk less one; a whole chunk, by both kernels, keyed, a later chunk
  (0x300000#64, 0x100000#64, 128#64, 1#64, 0#64, 5#64, ExampleC.key 1, ExampleC.bytes 128),
  (0x100000#64, 0x200000#64, 1023#64, 7#64, 0#64, 5#64, ExampleC.key 3, ExampleC.bytes 1023),
  (0x100000#64, 0x200000#64, 1024#64, 0#64, 0#64, 5#64, ExampleC.key 1, ExampleC.bytes 1024),
  (0x100000#64, 0x200000#64, 1024#64, 9#64, 16#64, 3#64, ExampleC.key 4, ExampleC.bytes 1024),
  -- not examples: a count that is not the bytes'; more than a chunk
  (0x100000#64, 0x200000#64, 4#64, 0#64, 0#64, 5#64, ExampleC.key 1, ExampleC.bytes 5),
  (0x100000#64, 0x200000#64, 1025#64, 0#64, 0#64, 5#64, ExampleC.key 1, ExampleC.bytes 1025)]
