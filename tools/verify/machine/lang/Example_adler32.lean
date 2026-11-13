import Sample_bytes
import Spec_adler32

/-! Examples for the public seed-one Adler contract. Small fixed vectors exercise
packing; all-255 inputs cross both modular-reduction thresholds. The final count
mismatch deliberately falls outside the contract's accepted arguments. -/

def Adler32.examples : List (BitVec 64 × BitVec 64 × List (BitVec 8)) := [
  (0x100000#64, 0#64, []),
  (0x100001#64, 1#64, [97#8]),
  (0x100000#64, 9#64, [87#8,105#8,107#8,105#8,112#8,101#8,100#8,105#8,97#8]),
  (0x100003#64, 9#64, [49#8,50#8,51#8,52#8,53#8,54#8,55#8,56#8,57#8]),
  (0x100000#64, 64#64, List.replicate 64 255#8),
  (0x100001#64, 257#64, List.replicate 257 255#8),
  (0x100000#64, 2#64, [97#8])]
