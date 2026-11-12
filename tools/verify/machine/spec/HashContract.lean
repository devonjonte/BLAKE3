import Blake3
import Contract

/-! # `hash`: what is claimed, of the code for any machine

Definitions only. **No theorem yet**: so far the contract is tried on examples (`../lang/HashTry.lean`),
at the level of the source's meaning. It is here because it is the statement a user reads: the function
they call computes BLAKE3. -/

namespace Blake3

/-- The specification's hash of bytes, as bytes: `Blake3.hash` (C2SP's BLAKE3, section 1.1), 32 bytes. -/
def hashBytes (msg : List (BitVec 8)) : List (BitVec 8) :=
  (hash ⟨(msg.map fun b => (⟨b⟩ : UInt8)).toArray⟩).toList.map (·.toBitVec)

/-- The specification's `IV`, as the 32 bytes a caller passes for the key of an unkeyed hash: its eight
words, each lowest byte first. -/
def ivBytes : List (BitVec 8) :=
  IV.toList.flatMap fun w => (List.range 4).map fun i => w.toBitVec.extractLsb' (8 * i) 8

end Blake3

/-- **`hash(out, input, len, key, flags, plat)`, called for an unkeyed hash.** With the `len` bytes of a
message at `input`, the specification's `IV` at `key` and no flags: the 32 bytes at `out` become the
BLAKE3 hash of the message; the message and the key are unchanged. `plat` (3, 4 or 5: SSE4.1, AVX2,
AVX-512) chooses the kernels and changes nothing else. -/
def Hash.byteContract (out inp len key plat : BitVec 64) (msg : List (BitVec 8)) : Bytes.Contract where
  args := [out, inp, len, key, 0#64, plat]
  accepts := len.toNat = msg.length ∧ (plat = 3#64 ∨ plat = 4#64 ∨ plat = 5#64)
  reads := [(Bytes.plain msg.length).keeps inp msg, (Bytes.plain 32).keeps key Blake3.ivBytes]
  updates := [(Bytes.plain 32).fills out (Blake3.hashBytes msg)]
  returns := fun _ => True
