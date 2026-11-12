import Meets_hex
import BytesAt
import HexContract
open X86

/-! # `hex` on x86-64 meets the contract that names no machine, quietly

`Hex.byteContract` (`../spec/HexContract.lean`) is the statement; `../arm/HexNeonBytes.lean` proves the
AArch64 kernel against the same statement, on Google DeepMind's model. -/

/-- **`Hex.contract` is `Hex.byteContract` read for this machine**, with no stack. -/
theorem Hex.contract_eq (out inp : BitVec 64) (hash : List (BitVec 8)) :
    Abi.ofBytes (Hex.byteContract out inp hash) 0#64 = Hex.contract out inp hash := by
  simp only [Abi.ofBytes, Hex.byteContract, Hex.contract, List.map, Bytes.piece_keeps 32 (by decide), Bytes.piece_fills 64 (by decide)]

/-- **The x86-64 kernel `hex` meets `Hex.byteContract` whatever the hash is, and what an observer of
time and of the cache sees does not depend on the hash.** -/
theorem hex_meets_bytes (out inp : BitVec 64) :
    Abi.MeetsQuietly Code_hex.prog 0x50000 (fun hash : List (BitVec 8) => Abi.ofBytes (Hex.byteContract out inp hash) 0#64) := by
  simp only [Hex.contract_eq]
  exact hex_meets out inp

#print axioms hex_meets_bytes
