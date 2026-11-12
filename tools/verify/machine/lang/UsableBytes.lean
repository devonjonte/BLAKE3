import Usable
import MergeAsBytes
import Meets_hex_bytes
open X86

/-! # The contracts that name no machine can be used, on this one

For each `Bytes.Contract` of `../spec`, read for this machine (`Abi.ofBytes`): there is a stack and a memory
that give it all it asks. From `Usable.lean`'s theorems about the model's own contracts, which they equal. -/

theorem Push.usable_bytes : (Abi.ofBytes (Push.byteContract 0x100000#64 0x200000#64 zeroCv []) 64#64).Usable := by
  rw [Push.contract_eq]; exact Push.usable

theorem Merge.usable_bytes : (Abi.ofBytes (Merge.byteContract 0x100000#64 0x200000#64 0#64 5#64 1#64 zeroCv []) 256#64).Usable := by
  rw [Merge.contract_eq]; exact Merge.usable

theorem Add.usable_bytes :
    (Abi.ofBytes (Add.byteContract 0x100000#64 0x200000#64 0#64 5#64 0x300000#64 1#64 zeroCv zeroCv []) 512#64).Usable := by
  rw [Add.contract_eq]; exact Add.usable

theorem Hex.usable_bytes : (Abi.ofBytes (Hex.byteContract 0x100000#64 0x200000#64 (List.replicate 32 0#8)) 0#64).Usable := by
  rw [Hex.contract_eq]; exact Hex.usable

#print axioms Add.usable_bytes
