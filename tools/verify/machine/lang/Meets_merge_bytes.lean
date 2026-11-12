import Proof_merge
import Proof_add
import MergeAsBytes
open X86

/-! # `merge` and `add` on x86-64 meet the contracts that name no machine

`Merge.byteContract` and `Add.byteContract` (`../spec/MergeContract.lean`) are the statements. -/

/-- **The x86-64 code of `merge` meets `Merge.byteContract`**, with 256 bytes of stack. -/
theorem merge_meets_bytes (st key flags plat target : BitVec 64) (k : Blake3.CV) (cvs : List Blake3.CV) :
    Abi.Meets Code_merge.prog 0x60000 (Abi.ofBytes (Merge.byteContract st key flags plat target k cvs) 256#64) := by
  rw [Merge.contract_eq]
  exact Proof_merge.merge_meets st key flags plat target k cvs

/-- **The x86-64 code of `add` meets `Add.byteContract`**, with 512 bytes of stack. -/
theorem add_meets_bytes (st key flags plat cv target : BitVec 64) (k new : Blake3.CV) (cvs : List Blake3.CV) :
    Abi.Meets Code_add.prog 0x80000 (Abi.ofBytes (Add.byteContract st key flags plat cv target k new cvs) 512#64) := by
  rw [Add.contract_eq]
  exact Proof_add.add_meets st key flags plat cv target k new cvs

#print axioms merge_meets_bytes
#print axioms add_meets_bytes
