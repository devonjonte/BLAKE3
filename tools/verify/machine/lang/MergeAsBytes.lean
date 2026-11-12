import StackAsBytes
import MergeContract
import Spec_merge
import Spec_add
open X86

/-! # `merge`'s and `add`'s contracts are the ones that name no machine, read for this machine

By the two lemmas of `StackAsBytes.lean` about the stack and a chaining value as pieces. -/

/-- `Merge.merged` (../spec) is `Merge.result` (`Spec_merge.lean`), word for word. -/
theorem Merge.merged_eq : Merge.merged = Merge.result := rfl

/-- **`Merge.contract` is `Merge.byteContract` read for this machine**, with 256 bytes of stack. -/
theorem Merge.contract_eq (st key flags plat target : BitVec 64) (k : Blake3.CV) (cvs : List Blake3.CV) :
    Abi.ofBytes (Merge.byteContract st key flags plat target k cvs) 256#64 = Merge.contract st key flags plat target k cvs := by
  simp only [Abi.ofBytes, Merge.byteContract, Merge.contract, List.map, Cv.piece_keeps, Stack.piece_turns, Merge.merged,
    Merge.result]

/-- **`Add.contract` is `Add.byteContract` read for this machine**, with 512 bytes of stack. -/
theorem Add.contract_eq (st key flags plat cv target : BitVec 64) (k new : Blake3.CV) (cvs : List Blake3.CV) :
    Abi.ofBytes (Add.byteContract st key flags plat cv target k new cvs) 512#64 = Add.contract st key flags plat cv target k new cvs := by
  simp only [Abi.ofBytes, Add.byteContract, Add.contract, List.map, Cv.piece_keeps, Stack.piece_turns, Merge.merged,
    Merge.result]
