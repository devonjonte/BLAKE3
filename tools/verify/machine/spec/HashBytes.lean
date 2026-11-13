import Std.Tactic.BVDecide
import Chunk
import StackBytes
import HashContract

/-! # The hash of a message, as bytes, is the bytes of the root's first eight output words

`Blake3.hashBytes` (what `Hash.byteContract` says is left at `out`) from `Blake3.blake3_32` (`../alg/Chunk.lean`):
one fact about the specification alone, for whichever machine's code is shown to write those words. Checked
by Lean; not to be read. -/

namespace Blake3

theorem size_data (bs : ByteArray) : bs.size = bs.data.toList.length := by
  cases bs; rfl

theorem toList_loop (bs : ByteArray) : ∀ (n i : Nat) (r : List UInt8), n = bs.size - i →
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  intro n
  induction n with
  | zero =>
    intro i r h
    unfold ByteArray.toList.loop
    have : ¬ i < bs.size := by omega
    rw [if_neg this]
    rw [List.drop_eq_nil_of_le (by rw [size_data] at this; omega)]; simp
  | succ n ih =>
    intro i r h
    unfold ByteArray.toList.loop
    have hi : i < bs.size := by omega
    rw [if_pos hi]
    rw [ih (i + 1) _ (by omega)]
    have hi' : i < bs.data.toList.length := by rw [size_data] at hi; exact hi
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, List.drop_eq_getElem_cons hi']
    congr 2
    have hi2 : i < bs.data.size := by simpa using hi'
    show bs.data[i]! = bs.data.toList[i]
    rw [getElem!_pos bs.data i hi2]; simp

theorem toList_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  unfold ByteArray.toList
  rw [toList_loop bs _ 0 [] rfl]; simp

end Blake3

theorem le32_wordBytes (w : Blake3.Word) : (Blake3.wordBytes w).map (·.toBitVec) = Bytes.le32 w := by
  simp only [Blake3.wordBytes, Bytes.le32, List.map_cons, List.map_nil, List.range, List.range.loop]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp; bv_decide)

/-- **The specification's hash of a message, as bytes, is the bytes of the first eight output words of the
root of the tree over the message's chunks, under the IV and no flags.** -/
theorem hashBytes_words (msg : List (BitVec 8)) :
    Blake3.hashBytes msg = Cv.bytes (Blake3.rootWords (Blake3.tree Blake3.IV 0 (Blake3.chunksOf Blake3.IV 0 (Blake3.ofBytes msg)))) := by
  unfold Blake3.hashBytes Blake3.hash Cv.bytes
  rw [Blake3.toList_data, show (⟨(msg.map fun b => (⟨b⟩ : UInt8)).toArray⟩ : ByteArray) = Blake3.ofBytes msg from rfl, Blake3.blake3_32]
  rw [List.map_flatMap]
  congr 1
  first | done | (funext w; exact le32_wordBytes w)
