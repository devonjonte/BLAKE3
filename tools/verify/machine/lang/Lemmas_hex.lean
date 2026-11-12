import BytesLemmas
import Spec_hex
import HexSpec
open X86

/-! # `hex`: lemmas for the prover

The kernel works on vectors: its instructions are proved to write `Hex.hex8` of the two vectors read
(`HexSpec.lean`, the kernel's own view). The contract speaks of bytes (`Spec_hex.lean`). `Hex.text_vecs`
says the two agree. Written by hand for this function; checked by Lean; not to be read. -/

theorem Hex.char_eq (n : BitVec 8) : Hex.char n = Hex.hexc n := by
  simp only [Hex.char, Hex.hexc]
  bv_decide

set_option maxRecDepth 100000 in
/-- The hexadecimal of thirty-two bytes, as the four vectors the kernel writes. -/
theorem Hex.text_vecs (v0 v1 : V) :
    Hex.text (Bytes.ofVec v0 ++ Bytes.ofVec v1) =
      Bytes.ofVec (Hex.hex8 v0 0) ++ Bytes.ofVec (Hex.hex8 v0 8) ++ Bytes.ofVec (Hex.hex8 v1 0) ++ Bytes.ofVec (Hex.hex8 v1 8) := by
  simp only [Hex.text, Bytes.ofVec, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons.injEq, and_true, Hex.char_eq]
  simp only [Hex.hex8, Hex.hi, Hex.lo, Hex.hexc, by8]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide
