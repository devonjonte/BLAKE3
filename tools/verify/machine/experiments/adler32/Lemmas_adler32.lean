import Cells
import Spec_adler32
open X86 Cells

namespace Adler32

/-- Conditional subtraction, used only in proof lemmas about the source's branches. -/
def red (x : BitVec 64) : BitVec 64 := if x < 65521#64 then x else x - 65521#64

theorem red_nat (x : BitVec 64) (h : x.toNat < 131042) : (red x).toNat = x.toNat % 65521 := by
  unfold red
  split
  · rename_i hc
    have hc' : x.toNat < 65521 := hc
    simp only [Nat.mod_eq_of_lt hc']
  · rename_i hc
    have hc' : 65521 ≤ x.toNat := BitVec.not_lt.mp hc
    rw [BitVec.toNat_sub_of_le (BitVec.not_lt.mp hc)]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega

/-- The current sums followed by the remaining bytes give the checksum's full sums. -/
def Mid (m : Mem) (input n : BitVec 64) (bytes : List (BitVec 8)) (i a b : BitVec 64) : Prop :=
  n.toNat = bytes.length ∧ i ≤ n ∧ Bytes.At m input bytes ∧ a < 65521#64 ∧ b < 65521#64 ∧
  (bytes.drop i.toNat).foldl step (a.toNat, b.toNat) = sums bytes

namespace Mid
variable {m m' : Mem} {input n i a b : BitVec 64} {bytes : List (BitVec 8)}

theorem cells (h : Mid m input n bytes i a b) : i ≤ n ∧ a < 65521#64 ∧ b < 65521#64 :=
  ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem start (hb : Bytes.At m input bytes) (hn : n.toNat = bytes.length)
    (same : ∀ x : BitVec 64, x - input < BitVec.ofNat 64 bytes.length → m' x = m x) :
    Mid m' input n bytes 0#64 1#64 0#64 := by
  refine ⟨hn, by bv_decide, ?_, by decide, by decide, ?_⟩
  · intro j hj
    rw [same _ (by
      have e : input + BitVec.ofNat 64 j - input = BitVec.ofNat 64 j := by bv_omega
      rw [e]; simp only [BitVec.lt_def, BitVec.toNat_ofNat]
      have := n.isLt; omega)]
    exact hb j hj
  · simp [sums]

theorem next (h : Mid m input n bytes i a b) (hc : i < n) :
    ∃ v : BitVec 8, Byte m (input + i) v ∧
      (m.read (input + i) 8).getD 0#64 = v.setWidth 64 ∧ bytes.getD i.toNat 0#8 = v := by
  have hi : i.toNat < bytes.length := by rw [← h.1]; exact hc
  refine ⟨bytes[i.toNat], ?_, ?_, ?_⟩
  · have hh := h.2.2.1 _ hi
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Byte] using hh
  · have hh := h.2.2.1 _ hi
    have hb : Byte m (input + i) bytes[i.toNat] := by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Byte] using hh
    rw [read8_cell _ _ _ hb]; rfl
  · simp [List.getD, List.getElem?_eq_getElem hi]

theorem advance {v : BitVec 8} (h : Mid m input n bytes i a b) (hc : i < n)
    (hv : bytes.getD i.toNat 0#8 = v) :
    Mid m input n bytes (i + 1#64) (red (a + v.setWidth 64)) (red (b + red (a + v.setWidth 64))) := by
  obtain ⟨hn, hi, hm, ha, hb, hf⟩ := h
  have hai : a.toNat < 65521 := ha
  have hbi : b.toNat < 65521 := hb
  have vi : v.toNat < 256 := v.isLt
  have va : (v.setWidth 64).toNat = v.toNat := by simp; omega
  have add_a : (a + v.setWidth 64).toNat = a.toNat + v.toNat := by
    simp only [BitVec.toNat_add, va]; rw [Nat.mod_eq_of_lt (by omega)]
  have ar := red_nat (a + v.setWidth 64) (by rw [add_a]; omega)
  rw [add_a] at ar
  have alt : (red (a + v.setWidth 64)).toNat < 65521 := by rw [ar]; omega
  have add_b : (b + red (a + v.setWidth 64)).toNat = b.toNat + (red (a + v.setWidth 64)).toNat := by
    simp only [BitVec.toNat_add]; rw [Nat.mod_eq_of_lt (by omega)]
  have br := red_nat (b + red (a + v.setWidth 64)) (by rw [add_b]; omega)
  rw [add_b] at br
  have blt : (red (b + red (a + v.setWidth 64))).toNat < 65521 := by rw [br]; omega
  have inc : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
  have ilt : i.toNat < bytes.length := by rw [← hn]; exact hc
  have get : bytes[i.toNat] = v := by
    simpa [List.getD, List.getElem?_eq_getElem ilt] using hv
  refine ⟨hn, by bv_omega, hm, alt, blt, ?_⟩
  rw [List.drop_eq_getElem_cons ilt, get, List.foldl_cons] at hf
  simpa only [step, inc, ar, br] using hf

/-- The small/small path of the two conditional subtractions. -/
theorem small_small {v : BitVec 8} (h : Mid m input n bytes i a b) (hc : i < n)
    (hv : bytes.getD i.toNat 0#8 = v) (ha : a + v.setWidth 64 < 65521#64) (hb : b + (a + v.setWidth 64) < 65521#64) :
    Mid m input n bytes (i + 1#64) (a + v.setWidth 64) (b + (a + v.setWidth 64)) := by
  simpa only [red, ite_eq_left ha, ite_eq_left hb] using advance h hc hv


/-- The small/large path of the two conditional subtractions. -/
theorem small_large {v : BitVec 8} (h : Mid m input n bytes i a b) (hc : i < n)
    (hv : bytes.getD i.toNat 0#8 = v) (ha : a + v.setWidth 64 < 65521#64) (hb : ¬ b + (a + v.setWidth 64) < 65521#64) :
    Mid m input n bytes (i + 1#64) (a + v.setWidth 64) (b + (a + (v.setWidth 64 - 65521#64))) := by
  simpa only [red, ite_eq_left ha, ite_eq_right hb, add_sub_lit, BitVec.add_assoc] using advance h hc hv


/-- The large/small path of the two conditional subtractions. -/
theorem large_small {v : BitVec 8} (h : Mid m input n bytes i a b) (hc : i < n)
    (hv : bytes.getD i.toNat 0#8 = v) (ha : ¬ a + v.setWidth 64 < 65521#64) (hb : b + (a + v.setWidth 64 - 65521#64) < 65521#64) :
    Mid m input n bytes (i + 1#64) (a + (v.setWidth 64 - 65521#64)) (b + (a + (v.setWidth 64 - 65521#64))) := by
  have hh : Mid m input n bytes (i + 1#64) (a + v.setWidth 64 - 65521#64) (b + (a + v.setWidth 64 - 65521#64)) := by
    simpa only [red, ite_eq_right ha, ite_eq_left hb] using advance h hc hv
  simpa only [add_sub_lit, BitVec.add_assoc] using hh


/-- The large/large path of the two conditional subtractions. -/
theorem large_large {v : BitVec 8} (h : Mid m input n bytes i a b) (hc : i < n)
    (hv : bytes.getD i.toNat 0#8 = v) (ha : ¬ a + v.setWidth 64 < 65521#64) (hb : ¬ b + (a + v.setWidth 64 - 65521#64) < 65521#64) :
    Mid m input n bytes (i + 1#64) (a + (v.setWidth 64 - 65521#64)) (b + (a + (v.setWidth 64 - 65521#64 - 65521#64))) := by
  have hh : Mid m input n bytes (i + 1#64) (a + v.setWidth 64 - 65521#64) (b + (a + v.setWidth 64 - 65521#64) - 65521#64) := by
    simpa only [red, ite_eq_right ha, ite_eq_right hb] using advance h hc hv
  simpa only [add_sub_lit, BitVec.add_assoc] using hh

end Mid

/-- At exit, the two bounded words pack the specification's sums without overlap. -/
theorem exit {m : Mem} {input n i a b : BitVec 64} {bytes : List (BitVec 8)}
    (h : Mid m input n bytes i a b) (hc : ¬ i < n) :
    (b <<< 16 ||| a) = checksum bytes := by
  obtain ⟨hn, hi, hm, ha, hb, hf⟩ := h
  have ieq : i = n := by bv_omega
  have ilen : i.toNat = bytes.length := by rw [ieq, hn]
  simp only [ilen, List.drop_length, List.foldl_nil] at hf
  unfold checksum
  rw [← hf]
  have disjoint : b <<< 16 ||| a = (b <<< 16) + a := by bv_decide
  rw [disjoint]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.reducePow,
    BitVec.toNat_ofNat, Nat.mod_add_mod]

end Adler32
