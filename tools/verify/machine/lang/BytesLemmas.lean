import Cells
import Spec_bytes
open X86 Cells

/-! # Bytes in memory and the 16-byte vectors code moves them in

A contract speaks of bytes one after another (`Bytes.At`); vector code reads and writes sixteen at a time
(`Vec`). These lemmas, written once, go from one to the other for 32 bytes read as two vectors and 64
bytes written as four. Checked by Lean; not to be read. (The case-by-case parts were written by a script.) -/

/-- Bytes are in their own place: a memory that agrees there holds them too. (A list of 2^64 bytes or more
could not lie in memory one after another: the bound is asked for.) -/
theorem Bytes.At.frame {m m' : Mem} {a : BitVec 64} {l : List (BitVec 8)} (h : Bytes.At m a l)
    (same : ∀ x : BitVec 64, x - a < BitVec.ofNat 64 l.length → m' x = m x) (hl : l.length < 2 ^ 64) : Bytes.At m' a l := by
  intro i hi
  rw [same _ (by
    have e : a + BitVec.ofNat 64 i - a = BitVec.ofNat 64 i := by bv_omega
    rw [e]; simp only [BitVec.lt_def, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hl]; exact hi)]
  exact h i hi

/-- The sixteen bytes of a vector, lowest first. -/
def Bytes.ofVec (v : V) : List (BitVec 8) := [by8 v 0, by8 v 1, by8 v 2, by8 v 3, by8 v 4, by8 v 5, by8 v 6, by8 v 7, by8 v 8, by8 v 9, by8 v 10, by8 v 11, by8 v 12, by8 v 13, by8 v 14, by8 v 15]

/-- A vector from its sixteen bytes, lowest first. -/
def Bytes.pack (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : V := b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

theorem Bytes.ofVec_pack (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : Bytes.ofVec (Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
  simp only [Bytes.ofVec, Bytes.pack, by8, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

theorem List.cons_of_length_succ {α : Type} {n : Nat} (l : List α) (h : l.length = n + 1) : ∃ a rest, l = a :: rest ∧ rest.length = n := by
  cases l with
  | nil => simp at h
  | cons a rest => exact ⟨a, rest, rfl, by simpa using h⟩

/-- Thirty-two bytes are two vectors. -/
theorem Bytes.two_vectors (l : List (BitVec 8)) (h : l.length = 32) : ∃ v0 v1 : V, l = Bytes.ofVec v0 ++ Bytes.ofVec v1 := by
  obtain ⟨b0, r0, e0, h0⟩ := List.cons_of_length_succ l h
  obtain ⟨b1, r1, e1, h1⟩ := List.cons_of_length_succ r0 h0
  obtain ⟨b2, r2, e2, h2⟩ := List.cons_of_length_succ r1 h1
  obtain ⟨b3, r3, e3, h3⟩ := List.cons_of_length_succ r2 h2
  obtain ⟨b4, r4, e4, h4⟩ := List.cons_of_length_succ r3 h3
  obtain ⟨b5, r5, e5, h5⟩ := List.cons_of_length_succ r4 h4
  obtain ⟨b6, r6, e6, h6⟩ := List.cons_of_length_succ r5 h5
  obtain ⟨b7, r7, e7, h7⟩ := List.cons_of_length_succ r6 h6
  obtain ⟨b8, r8, e8, h8⟩ := List.cons_of_length_succ r7 h7
  obtain ⟨b9, r9, e9, h9⟩ := List.cons_of_length_succ r8 h8
  obtain ⟨b10, r10, e10, h10⟩ := List.cons_of_length_succ r9 h9
  obtain ⟨b11, r11, e11, h11⟩ := List.cons_of_length_succ r10 h10
  obtain ⟨b12, r12, e12, h12⟩ := List.cons_of_length_succ r11 h11
  obtain ⟨b13, r13, e13, h13⟩ := List.cons_of_length_succ r12 h12
  obtain ⟨b14, r14, e14, h14⟩ := List.cons_of_length_succ r13 h13
  obtain ⟨b15, r15, e15, h15⟩ := List.cons_of_length_succ r14 h14
  obtain ⟨b16, r16, e16, h16⟩ := List.cons_of_length_succ r15 h15
  obtain ⟨b17, r17, e17, h17⟩ := List.cons_of_length_succ r16 h16
  obtain ⟨b18, r18, e18, h18⟩ := List.cons_of_length_succ r17 h17
  obtain ⟨b19, r19, e19, h19⟩ := List.cons_of_length_succ r18 h18
  obtain ⟨b20, r20, e20, h20⟩ := List.cons_of_length_succ r19 h19
  obtain ⟨b21, r21, e21, h21⟩ := List.cons_of_length_succ r20 h20
  obtain ⟨b22, r22, e22, h22⟩ := List.cons_of_length_succ r21 h21
  obtain ⟨b23, r23, e23, h23⟩ := List.cons_of_length_succ r22 h22
  obtain ⟨b24, r24, e24, h24⟩ := List.cons_of_length_succ r23 h23
  obtain ⟨b25, r25, e25, h25⟩ := List.cons_of_length_succ r24 h24
  obtain ⟨b26, r26, e26, h26⟩ := List.cons_of_length_succ r25 h25
  obtain ⟨b27, r27, e27, h27⟩ := List.cons_of_length_succ r26 h26
  obtain ⟨b28, r28, e28, h28⟩ := List.cons_of_length_succ r27 h27
  obtain ⟨b29, r29, e29, h29⟩ := List.cons_of_length_succ r28 h28
  obtain ⟨b30, r30, e30, h30⟩ := List.cons_of_length_succ r29 h29
  obtain ⟨b31, r31, e31, h31⟩ := List.cons_of_length_succ r30 h30
  have enil : r31 = [] := List.eq_nil_of_length_eq_zero h31
  subst enil e31 e30 e29 e28 e27 e26 e25 e24 e23 e22 e21 e20 e19 e18 e17 e16 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0
  exact ⟨Bytes.pack b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15, Bytes.pack b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31, by rw [Bytes.ofVec_pack, Bytes.ofVec_pack]; rfl⟩

/-- Thirty-two bytes in memory, as the two vectors code reads. -/
theorem Bytes.vecs32 {m : Mem} {a : BitVec 64} {l : List (BitVec 8)} (hl : l.length = 32) (h : Bytes.At m a l) :
    ∃ v0 v1 : V, Vec m a v0 ∧ Vec m (a + 16#64) v1 ∧ l = Bytes.ofVec v0 ++ Bytes.ofVec v1 := by
  obtain ⟨v0, v1, e⟩ := Bytes.two_vectors l hl
  subst e
  have len : (Bytes.ofVec v0 ++ Bytes.ofVec v1).length = 32 := rfl
  refine ⟨v0, v1, ?_, ?_, rfl⟩
  · refine ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega), h 8 (by omega), h 9 (by omega), h 10 (by omega), h 11 (by omega), h 12 (by omega), h 13 (by omega), h 14 (by omega), h 15 (by omega)⟩
  · refine ⟨(by rw [BitVec.add_assoc]; exact h 16 (by omega)), (by rw [BitVec.add_assoc]; exact h 17 (by omega)), (by rw [BitVec.add_assoc]; exact h 18 (by omega)), (by rw [BitVec.add_assoc]; exact h 19 (by omega)), (by rw [BitVec.add_assoc]; exact h 20 (by omega)), (by rw [BitVec.add_assoc]; exact h 21 (by omega)), (by rw [BitVec.add_assoc]; exact h 22 (by omega)), (by rw [BitVec.add_assoc]; exact h 23 (by omega)), (by rw [BitVec.add_assoc]; exact h 24 (by omega)), (by rw [BitVec.add_assoc]; exact h 25 (by omega)), (by rw [BitVec.add_assoc]; exact h 26 (by omega)), (by rw [BitVec.add_assoc]; exact h 27 (by omega)), (by rw [BitVec.add_assoc]; exact h 28 (by omega)), (by rw [BitVec.add_assoc]; exact h 29 (by omega)), (by rw [BitVec.add_assoc]; exact h 30 (by omega)), (by rw [BitVec.add_assoc]; exact h 31 (by omega))⟩

/-- Four vectors written one after another are sixty-four bytes in memory. -/
theorem Bytes.at_of_vecs64 {m : Mem} {a : BitVec 64} {w0 w1 w2 w3 : V}
    (h0 : Vec m a w0) (h1 : Vec m (a + 16#64) w1) (h2 : Vec m (a + 32#64) w2) (h3 : Vec m (a + 48#64) w3) :
    Bytes.At m a (Bytes.ofVec w0 ++ Bytes.ofVec w1 ++ Bytes.ofVec w2 ++ Bytes.ofVec w3) := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := h0
  obtain ⟨c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31⟩ := h1
  obtain ⟨c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47⟩ := h2
  obtain ⟨c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63⟩ := h3
  intro i hi
  match i, hi with
  | 0, _ => exact c0
  | 1, _ => exact c1
  | 2, _ => exact c2
  | 3, _ => exact c3
  | 4, _ => exact c4
  | 5, _ => exact c5
  | 6, _ => exact c6
  | 7, _ => exact c7
  | 8, _ => exact c8
  | 9, _ => exact c9
  | 10, _ => exact c10
  | 11, _ => exact c11
  | 12, _ => exact c12
  | 13, _ => exact c13
  | 14, _ => exact c14
  | 15, _ => exact c15
  | 16, _ => rw [BitVec.add_assoc] at c16; exact c16
  | 17, _ => rw [BitVec.add_assoc] at c17; exact c17
  | 18, _ => rw [BitVec.add_assoc] at c18; exact c18
  | 19, _ => rw [BitVec.add_assoc] at c19; exact c19
  | 20, _ => rw [BitVec.add_assoc] at c20; exact c20
  | 21, _ => rw [BitVec.add_assoc] at c21; exact c21
  | 22, _ => rw [BitVec.add_assoc] at c22; exact c22
  | 23, _ => rw [BitVec.add_assoc] at c23; exact c23
  | 24, _ => rw [BitVec.add_assoc] at c24; exact c24
  | 25, _ => rw [BitVec.add_assoc] at c25; exact c25
  | 26, _ => rw [BitVec.add_assoc] at c26; exact c26
  | 27, _ => rw [BitVec.add_assoc] at c27; exact c27
  | 28, _ => rw [BitVec.add_assoc] at c28; exact c28
  | 29, _ => rw [BitVec.add_assoc] at c29; exact c29
  | 30, _ => rw [BitVec.add_assoc] at c30; exact c30
  | 31, _ => rw [BitVec.add_assoc] at c31; exact c31
  | 32, _ => rw [BitVec.add_assoc] at c32; exact c32
  | 33, _ => rw [BitVec.add_assoc] at c33; exact c33
  | 34, _ => rw [BitVec.add_assoc] at c34; exact c34
  | 35, _ => rw [BitVec.add_assoc] at c35; exact c35
  | 36, _ => rw [BitVec.add_assoc] at c36; exact c36
  | 37, _ => rw [BitVec.add_assoc] at c37; exact c37
  | 38, _ => rw [BitVec.add_assoc] at c38; exact c38
  | 39, _ => rw [BitVec.add_assoc] at c39; exact c39
  | 40, _ => rw [BitVec.add_assoc] at c40; exact c40
  | 41, _ => rw [BitVec.add_assoc] at c41; exact c41
  | 42, _ => rw [BitVec.add_assoc] at c42; exact c42
  | 43, _ => rw [BitVec.add_assoc] at c43; exact c43
  | 44, _ => rw [BitVec.add_assoc] at c44; exact c44
  | 45, _ => rw [BitVec.add_assoc] at c45; exact c45
  | 46, _ => rw [BitVec.add_assoc] at c46; exact c46
  | 47, _ => rw [BitVec.add_assoc] at c47; exact c47
  | 48, _ => rw [BitVec.add_assoc] at c48; exact c48
  | 49, _ => rw [BitVec.add_assoc] at c49; exact c49
  | 50, _ => rw [BitVec.add_assoc] at c50; exact c50
  | 51, _ => rw [BitVec.add_assoc] at c51; exact c51
  | 52, _ => rw [BitVec.add_assoc] at c52; exact c52
  | 53, _ => rw [BitVec.add_assoc] at c53; exact c53
  | 54, _ => rw [BitVec.add_assoc] at c54; exact c54
  | 55, _ => rw [BitVec.add_assoc] at c55; exact c55
  | 56, _ => rw [BitVec.add_assoc] at c56; exact c56
  | 57, _ => rw [BitVec.add_assoc] at c57; exact c57
  | 58, _ => rw [BitVec.add_assoc] at c58; exact c58
  | 59, _ => rw [BitVec.add_assoc] at c59; exact c59
  | 60, _ => rw [BitVec.add_assoc] at c60; exact c60
  | 61, _ => rw [BitVec.add_assoc] at c61; exact c61
  | 62, _ => rw [BitVec.add_assoc] at c62; exact c62
  | 63, _ => rw [BitVec.add_assoc] at c63; exact c63
  | n + 64, hn => exact absurd hn (by rw [show (Bytes.ofVec w0 ++ Bytes.ofVec w1 ++ Bytes.ofVec w2 ++ Bytes.ofVec w3).length = 64 from rfl]; omega)

/-- The four vectors' places are the program's if the sixty-four bytes are. -/
theorem Bytes.owned4 {m : Mem} {a : BitVec 64} (h : Region m a 64#64) :
    Owned16 m (a + 0) ∧ Owned16 m (a + 16) ∧ Owned16 m (a + 32) ∧ Owned16 m (a + 48) :=
  ⟨owned16_region h 0#64 (by decide), owned16_region h 16#64 (by decide), owned16_region h 32#64 (by decide), owned16_region h 48#64 (by decide)⟩
