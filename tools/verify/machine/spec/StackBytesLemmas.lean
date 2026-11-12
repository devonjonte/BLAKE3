import StackBytes

/-! # The hasher's stack as bytes: lemmas

About lists of bytes only; shared by the proofs for every architecture. -/

theorem Bytes.le64_length (n : Nat) : (Bytes.le64 n).length = 8 := by simp [Bytes.le64]

theorem Bytes.le32_flat_length (l : List Blake3.Word) : (l.flatMap Bytes.le32).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons w rest ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]; simp [Bytes.le32]; omega

theorem Cv.bytes_length (cv : Blake3.CV) : (Cv.bytes cv).length = 32 := by
  rw [Cv.bytes, Bytes.le32_flat_length, Vector.length_toList]

theorem Cv.bytes_flat_length (l : List Blake3.CV) : (l.flatMap Cv.bytes).length = 32 * l.length := by
  induction l with
  | nil => rfl
  | cons cv rest ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, Cv.bytes_length]; omega

/-- **Room for one more.** A stack of fewer than 55 values has, after its values, the 32 bytes the next
one takes. -/
theorem Stack.Holds.room {b : List (BitVec 8)} {cvs : List Blake3.CV} (h : Stack.Holds b cvs) (hl : cvs.length < 55) :
    ∃ unused slot after : List (BitVec 8), unused.length = 24 ∧ slot.length = 32 ∧
      after.length = 1728 - 32 * cvs.length ∧
      b = Bytes.le64 cvs.length ++ unused ++ cvs.reverse.flatMap Cv.bytes ++ slot ++ after := by
  obtain ⟨_, hb, unused, rest, hu, e⟩ := h
  have hr : rest.length = 1792 - 32 - 32 * cvs.length := by
    have := congrArg List.length e
    simp only [List.length_append, Bytes.le64_length, hu, Cv.bytes_flat_length, List.length_reverse, hb] at this
    omega
  refine ⟨unused, rest.take 32, rest.drop 32, hu, ?_, ?_, ?_⟩
  · rw [List.length_take, hr]; omega
  · rw [List.length_drop, hr]; omega
  · rw [List.append_assoc _ (rest.take 32), List.take_append_drop]; exact e

/-- **The stack with one more value.** The count one higher, the new value's bytes after the others. -/
theorem Stack.Holds.pushed {cvs : List Blake3.CV} (new : Blake3.CV) {unused after : List (BitVec 8)}
    (hl : cvs.length < 55) (hu : unused.length = 24) (ha : after.length = 1728 - 32 * cvs.length) :
    Stack.Holds (Bytes.le64 (cvs.length + 1) ++ unused ++ cvs.reverse.flatMap Cv.bytes ++ Cv.bytes new ++ after) (new :: cvs) := by
  refine ⟨by rw [List.length_cons]; omega, ?_, unused, after, hu, ?_⟩
  · simp only [List.length_append, Bytes.le64_length, hu, Cv.bytes_flat_length, List.length_reverse, Cv.bytes_length, ha]; omega
  · simp only [List.length_cons, List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc]
