import Spec_stack
import BytesLemmas
import StackBytesLemmas
import BytesAt
import PushContract
import Spec_push
open X86 Cells

/-! # The stack in this model's memory is the stack as bytes

`Spec_stack.lean` says what it means for this model's memory to hold a chaining value and the hasher's
stack, in the 16-byte vectors and 8-byte cells code moves. `../spec/StackBytes.lean` says it of bytes,
naming no machine. Here they are shown to be the same statement: memory holds the stack at `st` exactly
when the bytes at `st` are bytes that hold it. So a contract written with the layouts of bytes
(`Abi.Layout.ofBytes`) is met by the code that meets the one written with `Stack.layout` and `Cv.layout`. -/

theorem Bytes.le64_eq (n : Nat) : Bytes.le64 n =
    [(BitVec.ofNat 64 n).extractLsb' 0 8, (BitVec.ofNat 64 n).extractLsb' 8 8, (BitVec.ofNat 64 n).extractLsb' 16 8,
     (BitVec.ofNat 64 n).extractLsb' 24 8, (BitVec.ofNat 64 n).extractLsb' 32 8, (BitVec.ofNat 64 n).extractLsb' 40 8,
     (BitVec.ofNat 64 n).extractLsb' 48 8, (BitVec.ofNat 64 n).extractLsb' 56 8] := rfl

theorem Bytes.le32_eq (w : Blake3.Word) : Bytes.le32 w =
    [w.toBitVec.extractLsb' 0 8, w.toBitVec.extractLsb' 8 8, w.toBitVec.extractLsb' 16 8, w.toBitVec.extractLsb' 24 8] := rfl

/-- A 64-bit cell in memory is its eight bytes in memory. -/
theorem Quad_iff_bytes (m : Mem) (a : BitVec 64) (n : Nat) : Quad m a (BitVec.ofNat 64 n) ↔ Bytes.At m a (Bytes.le64 n) := by
  rw [Bytes.le64_eq]
  generalize BitVec.ofNat 64 n = v
  have b0 : byte v 0 = v.extractLsb' 0 8 := by simp only [byte, Nat.reduceMul]; bv_decide
  have b1 : byte v 1 = v.extractLsb' 8 8 := by simp only [byte, Nat.reduceMul]; bv_decide
  have b2 : byte v 2 = v.extractLsb' 16 8 := by simp only [byte, Nat.reduceMul]; bv_decide
  have b3 : byte v 3 = v.extractLsb' 24 8 := by simp only [byte, Nat.reduceMul]; bv_decide
  have b4 : byte v 4 = v.extractLsb' 32 8 := by simp only [byte, Nat.reduceMul]; bv_decide
  have b5 : byte v 5 = v.extractLsb' 40 8 := by simp only [byte, Nat.reduceMul]; bv_decide
  have b6 : byte v 6 = v.extractLsb' 48 8 := by simp only [byte, Nat.reduceMul]; bv_decide
  have b7 : byte v 7 = v.extractLsb' 56 8 := by simp only [byte, Nat.reduceMul]; bv_decide
  simp only [Quad, b0, b1, b2, b3, b4, b5, b6, b7, Bytes.At.cons_iff, Bytes.At.nil, and_true, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]

/-- A vector in memory is its sixteen bytes in memory. -/
theorem Vec_iff_bytes (m : Mem) (a : BitVec 64) (v : V) : Vec m a v ↔ Bytes.At m a (Bytes.ofVec v) := by
  simp only [Vec, Bytes.ofVec, Bytes.At.cons_iff, Bytes.At.nil, and_true, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    BitVec.add_assoc, BitVec.reduceAdd]

/-- The bytes of the chaining value two vectors make are the vectors' bytes. -/
theorem Cv.bytes_words8 (v0 v1 : V) : Cv.bytes (words8 v0 v1) = Bytes.ofVec v0 ++ Bytes.ofVec v1 := by
  have e : (words8 v0 v1).toList = [⟨dw v0 0⟩, ⟨dw v0 1⟩, ⟨dw v0 2⟩, ⟨dw v0 3⟩, ⟨dw v1 0⟩, ⟨dw v1 1⟩, ⟨dw v1 2⟩, ⟨dw v1 3⟩] := rfl
  rw [Cv.bytes, e]
  simp only [List.flatMap_cons, List.flatMap_nil, Bytes.le32_eq, List.append_nil, List.cons_append, List.nil_append,
    Bytes.ofVec, dw, by8, List.cons.injEq, and_true, Nat.reduceMul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

private theorem dwm0 (a b c d : BitVec 32) : dw (mk4 a b c d) 0 = a := by simp only [dw, mk4]; bv_decide
private theorem dwm1 (a b c d : BitVec 32) : dw (mk4 a b c d) 1 = b := by simp only [dw, mk4]; bv_decide
private theorem dwm2 (a b c d : BitVec 32) : dw (mk4 a b c d) 2 = c := by simp only [dw, mk4]; bv_decide
private theorem dwm3 (a b c d : BitVec 32) : dw (mk4 a b c d) 3 = d := by simp only [dw, mk4]; bv_decide

private theorem words8_mk4 (a0 a1 a2 a3 a4 a5 a6 a7 : Blake3.Word) :
    words8 (mk4 a0.toBitVec a1.toBitVec a2.toBitVec a3.toBitVec) (mk4 a4.toBitVec a5.toBitVec a6.toBitVec a7.toBitVec) =
      #v[a0, a1, a2, a3, a4, a5, a6, a7] := by
  simp only [words8, dwm0, dwm1, dwm2, dwm3]

private theorem cv_eta (cv : Blake3.CV) : #v[cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7]] = cv := by
  apply Vector.ext
  intro i hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

/-- **A chaining value in this model's memory is its 32 bytes in memory.** -/
theorem Cv.At_iff_bytes (m : Mem) (a : BitVec 64) (cv : Blake3.CV) : Cv.At m a cv ↔ Bytes.At m a (Cv.bytes cv) := by
  constructor
  · rintro ⟨v0, v1, h0, h1, e⟩
    subst e
    rw [Cv.bytes_words8, Bytes.At.append_iff]
    exact ⟨(Vec_iff_bytes m a v0).1 h0, (Vec_iff_bytes m _ v1).1 h1⟩
  · intro h
    have e := (words8_mk4 cv[0] cv[1] cv[2] cv[3] cv[4] cv[5] cv[6] cv[7]).trans (cv_eta cv)
    rw [← e, Cv.bytes_words8, Bytes.At.append_iff] at h
    exact ⟨_, _, (Vec_iff_bytes m a _).2 h.1, (Vec_iff_bytes m _ _).2 h.2, e⟩

/-- **Chaining values in this model's memory, the newest highest, are their bytes in memory, the oldest
first.** -/
theorem Cvs.At_iff_bytes (m : Mem) (a : BitVec 64) : ∀ cvs : List Blake3.CV,
    Cvs.At m (a + 32#64 * BitVec.ofNat 64 cvs.length - 32#64) cvs ↔ Bytes.At m a (cvs.reverse.flatMap Cv.bytes)
  | [] => by simp [Cvs.At, Bytes.At.nil]
  | cv :: rest => by
    have ih := Cvs.At_iff_bytes m a rest
    have e1 : a + 32#64 * BitVec.ofNat 64 (rest.length + 1) - 32#64 = a + BitVec.ofNat 64 (32 * rest.length) := by
      rw [BitVec.ofNat_add, BitVec.ofNat_mul]
      generalize BitVec.ofNat 64 rest.length = x
      bv_omega
    have e2 : a + BitVec.ofNat 64 (32 * rest.length) - 32#64 = a + 32#64 * BitVec.ofNat 64 rest.length - 32#64 := by
      rw [BitVec.ofNat_mul]
    simp only [Cvs.At, List.length_cons, List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Bytes.At.append_iff, Cv.bytes_flat_length, List.length_reverse]
    rw [e1, e2, ih, Cv.At_iff_bytes]
    exact and_comm

/-- **This model's memory holds the hasher's stack at `st` exactly when the bytes at `st` are bytes that
hold it** (`Stack.Holds`, which names no machine). -/
theorem Stack.At_iff_bytes (m : Mem) (st : BitVec 64) (cvs : List Blake3.CV) :
    Stack.At m st cvs ↔ ∃ b, Bytes.At m st b ∧ Stack.Holds b cvs := by
  have top : st + 32#64 * BitVec.ofNat 64 cvs.length = st + 32#64 + 32#64 * BitVec.ofNat 64 cvs.length - 32#64 := by
    generalize BitVec.ofNat 64 cvs.length = x
    bv_omega
  constructor
  · rintro ⟨hle, hreg, hq, hc⟩
    obtain ⟨b, hbl, hb⟩ := Bytes.of_region 1792 (by decide) hreg
    have l1 : (b.take 8).length = 8 := by rw [List.length_take, hbl]; rfl
    have l2 : ((b.drop 8).take 24).length = 24 := by rw [List.length_take, List.length_drop, hbl]; rfl
    have l3 : ((b.drop 32).take (32 * cvs.length)).length = 32 * cvs.length := by
      rw [List.length_take, List.length_drop, hbl]; omega
    have d1 : (b.drop 8).drop 24 = b.drop 32 := by rw [List.drop_drop]
    have dec : b = b.take 8 ++ ((b.drop 8).take 24 ++ ((b.drop 32).take (32 * cvs.length) ++ (b.drop 32).drop (32 * cvs.length))) := by
      rw [List.take_append_drop, ← d1, List.take_append_drop, List.take_append_drop]
    have hb' := hb
    rw [dec] at hb'
    obtain ⟨h1, hr⟩ := Bytes.At.append_iff.1 hb'
    rw [l1] at hr
    obtain ⟨-, hr⟩ := Bytes.At.append_iff.1 hr
    rw [l2] at hr
    obtain ⟨h3, -⟩ := Bytes.At.append_iff.1 hr
    rw [show st + BitVec.ofNat 64 8 + BitVec.ofNat 64 24 = st + 32#64 by bv_omega] at h3
    rw [top] at hc
    have p1 : b.take 8 = Bytes.le64 cvs.length :=
      Bytes.At.unique h1 ((Quad_iff_bytes m st _).1 hq) (by rw [l1, Bytes.le64_length])
    have p3 : (b.drop 32).take (32 * cvs.length) = cvs.reverse.flatMap Cv.bytes :=
      Bytes.At.unique h3 ((Cvs.At_iff_bytes m _ cvs).1 hc) (by rw [l3, Cv.bytes_flat_length, List.length_reverse])
    refine ⟨b, hb, hle, hbl, (b.drop 8).take 24, (b.drop 32).drop (32 * cvs.length), l2, ?_⟩
    calc b = _ := dec
      _ = _ := by rw [p1, p3]; simp only [List.append_assoc]
  · rintro ⟨b, hb, hle, hbl, unused, after, hu, e⟩
    have hb' := hb
    rw [e] at hb'
    simp only [List.append_assoc] at hb'
    obtain ⟨h1, hr⟩ := Bytes.At.append_iff.1 hb'
    rw [Bytes.le64_length] at hr
    obtain ⟨-, hr⟩ := Bytes.At.append_iff.1 hr
    rw [hu] at hr
    obtain ⟨h3, -⟩ := Bytes.At.append_iff.1 hr
    rw [show st + BitVec.ofNat 64 8 + BitVec.ofNat 64 24 = st + 32#64 by bv_omega] at h3
    refine ⟨hle, ?_, (Quad_iff_bytes m st _).2 h1, ?_⟩
    · intro d hd
      have hd' : d.toNat < b.length := by rw [hbl]; bv_omega
      have := hb d.toNat hd'
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
      rw [this]; rfl
    · rw [top]
      exact (Cvs.At_iff_bytes m _ cvs).2 h3

/-! ## The contracts are the same

`Push.contract` (`Spec_push.lean`, in this model's vectors and cells) is `Push.byteContract`
(`../spec/PushContract.lean`, which names no machine) read for this machine. -/

/-- A chaining value's bytes open as the model's chaining value in memory. -/
theorem Cv.opens : Abi.Layout.Opens Cv.byteLayout Cv.layout where
  size := rfl
  small := by decide
  holds := fun m a v => by
    apply propext
    show (∃ b : List (BitVec 8), b.length = 32 ∧ Bytes.At m a b ∧ b = Cv.bytes v) ↔ Cv.At m a v
    rw [Cv.At_iff_bytes]
    exact ⟨fun ⟨b, _, hb, e⟩ => e ▸ hb, fun h => ⟨_, Cv.bytes_length v, h, rfl⟩⟩

/-- The stack's bytes open as the model's stack in memory. -/
theorem Stack.opens : Abi.Layout.Opens Stack.byteLayout Stack.layout where
  size := rfl
  small := by decide
  holds := fun m a x => by
    apply propext
    show (∃ b : List (BitVec 8), b.length = 1792 ∧ Bytes.At m a b ∧ Stack.Holds b x) ↔ Stack.At m a x
    rw [Stack.At_iff_bytes]
    exact ⟨fun ⟨b, _, hb, h⟩ => ⟨b, hb, h⟩, fun ⟨b, hb, h⟩ => ⟨b, h.2.1, hb, h⟩⟩

theorem Cv.piece_keeps (a : BitVec 64) (v : Blake3.CV) : Abi.Piece.ofBytes (Cv.byteLayout.keeps a v) = Cv.layout.keeps a v :=
  Cv.opens.keeps a v

theorem Stack.piece_turns (a : BitVec 64) (v w : List Blake3.CV) :
    Abi.Piece.ofBytes (Stack.byteLayout.turns a v w) = Stack.layout.turns a v w := Stack.opens.turns a v w

/-- **`Push.contract` is `Push.byteContract` read for this machine**, with 64 bytes of stack. -/
theorem Push.contract_eq (st cv : BitVec 64) (new : Blake3.CV) (cvs : List Blake3.CV) :
    Abi.ofBytes (Push.byteContract st cv new cvs) 64#64 = Push.contract st cv new cvs := by
  simp only [Abi.ofBytes, Push.byteContract, Push.contract, List.map, Cv.piece_keeps, Stack.piece_turns]
