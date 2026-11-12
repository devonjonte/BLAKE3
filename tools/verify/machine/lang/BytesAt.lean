import BytesLemmas
import AbiBytes
open X86 Cells

/-! # Bytes in this model's memory: lemmas

`Bytes.At` over lists put together and taken apart, and plain bytes as a piece of a contract that names
no machine (`Abi.Piece.ofBytes`) against the model's own `Bytes.layout`. Checked by Lean; not to be read. -/

theorem Bytes.At.nil (m : Mem) (a : BitVec 64) : Bytes.At m a [] := fun i h => absurd h (by simp)

theorem Bytes.At.cons_iff {m : Mem} {a : BitVec 64} {x : BitVec 8} {l : List (BitVec 8)} :
    Bytes.At m a (x :: l) ↔ m a = some x ∧ Bytes.At m (a + 1#64) l := by
  have e : ∀ i : Nat, a + 1#64 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := by
    intro i; rw [BitVec.add_assoc, Nat.add_comm, BitVec.ofNat_add]
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · have h0 : m (a + BitVec.ofNat 64 0) = some ((x :: l)[0]'(by simp)) := h 0 (by simp)
      rw [show a + BitVec.ofNat 64 0 = a from BitVec.add_zero a] at h0
      exact h0
    · rw [e]
      exact h (i + 1) (by simpa using hi)
  · rintro ⟨h0, h1⟩ i hi
    cases i with
    | zero =>
      rw [show a + BitVec.ofNat 64 0 = a from BitVec.add_zero a]
      exact h0
    | succ j =>
      rw [← e]
      exact h1 j (by simpa using hi)

theorem Bytes.At.append_iff {m : Mem} {l2 : List (BitVec 8)} : ∀ {l1 : List (BitVec 8)} {a : BitVec 64},
    Bytes.At m a (l1 ++ l2) ↔ Bytes.At m a l1 ∧ Bytes.At m (a + BitVec.ofNat 64 l1.length) l2
  | [], a => by simp [Bytes.At.nil]
  | x :: l1, a => by
    have e : a + 1#64 + BitVec.ofNat 64 l1.length = a + BitVec.ofNat 64 (l1.length + 1) := by
      rw [BitVec.add_assoc, Nat.add_comm, BitVec.ofNat_add]
    rw [List.cons_append, Bytes.At.cons_iff, Bytes.At.cons_iff, Bytes.At.append_iff (l1 := l1), List.length_cons, e, and_assoc]

theorem Bytes.At.unique {m : Mem} {a : BitVec 64} {l1 l2 : List (BitVec 8)} (h1 : Bytes.At m a l1) (h2 : Bytes.At m a l2)
    (hl : l1.length = l2.length) : l1 = l2 := by
  apply List.ext_getElem hl
  intro i hi1 hi2
  have := (h1 i hi1).symm.trans (h2 i hi2)
  exact Option.some.inj this

/-- The bytes of an owned region, read out of memory. -/
theorem Bytes.of_region {m : Mem} {a : BitVec 64} (n : Nat) (hn : n < 2 ^ 64) (h : Region m a (BitVec.ofNat 64 n)) :
    ∃ b : List (BitVec 8), b.length = n ∧ Bytes.At m a b := by
  refine ⟨(List.range n).map fun i => (m (a + BitVec.ofNat 64 i)).getD 0, by simp, ?_⟩
  intro i hi
  have hi' : i < n := by simpa using hi
  have hs := h (BitVec.ofNat 64 i) (by rw [BitVec.lt_def]; simp only [BitVec.toNat_ofNat]; omega)
  simp only [List.getElem_map, List.getElem_range]
  cases hm : m (a + BitVec.ofNat 64 i) with
  | none => rw [hm] at hs; cases hs
  | some x => rfl

/-- **A layout in bytes opens as a layout of this model**: the same size, and memory holds a value in the
model's layout exactly when the bytes at the address are bytes that hold it. One such fact a data structure
is all the pieces of a contract need (`keeps`, `turns`, `fills` below). -/
structure Abi.Layout.Opens {α : Type} (L : Bytes.Layout α) (N : Abi.Layout α) : Prop where
  size : N.size = BitVec.ofNat 64 L.size
  small : L.size < 2 ^ 64
  holds : ∀ (m : Mem) (a : BitVec 64) (v : α), (∃ b : List (BitVec 8), b.length = L.size ∧ Bytes.At m a b ∧ L.holds b v) = N.holds m a v

theorem Abi.Layout.Opens.keeps {α : Type} {L : Bytes.Layout α} {N : Abi.Layout α} (h : Abi.Layout.Opens L N) (a : BitVec 64) (v : α) :
    Abi.Piece.ofBytes (L.keeps a v) = N.keeps a v := by
  simp only [Abi.Piece.ofBytes, Bytes.Layout.keeps, Abi.Layout.keeps, h.holds, h.size]

theorem Abi.Layout.Opens.turns {α : Type} {L : Bytes.Layout α} {N : Abi.Layout α} (h : Abi.Layout.Opens L N) (a : BitVec 64) (v w : α) :
    Abi.Piece.ofBytes (L.turns a v w) = N.turns a v w := by
  simp only [Abi.Piece.ofBytes, Bytes.Layout.turns, Abi.Layout.turns, h.holds, h.size]

/-- Owned bytes are some bytes in memory. -/
theorem Bytes.region_iff (n : Nat) (hn : n < 2 ^ 64) (m : Mem) (a : BitVec 64) :
    (∃ b : List (BitVec 8), b.length = n ∧ Bytes.At m a b ∧ True) = Region m a (BitVec.ofNat 64 n) := by
  apply propext
  constructor
  · rintro ⟨b, hl, hb, -⟩ d hd
    have hd' : d.toNat < b.length := by
      rw [hl]; rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hd; exact hd
    have := hb d.toNat hd'
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    rw [this]; rfl
  · intro h
    obtain ⟨b, hl, hb⟩ := Bytes.of_region n hn h
    exact ⟨b, hl, hb, trivial⟩

theorem Abi.Layout.Opens.fills {α : Type} {L : Bytes.Layout α} {N : Abi.Layout α} (h : Abi.Layout.Opens L N) (a : BitVec 64) (w : α) :
    Abi.Piece.ofBytes (L.fills a w) = N.fills a w := by
  simp only [Abi.Piece.ofBytes, Bytes.Layout.fills, Abi.Layout.fills, h.holds, h.size, Bytes.region_iff _ h.small]

/-- Plain bytes open as the model's plain bytes. -/
theorem Bytes.opens (n : Nat) (hn : n < 2 ^ 64) : Abi.Layout.Opens (Bytes.plain n) (Bytes.layout n) where
  size := rfl
  small := hn
  holds := fun _ _ v => propext ⟨fun ⟨_, hl, hb, e⟩ => e ▸ ⟨hl, hb⟩, fun ⟨hl, hb⟩ => ⟨v, hl, hb, rfl⟩⟩

/-- Plain bytes the function does not change: the piece read for this machine is the model's own. -/
theorem Bytes.piece_keeps (n : Nat) (hn : n < 2 ^ 64) (a : BitVec 64) (v : List (BitVec 8)) :
    Abi.Piece.ofBytes ((Bytes.plain n).keeps a v) = (Bytes.layout n).keeps a v := (Bytes.opens n hn).keeps a v

/-- Plain bytes the function fills: the same. -/
theorem Bytes.piece_fills (n : Nat) (hn : n < 2 ^ 64) (a : BitVec 64) (w : List (BitVec 8)) :
    Abi.Piece.ofBytes ((Bytes.plain n).fills a w) = (Bytes.layout n).fills a w := (Bytes.opens n hn).fills a w
