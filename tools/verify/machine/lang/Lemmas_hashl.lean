import Lemmas_chunk
import Lemmas_lroot
import Spec_hashl
open X86 Cells

/-! # `hashl`: lemmas for the prover

Written by hand for this function; its source names them. Checked by Lean; not to be read. -/

namespace Hash

/-- Chunk number `c` of a message's bytes. -/
def chunk (bytes : List (BitVec 8)) (c : BitVec 64) : List (BitVec 8) := (bytes.drop (1024 * c.toNat)).take 1024

/-- The nodes of a message's first `c` chunks. -/
def nodes (k : Blake3.CV) (flags : BitVec 64) (bytes : List (BitVec 8)) (c : BitVec 64) : Array Blake3.Node :=
  (Array.range c.toNat).map fun i => Chunk.node k flags (BitVec.ofNat 64 i) (chunk bytes (BitVec.ofNat 64 i))

theorem ofBytes_extract (l : List (BitVec 8)) (a b : Nat) :
    (Blake3.ofBytes l).extract a b = Blake3.ofBytes ((l.drop a).take (b - a)) := by
  apply ByteArray.ext
  simp only [Blake3.ofBytes, ByteArray.data_extract]
  apply Array.ext'
  simp [List.map_drop, List.map_take]

/-- A chunk's node, as `Blake3.chunksOf` makes it. -/
theorem node_spec (k : Blake3.CV) (flags : BitVec 64) (bytes : List (BitVec 8)) (i : Nat) (hi : i < 2 ^ 64) :
    Chunk.node k flags (BitVec.ofNat 64 i) (chunk bytes (BitVec.ofNat 64 i))
      = Blake3.chunkNode k ⟨flags.setWidth 32⟩ ((Blake3.ofBytes bytes).extract (1024 * i) (1024 * (i + 1))) i := by
  have e : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  unfold Chunk.node chunk
  rw [e, ofBytes_extract, show 1024 * (i + 1) - 1024 * i = 1024 by omega]

/-- **The nodes of all the chunks are the specification's.** -/
theorem nodes_all (k : Blake3.CV) (flags : BitVec 64) (bytes : List (BitVec 8)) (c : BitVec 64)
    (hc : c.toNat = max 1 ((bytes.length + 1023) / 1024)) :
    nodes k flags bytes c = Blake3.chunksOf k ⟨flags.setWidth 32⟩ (Blake3.ofBytes bytes) := by
  unfold nodes Blake3.chunksOf
  rw [Blake3.ofBytes_size, hc]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_map, Array.getElem_range]
    have hi : i < max 1 ((bytes.length + 1023) / 1024) := by simpa using h1
    exact node_spec k flags bytes i (by have := c.isLt; omega)

theorem nodes_zero (k : Blake3.CV) (flags : BitVec 64) (bytes : List (BitVec 8)) : nodes k flags bytes 0#64 = #[] := by
  simp [nodes]

theorem nodes_succ (k : Blake3.CV) (flags : BitVec 64) (bytes : List (BitVec 8)) (c : BitVec 64) (hc : c.toNat + 1 < 2 ^ 64) :
    nodes k flags bytes (c + 1#64) = (nodes k flags bytes c).push (Chunk.node k flags c (chunk bytes c)) := by
  have e : (c + 1#64).toNat = c.toNat + 1 := by bv_omega
  unfold nodes
  rw [e, Array.range_succ]
  simp [BitVec.ofNat_toNat]

end Hash

namespace Levels
variable {k : Blake3.CV} {chunks : Array Blake3.Node}

/-- The levels are in their own 3520 bytes: a memory that agrees on them holds them too. -/
theorem At.frame {m m' : Mem} {lv : BitVec 64} {mode : Blake3.Word} (h : At k mode m lv chunks)
    (same : ∀ y : BitVec 64, y - lv < 3520#64 → m' y = m y) : At k mode m' lv chunks := by
  obtain ⟨hn, hR, hq, h1⟩ := h
  refine ⟨hn, ?_, quad_congr (fun y hy => same y (by bv_omega)) hq, fun hp => ?_⟩
  · intro d hd
    rw [same _ (by bv_omega)]; exact hR d hd
  obtain ⟨hl, hc⟩ := h1 hp
  have hpl : place (chunks.size - 1) = 0#64 ∨ place (chunks.size - 1) = 32#64 := by
    rcases Nat.mod_two_eq_zero_or_one (chunks.size - 1) with h | h
    · exact Or.inl (place_even h)
    · exact Or.inr (place_odd h)
  refine ⟨Lev.frame _ _ _ _ (by omega) (fun y hy => same y ?_) hl, Cv.At.frame hc (fun y hy => same y ?_)⟩
  · bv_omega
  · rcases hpl with h | h <;> (rw [h] at hy; bv_omega)

end Levels

namespace Hash

/-- The levels at `lv` over `chunks`, memory first (the form a source's clause takes). -/
abbrev Lv (m : Mem) (lv : BitVec 64) (k : Blake3.CV) (flags : BitVec 64) (chunks : Array Blake3.Node) : Prop :=
  Levels.At k ⟨flags.setWidth 32⟩ m lv chunks

variable {m m' : Mem} {lv input len p rem counter flags : BitVec 64} {k : Blake3.CV} {bytes : List (BitVec 8)}

theorem Lv.frame {chunks : Array Blake3.Node} (h : Lv m lv k flags chunks)
    (same : ∀ y : BitVec 64, y - lv < 3520#64 → m' y = m y) : Lv m' lv k flags chunks := Levels.At.frame h same

/-- **Before the loop:** the count written as 0: the levels over no chunk. -/
theorem Lv.start (hq : Quad m lv 0#64) (hR : Region m lv 3520#64) : Lv m lv k flags (nodes k flags bytes 0#64) := by
  rw [nodes_zero]
  exact ⟨by simp, hR, hq, fun h => absurd h (by simp)⟩

/-- The message, and where the loop is in it: `counter` whole chunks are done, `rem` bytes are left from `p`. -/
def In (m : Mem) (input len : BitVec 64) (bytes : List (BitVec 8)) (p rem counter : BitVec 64) : Prop :=
  len.toNat = bytes.length ∧ Bytes.At m input bytes ∧ rem.toNat + 1024 * counter.toNat = bytes.length ∧
  p = input + (len - rem) ∧ (counter = 0#64 ∨ 0#64 < rem)

/-- What its holder may use at once: where `p` lies in the message's piece, in the words a proof of apartness speaks. -/
theorem In.cells (h : In m input len bytes p rem counter) :
    len = BitVec.ofNat 64 bytes.length ∧ p = input + (len - rem) ∧ rem ≤ len ∧ (counter = 0#64 ∨ 0#64 < rem) ∧
    counter < 0x40000000000000#64 ∧ rem + counter <<< 10 = len := by
  obtain ⟨hn, _, hr, hp, hor⟩ := h
  have hl := len.isLt
  refine ⟨?_, hp, by bv_omega, hor, by bv_omega, ?_⟩
  · apply BitVec.eq_of_toNat_eq; rw [hn, BitVec.toNat_ofNat]; omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, hn]
    have : counter.toNat * 2 ^ 10 < 2 ^ 64 := by omega
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]; omega

theorem In.frame (h : In m input len bytes p rem counter)
    (same : ∀ x : BitVec 64, x - input < BitVec.ofNat 64 bytes.length → m' x = m x) : In m' input len bytes p rem counter := by
  obtain ⟨hn, hb, hr, hp, hor⟩ := h
  exact ⟨hn, Bytes.At.frame hb same (by have := len.isLt; omega), hr, hp, hor⟩

/-- **Before the loop.** -/
theorem In.start (hb : Bytes.At m input bytes) (hn : len.toNat = bytes.length)
    (same : ∀ x : BitVec 64, x - input < BitVec.ofNat 64 bytes.length → m' x = m x) : In m' input len bytes input len 0#64 :=
  ⟨hn, Bytes.At.frame hb same (by have := len.isLt; omega), by simp [hn], by simp, Or.inl rfl⟩

/-- **Across a turn:** one whole chunk on. -/
theorem In.step (h : In m input len bytes p rem counter) (hc : 1024#64 < rem) :
    In m input len bytes (p + 1024#64) (rem - 1024#64) (counter + 1#64) := by
  obtain ⟨hn, hb, hr, hp, hor⟩ := h
  have hl := len.isLt
  have hrem : 1024 < rem.toNat := hc
  refine ⟨hn, hb, ?_, by rw [hp]; bv_omega, Or.inr (by bv_omega)⟩
  have e1 : (rem - 1024#64).toNat = rem.toNat - 1024 := by bv_omega
  have e2 : (counter + 1#64).toNat = counter.toNat + 1 := by bv_omega
  rw [e1, e2]; omega

/-- The chunk at `p`, as a call of `chunk_node` is given it. -/
theorem In.here (h : In m input len bytes p rem counter) :
    Bytes.At m p (chunk bytes counter) ∧ (chunk bytes counter).length < 2 ^ 64 ∧
    (chunk bytes counter).length = min 1024 rem.toNat := by
  obtain ⟨hn, hb, hr, hp, hor⟩ := h
  have hl := len.isLt
  have hlen : (chunk bytes counter).length = min 1024 rem.toNat := by
    unfold chunk; rw [List.length_take, List.length_drop]; omega
  refine ⟨?_, by omega, hlen⟩
  intro i hi
  have hi' : 1024 * counter.toNat + i < bytes.length := by rw [hlen] at hi; omega
  have e : p + BitVec.ofNat 64 i = input + BitVec.ofNat 64 (1024 * counter.toNat + i) := by
    rw [hp]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e, hb _ hi']
  have hq : ((bytes.drop (1024 * counter.toNat)).take 1024)[i]? = bytes[1024 * counter.toNat + i]? := by
    rw [List.getElem?_take, List.getElem?_drop]
    simp only [ite_eq_left_iff]; intro hn'; rw [hlen] at hi; omega
  have hq2 : (chunk bytes counter)[i]? = some (chunk bytes counter)[i] := List.getElem?_eq_getElem hi
  rw [show (chunk bytes counter)[i]? = bytes[1024 * counter.toNat + i]? from hq, List.getElem?_eq_getElem hi'] at hq2
  exact hq2

end Hash

namespace Hash

variable {m m' : Mem} {lv input len p rem counter flags : BitVec 64} {k : Blake3.CV} {bytes : List (BitVec 8)}

theorem nodes_size (k : Blake3.CV) (flags : BitVec 64) (bytes : List (BitVec 8)) (c : BitVec 64) : (nodes k flags bytes c).size = c.toNat := by
  simp [nodes]

theorem counter_small (hin : In m input len bytes p rem counter) (hpos : 0 < rem.toNat) :
    counter.toNat < 2 ^ 54 := by
  obtain ⟨hn, _, hr, _, _⟩ := hin
  have := len.isLt
  omega

/-- **In a turn:** what the three calls are given. -/
theorem turn (hin : In m input len bytes p rem counter) (hlv : Lv m lv k flags (nodes k flags bytes counter))
    (hc : 1024#64 < rem) :
    ∃ _u : Unit, Bytes.At m p (chunk bytes counter) ∧ (chunk bytes counter).length < 2 ^ 64 ∧
      1024 = (chunk bytes counter).length ∧ (1024#64).toNat = (chunk bytes counter).length ∧
      (chunk bytes counter).length ≤ 1024 ∧ (nodes k flags bytes counter).size < 2 ^ 54 ∧
      BitVec.ofNat 64 (chunk bytes counter).length = 1024#64 := by
  have hrem : 1024 < rem.toNat := hc
  obtain ⟨hb, hlt, hlen⟩ := In.here hin
  have e : (chunk bytes counter).length = 1024 := by rw [hlen]; omega
  refine ⟨(), hb, hlt, e.symm, by rw [e]; rfl, by omega, ?_, by rw [e]⟩
  rw [nodes_size]; exact counter_small hin (by omega)

/-- **After the loop:** the last chunk, and what the calls are given. -/
theorem last (hin : In m input len bytes p rem counter) (hlv : Lv m lv k flags (nodes k flags bytes counter))
    (hc : ¬ 1024#64 < rem) :
    ∃ _u : Unit, Bytes.At m p (chunk bytes counter) ∧ (chunk bytes counter).length < 2 ^ 64 ∧
      rem.toNat = (chunk bytes counter).length ∧ (chunk bytes counter).length ≤ 1024 ∧
      BitVec.ofNat 64 (chunk bytes counter).length = rem := by
  have hrem : rem.toNat ≤ 1024 := by simpa [BitVec.lt_def] using hc
  obtain ⟨hb, hlt, hlen⟩ := In.here hin
  have e : (chunk bytes counter).length = rem.toNat := by rw [hlen]; omega
  exact ⟨(), hb, hlt, e.symm, by omega, by rw [e, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩

/-- After the loop, with a chunk done before the last: the levels have room for the last. -/
theorem room (hin : In m input len bytes p rem counter) (hlv : Lv m lv k flags (nodes k flags bytes counter))
    (hne : counter ≠ 0#64) :
    (nodes k flags bytes counter).size < 2 ^ 54 := by
  rw [nodes_size]
  have hor := hin.2.2.2.2
  have hpos : 0 < rem.toNat := by
    rcases hor with h | h
    · exact absurd h hne
    · exact h
  exact counter_small hin hpos

/-- **Across a turn:** the levels over one chunk more. -/
theorem Lv.step
    (h : Levels.At k ⟨flags.setWidth 32⟩ m lv ((nodes k flags bytes counter).push (Chunk.node k flags counter (chunk bytes counter)))) :
    Lv m lv k flags (nodes k flags bytes (counter + 1#64)) := by
  have hs := h.1
  rw [Array.size_push, nodes_size] at hs
  rw [nodes_succ k flags bytes counter (by omega)]
  exact h

/-- A node's compression with no flag more is its chaining value. -/
theorem cv_of {n : Blake3.Node} {cv : BitVec 64} (h : Cv.At m cv (Node.out n ⟨BitVec.setWidth 32 0#64⟩)) : Cv.At m cv n.cv := by
  have e : Node.out n ⟨BitVec.setWidth 32 0#64⟩ = n.cv := by
    unfold Node.out Blake3.Node.cv
    rw [show n.flags ||| (⟨BitVec.setWidth 32 0#64⟩ : UInt32) = n.flags from by apply UInt32.toBitVec_inj.mp; simp]
  rw [← e]; exact h

/-- **Two chunks or more:** the root the levels give is the hash's. -/
theorem many
    (h : Levels.At k ⟨flags.setWidth 32⟩ m lv ((nodes k flags bytes counter).push (Chunk.node k flags counter (chunk bytes counter))))
    (hin : In m input len bytes p rem counter) (hc : ¬ 1024#64 < rem) (hne : counter ≠ 0#64) :
    2 ≤ ((nodes k flags bytes counter).push (Chunk.node k flags counter (chunk bytes counter))).size ∧
    Levels.rootCv k ⟨flags.setWidth 32⟩ ((nodes k flags bytes counter).push (Chunk.node k flags counter (chunk bytes counter)))
      = Hash.words k flags bytes := by
  have hs := h.1
  rw [Array.size_push, nodes_size] at hs
  have hrem : rem.toNat ≤ 1024 := by simpa [BitVec.lt_def] using hc
  obtain ⟨hn, _, hr, _, hor⟩ := hin
  have hc0 : 0 < counter.toNat := by
    rcases Nat.eq_zero_or_pos counter.toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hne
    · exact h0
  have hpos : 0 < rem.toNat := by
    rcases hor with h0 | h0
    · exact absurd h0 hne
    · exact h0
  refine ⟨by rw [Array.size_push, nodes_size]; omega, ?_⟩
  rw [← nodes_succ k flags bytes counter (by omega)]
  have e : (counter + 1#64).toNat = max 1 ((bytes.length + 1023) / 1024) := by
    have e1 : (counter + 1#64).toNat = counter.toNat + 1 := by bv_omega
    rw [e1]; omega
  rw [nodes_all k flags bytes _ e]
  rfl

/-- **One chunk:** its node's output is the hash's. -/
theorem one (hin : In m input len bytes p rem counter) (hlv : Lv m lv k flags (nodes k flags bytes counter))
    (hc : ¬ 1024#64 < rem) (h0 : counter = 0#64) :
    Node.out (Chunk.node k flags counter (chunk bytes counter)) ⟨BitVec.setWidth 32 8#64⟩ = Hash.words k flags bytes := by
  subst h0
  have hrem : rem.toNat ≤ 1024 := by simpa [BitVec.lt_def] using hc
  obtain ⟨hn, _, hr, _, _⟩ := hin
  have e : (1#64 : BitVec 64).toNat = max 1 ((bytes.length + 1023) / 1024) := by
    simp at hr; simp; omega
  have hall := nodes_all k flags bytes 1#64 e
  have h1 : nodes k flags bytes 1#64 = #[Chunk.node k flags 0#64 (chunk bytes 0#64)] := by
    have := nodes_succ k flags bytes 0#64 (by decide)
    rw [nodes_zero] at this
    simpa using this
  unfold Hash.words
  rw [← hall, h1, Blake3.tree_one _ _ _ (by simp)]
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_zero, Option.getD_some]
  unfold Node.out Blake3.rootWords
  have ht : (Chunk.node k flags 0#64 (chunk bytes 0#64)).t = 0 := by
    unfold Chunk.node; rw [Blake3.chunkNode_eq]; rfl
  rw [ht]; rfl

end Hash

/-- **At the return:** what was written at `out` is the hash's first eight words. -/
theorem Hashl.exit {m : Mem} {out flags : BitVec 64} {k : Blake3.CV} {bytes : List (BitVec 8)} {X : Blake3.CV}
    (h : Cv.At m out X) (hX : X = Hash.words k flags bytes) : True ∧ Cv.At m out (Hash.words k flags bytes) :=
  ⟨trivial, hX ▸ h⟩
