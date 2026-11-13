import Lemmas_block
import Spec_chunknode
open X86 Cells

/-! # `chunk_node`: lemmas for the prover

Written by hand for this function; its source names them. `Chunk.Mid` is what holds at the head of the
loop: the node's `h` is the chaining value after the blocks hashed so far (`Blake3.chunkFold`), and `rem`
bytes are left from `p`. Checked by Lean; not to be read. -/

namespace Chunk

/-- How many blocks are hashed when `rem` of `len` bytes are left. -/
def done (len rem : BitVec 64) : Nat := (len.toNat - rem.toNat) / 64

/-- The chaining value after `j` blocks. -/
def fold (k : Blake3.CV) (flags counter : BitVec 64) (bytes : List (BitVec 8)) (j : Nat) : Blake3.CV :=
  Blake3.chunkFold k ⟨flags.setWidth 32⟩ (Blake3.ofBytes bytes) counter.toNat j

/-- The node's `h`: the chaining value after every block but the last. -/
def h (k : Blake3.CV) (flags counter : BitVec 64) (bytes : List (BitVec 8)) : Blake3.CV := (node k flags counter bytes).h

/-- The bytes of the chunk's last block. -/
def rest (bytes : List (BitVec 8)) : List (BitVec 8) := bytes.drop (64 * (Blake3.blockCount bytes.length - 1))

/-- At the loop's head. -/
def Mid (m : Mem) (nd input len counter flags : BitVec 64) (k : Blake3.CV) (bytes : List (BitVec 8)) (p rem first : BitVec 64) : Prop :=
  len.toNat = bytes.length ∧ bytes.length ≤ 1024 ∧ flags < 256#64 ∧
  rem.toNat ≤ bytes.length ∧ 64 ∣ (bytes.length - rem.toNat) ∧ (rem = len ∨ 0#64 < rem) ∧
  p = input + (len - rem) ∧ first = (if rem = len then 1#64 else 0#64) ∧
  Cv.At m nd (fold k flags counter bytes (done len rem)) ∧ Bytes.At m input bytes ∧ Region m nd 120#64

/-- Sixteen owned bytes are a region. -/
theorem region_of_vec {m : Mem} {a : BitVec 64} {v : V} (h : Vec m a v) : Region m a 16#64 := by
  intro d hd
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := vec_owned h
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨ d = 14 ∨ d = 15 := by
    bv_decide
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A node's place is the program's when its first 32 bytes hold a value and the other 88 are the program's. -/
theorem region_node {m : Mem} {nd : BitVec 64} {k : Blake3.CV} (hk : Cv.At m nd k) (hT : Region m (nd + 32#64) 88#64) :
    Region m nd 120#64 := by
  obtain ⟨v0, v1, h0, h1, _⟩ := hk
  have r0 := region_of_vec h0
  have r1 := region_of_vec h1
  intro d hd
  by_cases c0 : d < 16#64
  · exact r0 d c0
  by_cases c1 : d < 32#64
  · have := r1 (d - 16#64) (by bv_omega)
    rwa [show nd + 16#64 + (d - 16#64) = nd + d by bv_omega] at this
  · have := hT (d - 32#64) (by bv_omega)
    rwa [show nd + 32#64 + (d - 32#64) = nd + d by bv_omega] at this

theorem src_same {m m' : Mem} {src : BitVec 64} {bytes : List (BitVec 8)} (hb : Bytes.At m src bytes)
    (sameSrc : ∀ x : BitVec 64, x - src < BitVec.ofNat 64 bytes.length → m' x = m x) (hl : bytes.length ≤ 1024) : Bytes.At m' src bytes := by
  intro i hi
  rw [sameSrc _ (by
    have e : src + BitVec.ofNat 64 i - src = BitVec.ofNat 64 i := by bv_omega
    rw [e]; simp only [BitVec.lt_def, BitVec.toNat_ofNat]; omega)]
  exact hb i hi

namespace Mid

variable {m m' : Mem} {nd input len counter flags p rem first : BitVec 64} {k : Blake3.CV} {bytes : List (BitVec 8)}

/-- What its holder may use at once. -/
theorem cells (h : Mid m nd input len counter flags k bytes p rem first) :
    Region m nd 120#64 ∧ first ≤ 1#64 ∧ rem ≤ 1024#64 ∧ flags < 256#64 := by
  obtain ⟨hn, hl, hf, hr, _, _, _, hfirst, _, _, hR⟩ := h
  refine ⟨hR, ?_, by bv_omega, hf⟩
  rw [hfirst]; split <;> decide

/-- **Before the loop:** no block hashed, the key in the node's `h`. -/
theorem start (hk : Cv.At m nd k) (hT : Region m (nd + 32#64) 88#64) (hb : Bytes.At m input bytes)
    (hn : len.toNat = bytes.length) (hl : bytes.length ≤ 1024) (hf : flags < 256#64)
    (sameN : ∀ x : BitVec 64, x - nd < 120#64 → m' x = m x)
    (sameI : ∀ x : BitVec 64, x - input < BitVec.ofNat 64 bytes.length → m' x = m x) :
    Mid m' nd input len counter flags k bytes input len 1#64 := by
  have hR := region_node hk hT
  refine ⟨hn, hl, hf, by omega, by rw [hn, Nat.sub_self]; exact Nat.dvd_zero 64, Or.inl rfl, by simp, by simp, ?_, src_same hb sameI hl, ?_⟩
  · have : done len len = 0 := by simp [done]
    rw [this]
    exact Cv.At.frame hk (fun x hx => sameN x (by bv_omega))
  · intro d hd
    rw [sameN _ (by bv_omega)]; exact hR d hd

theorem done_mul (h : Mid m nd input len counter flags k bytes p rem first) : 64 * done len rem = bytes.length - rem.toNat := by
  obtain ⟨hn, _, _, _, hdvd, _⟩ := h
  unfold done; rw [hn]; exact Nat.mul_div_cancel' hdvd

theorem p_eq (h : Mid m nd input len counter flags k bytes p rem first) : p = input + BitVec.ofNat 64 (64 * done len rem) := by
  have hs := done_mul h
  obtain ⟨hn, hl, _, hr, _, _, hp, _⟩ := h
  rw [hp, hs]; congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- A whole block to hash: the node's `h` and the block at `p`, as the six vectors a kernel reads. -/
theorem block (h : Mid m nd input len counter flags k bytes p rem first) (hc : 64#64 < rem) :
    ∃ h0 h1 b0 b1 b2 b3 : V, Vec m nd h0 ∧ Vec m (nd + 16#64) h1 ∧ Vec m p b0 ∧ Vec m (p + 16#64) b1 ∧
      Vec m (p + 32#64) b2 ∧ Vec m (p + 48#64) b3 ∧ words8 h0 h1 = fold k flags counter bytes (done len rem) ∧
      words8 b0 b1 ++ words8 b2 b3 = Blake3.wordsLE (Blake3.ofBytes bytes) (64 * done len rem) 16 := by
  have hs := done_mul h
  have hp := p_eq h
  obtain ⟨hn, hl, _, hr, _, _, _, _, ⟨h0, h1, hh0, hh1, hw⟩, hb, _⟩ := h
  have hrem : 64 < rem.toNat := hc
  generalize 64 * done len rem = s at hs hp ⊢
  have e (c : Nat) : p + BitVec.ofNat 64 c = input + BitVec.ofNat 64 (s + c) := by rw [hp, BitVec.add_assoc, ← BitVec.ofNat_add]
  refine ⟨h0, h1, Bytes.vec bytes s, Bytes.vec bytes (s + 16), Bytes.vec bytes (s + 32), Bytes.vec bytes (s + 48), hh0, hh1, ?_, ?_, ?_, ?_, hw, Bytes.block_words bytes s⟩
  · rw [hp]; exact Bytes.vec_at hb s (by omega)
  · rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, e]; exact Bytes.vec_at hb (s + 16) (by omega)
  · rw [show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from rfl, e]; exact Bytes.vec_at hb (s + 32) (by omega)
  · rw [show (48#64 : BitVec 64) = BitVec.ofNat 64 48 from rfl, e]; exact Bytes.vec_at hb (s + 48) (by omega)

/-- The flags of a block that is not the chunk's last, as the code makes them. -/
theorem flags_mid (flags first : BitVec 64) (blocks j : Nat) (hj : j + 1 ≠ blocks)
    (h1 : first = if j = 0 then 1#64 else 0#64) :
    flags.setWidth 32 ||| first.setWidth 32 = bv (Blake3.blockFlags ⟨flags.setWidth 32⟩ blocks j) := by
  simp only [Blake3.blockFlags, hj, ↓reduceIte, h1]
  by_cases h0 : j = 0
  · simp only [h0, ↓reduceIte]
    show _ = (flags.setWidth 32 ||| 1#32) ||| 0#32
    bv_decide
  · simp only [h0, ↓reduceIte]
    show _ = (flags.setWidth 32 ||| 0#32) ||| 0#32
    bv_decide

/-- **Across a turn:** one more block hashed into the node's `h`. -/
theorem step {h0 h1 b0 b1 b2 b3 : V} {F : BitVec 32}
    (h : Mid m nd input len counter flags k bytes p rem first) (hc : 64#64 < rem)
    (hw : words8 h0 h1 = fold k flags counter bytes (done len rem))
    (hb : words8 b0 b1 ++ words8 b2 b3 = Blake3.wordsLE (Blake3.ofBytes bytes) (64 * done len rem) 16)
    (hp0 : Vec m' nd (Kernels.out h0 h1 b0 b1 b2 b3 counter 64#32 F).1)
    (hp1 : Vec m' (nd + 16#64) (Kernels.out h0 h1 b0 b1 b2 b3 counter 64#32 F).2)
    (hF : F = flags.setWidth 32 ||| first.setWidth 32)
    (sameN : ∀ x : BitVec 64, x - nd < 120#64 → 32#64 ≤ x - nd → m' x = m x)
    (sameI : ∀ x : BitVec 64, x - input < BitVec.ofNat 64 bytes.length → m' x = m x) :
    Mid m' nd input len counter flags k bytes (p + 64#64) (rem - 64#64) 0#64 := by
  have hs := done_mul h
  obtain ⟨hn, hl, hf, hr, hdvd, hor, hp, hfirst, _, hbytes, hR⟩ := h
  have hrem : 64 < rem.toNat := hc
  have hr' : (rem - 64#64).toNat = rem.toNat - 64 := by bv_omega
  have hne : rem - 64#64 ≠ len := by intro e; rw [e] at hr'; omega
  have hd : done len (rem - 64#64) = done len rem + 1 := by
    unfold done; rw [hr', show len.toNat - (rem.toNat - 64) = (len.toNat - rem.toNat) + 64 by omega, Nat.add_div_right _ (by decide)]
  have hj0 : (done len rem = 0) ↔ rem = len := by
    constructor
    · intro e; rw [e] at hs; apply BitVec.eq_of_toNat_eq; omega
    · intro e; unfold done; rw [e]; simp
  have hB : done len rem + 1 ≠ Blake3.blockCount bytes.length := by
    unfold Blake3.blockCount; omega
  refine ⟨hn, hl, hf, by omega, ?_, Or.inr (by bv_omega), ?_, by simp [hne], ?_, src_same hbytes sameI hl, ?_⟩
  · rw [hr']; obtain ⟨c, hc'⟩ := hdvd; exact ⟨c + 1, by omega⟩
  · rw [hp]; bv_omega
  · rw [hd]
    refine ⟨_, _, hp0, hp1, ?_⟩
    have hfl : F = bv (Blake3.blockFlags ⟨flags.setWidth 32⟩ (Blake3.blockCount bytes.length) (done len rem)) := by
      rw [hF]; exact flags_mid flags first _ _ hB (by
        rw [hfirst]; by_cases e : rem = len
        · rw [if_pos e, if_pos (hj0.mpr e)]
        · rw [if_neg e, if_neg (mt hj0.mp e)])
    rw [Kernels.out_is h0 h1 b0 b1 b2 b3 counter.toNat.toUInt64 64 _ counter 64#32 F (by simp) rfl hfl, hw, hb]
    simp only [fold, Blake3.chunkFold, Blake3.ofBytes_size]
  · intro d hd'
    by_cases c0 : d < 16#64
    · exact region_of_vec hp0 d c0
    by_cases c1 : d < 32#64
    · have := region_of_vec hp1 (d - 16#64) (by bv_omega)
      rwa [show nd + 16#64 + (d - 16#64) = nd + d by bv_omega] at this
    · rw [sameN _ (by bv_omega) (by bv_omega)]; exact hR d hd'

end Mid

/-- Whether the chunk is one block: the flag of the first block is still to be set on the last. -/
def first (bytes : List (BitVec 8)) : BitVec 64 := if bytes.length ≤ 64 then 1#64 else 0#64

/-- The node's parts, as `Blake3.chunkNode_eq` gives them. -/
theorem node_h (k : Blake3.CV) (flags counter : BitVec 64) (bytes : List (BitVec 8)) :
    (node k flags counter bytes).h = fold k flags counter bytes (Blake3.blockCount bytes.length - 1) := by
  unfold node fold; rw [Blake3.chunkNode_eq, Blake3.ofBytes_size]

namespace Mid

variable {m m' : Mem} {nd input len counter flags p rem first : BitVec 64} {k : Blake3.CV} {bytes : List (BitVec 8)}

/-- When the loop ends, every block but the last is hashed. -/
theorem done_last (h : Mid m nd input len counter flags k bytes p rem first) (hc : ¬ 64#64 < rem) :
    done len rem = Blake3.blockCount bytes.length - 1 := by
  have hs := done_mul h
  obtain ⟨hn, hl, _, hr, hdvd, hor, _⟩ := h
  have hrem : rem.toNat ≤ 64 := by simpa [BitVec.lt_def] using hc
  have h0 : rem.toNat = 0 → bytes.length = 0 := by
    intro e
    rcases hor with e' | e'
    · rw [← hn, ← e', e]
    · exact absurd e' (by simp [BitVec.lt_def, e])
  unfold Blake3.blockCount
  omega

/-- **After the loop:** the node's `h` is done; the last block's bytes are at `p`; what the rest of the
function needs of the node's place. -/
theorem last (h : Mid m nd input len counter flags k bytes p rem first) (hc : ¬ 64#64 < rem) :
    ∃ _u : Unit, Cv.At m nd (Chunk.h k flags counter bytes) ∧ Bytes.At m p (rest bytes) ∧
      rem.toNat = (rest bytes).length ∧ (rest bytes).length ≤ 64 ∧
      Region m (nd + 32#64) 64#64 ∧ Region m nd 120#64 ∧ first = Chunk.first bytes := by
  have hs := done_mul h
  have hp := p_eq h
  have hd := done_last h hc
  obtain ⟨hn, hl, _, hr, hdvd, hor, _, hfirst, hcv, hb, hR⟩ := h
  have hrem : rem.toNat ≤ 64 := by simpa [BitVec.lt_def] using hc
  have hlen : (rest bytes).length = rem.toNat := by
    unfold rest; rw [List.length_drop, ← hd]; omega
  refine ⟨(), by unfold Chunk.h; rw [node_h, ← hd]; exact hcv, ?_, hlen.symm, by omega, ?_, hR, ?_⟩
  · intro i hi
    have hi' : 64 * done len rem + i < bytes.length := by rw [hs]; omega
    have := hb _ hi'
    rw [hp, BitVec.add_assoc, ← BitVec.ofNat_add, this]
    congr 1
    show bytes[64 * done len rem + i] = (bytes.drop (64 * (Blake3.blockCount bytes.length - 1)))[i]
    simp only [hd]
    exact List.getElem_drop.symm
  · exact region_sub hR 32#64 64#64 (by decide)
  · rw [hfirst]; unfold Chunk.first
    have e : rem = len ↔ bytes.length ≤ 64 := by
      constructor
      · intro e; rw [← hn, ← e]; exact hrem
      · intro e; apply BitVec.eq_of_toNat_eq; rw [hn]
        have h0 : rem.toNat = 0 → bytes.length = 0 := by
          intro e0
          rcases hor with e' | e'
          · rw [← hn, ← e', e0]
          · exact absurd e' (by simp [BitVec.lt_def, e0])
        obtain ⟨c, hc'⟩ := hdvd
        omega
    by_cases c : rem = len
    · rw [if_pos c, if_pos (e.mp c)]
    · rw [if_neg c, if_neg (mt e.mpr c)]

end Mid

/-- The padded last block's byte `i` is the chunk's byte there, zero past the chunk's end. -/
theorem rest_getD (bytes : List (BitVec 8)) (i : Nat) :
    (rest bytes ++ List.replicate (64 - (rest bytes).length) 0#8).getD i 0#8
      = bytes.getD (64 * (Blake3.blockCount bytes.length - 1) + i) 0#8 := by
  unfold rest
  generalize 64 * (Blake3.blockCount bytes.length - 1) = s
  by_cases h1 : i < (bytes.drop s).length
  · have h2 : s + i < bytes.length := by rw [List.length_drop] at h1; omega
    simp [List.getD, List.getElem?_append_left h1, h1, h2]
  · have h2 : ¬ s + i < bytes.length := by rw [List.length_drop] at h1; omega
    rw [List.getD, List.getD, List.getElem?_append_right (Nat.le_of_not_lt h1), List.getElem?_eq_none (Nat.le_of_not_lt h2)]
    simp [List.getElem?_replicate]
    split <;> rfl

theorem wordsLE_congr (b b' : ByteArray) (s s' : Nat) (h : ∀ i, b.get! (s + i) = b'.get! (s' + i)) :
    Blake3.wordsLE b s 16 = Blake3.wordsLE b' s' 16 := by
  ext i hi
  simp only [Blake3.wordsLE, Vector.getElem_ofFn, Nat.add_assoc, h]

/-- The flags of the chunk's last block, as the code makes them. -/
theorem flags_last (flags first : BitVec 64) (bytes : List (BitVec 8)) (hf : flags < 256#64) (h1 : first = Chunk.first bytes) :
    BitVec.setWidth 64 (Blake3.blockFlags ⟨flags.setWidth 32⟩ (Blake3.blockCount bytes.length) (Blake3.blockCount bytes.length - 1)).toBitVec
      = flags ||| first ||| 2#64 := by
  have hB1 : Blake3.blockCount bytes.length - 1 + 1 = Blake3.blockCount bytes.length := by unfold Blake3.blockCount; omega
  have h0 : Blake3.blockCount bytes.length - 1 = 0 ↔ bytes.length ≤ 64 := by unfold Blake3.blockCount; omega
  simp only [Blake3.blockFlags, hB1, ↓reduceIte, h1, Chunk.first]
  by_cases c : bytes.length ≤ 64
  · simp only [c, h0.mpr c, ↓reduceIte]
    show BitVec.setWidth 64 ((flags.setWidth 32 ||| 1#32) ||| 2#32) = _
    bv_decide
  · simp only [c, mt h0.mp c, ↓reduceIte]
    show BitVec.setWidth 64 ((flags.setWidth 32 ||| 0#32) ||| 2#32) = _
    bv_decide

end Chunk

/-- **At the return:** the node's `h` kept, the padded last block as the node's block, the three words
written: the specification's node of the chunk. -/
theorem ChunkNode.exit {m m' : Mem} {nd counter flags rem first : BitVec 64} {k : Blake3.CV} {bytes : List (BitVec 8)}
    (hcv : Cv.At m nd (Chunk.h k flags counter bytes))
    (hpad : Bytes.At m (nd + 32#64) (Chunk.rest bytes ++ List.replicate (64 - (Chunk.rest bytes).length) 0#8))
    (hrem : rem.toNat = (Chunk.rest bytes).length) (hl64 : (Chunk.rest bytes).length ≤ 64) (hfirst : first = Chunk.first bytes)
    (hf : flags < 256#64)
    (hq0 : Quad m' (nd + 96#64) counter) (hq1 : Quad m' (nd + 104#64) rem) (hq2 : Quad m' (nd + 112#64) (flags ||| first ||| 2#64))
    (same : ∀ x : BitVec 64, x - nd < 96#64 → m' x = m x) :
    True ∧ Cv.At m' nd (Chunk.node k flags counter bytes).h ∧ Node.Tail m' (nd + 32#64) (Chunk.node k flags counter bytes) := by
  have hP : (Chunk.rest bytes ++ List.replicate (64 - (Chunk.rest bytes).length) 0#8).length = 64 := by simp; omega
  generalize hPd : Chunk.rest bytes ++ List.replicate (64 - (Chunk.rest bytes).length) 0#8 = P at hpad hP
  have hpad' : Bytes.At m' (nd + 32#64) P := by
    intro i hi
    rw [same _ (by
      have e : nd + 32#64 + BitVec.ofNat 64 i - nd = 32#64 + BitVec.ofNat 64 i := by bv_omega
      rw [e]; have : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      bv_omega)]
    exact hpad i hi
  have hnode := Blake3.chunkNode_eq k ⟨flags.setWidth 32⟩ (Blake3.ofBytes bytes) counter.toNat
  rw [Blake3.ofBytes_size] at hnode
  have hB1 : 1 ≤ Blake3.blockCount bytes.length := by unfold Blake3.blockCount; omega
  have hrl : (Chunk.rest bytes).length = bytes.length - 64 * (Blake3.blockCount bytes.length - 1) := by unfold Chunk.rest; rw [List.length_drop]
  refine ⟨trivial, Cv.At.frame hcv (fun x hx => same x (by bv_omega)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Bytes.vec P 0, Bytes.vec P 16, Bytes.vec P 32, Bytes.vec P 48, ?_, ?_, ?_, ?_, ?_⟩
    · have := Bytes.vec_at hpad' 0 (by omega); rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
    · exact Bytes.vec_at hpad' 16 (by omega)
    · exact Bytes.vec_at hpad' 32 (by omega)
    · exact Bytes.vec_at hpad' 48 (by omega)
    · have := Bytes.block_words P 0
      simp only [Nat.zero_add] at this
      rw [this]
      unfold Chunk.node; rw [hnode]
      refine Chunk.wordsLE_congr _ _ 0 _ (fun i => ?_)
      rw [Blake3.ofBytes_get, Blake3.ofBytes_get, Nat.zero_add, ← hPd, Chunk.rest_getD]
  · rw [show nd + 32#64 + 64#64 = nd + 96#64 by bv_decide]
    unfold Chunk.node; rw [hnode]
    simpa using hq0
  · rw [show nd + 32#64 + 72#64 = nd + 104#64 by bv_decide]
    unfold Chunk.node; rw [hnode]
    have e : (BitVec.setWidth 64 (bytes.length - 64 * (Blake3.blockCount bytes.length - 1)).toUInt32.toBitVec) = rem := by
      apply BitVec.eq_of_toNat_eq
      rw [hrem, hrl]; simp; omega
    rw [e]; exact hq1
  · rw [show nd + 32#64 + 80#64 = nd + 112#64 by bv_decide]
    unfold Chunk.node; rw [hnode]
    rw [Chunk.flags_last flags first bytes hf hfirst]; exact hq2
  · unfold Chunk.node; rw [hnode]
    show (bytes.length - 64 * (Blake3.blockCount bytes.length - 1)).toUInt32.toBitVec ≤ 64#32
    rw [BitVec.le_def]; simp; omega
  · unfold Chunk.node; rw [hnode]
    have e := Chunk.flags_last flags first bytes hf hfirst
    have hfb : first ≤ 1#64 := by rw [hfirst]; unfold Chunk.first; split <;> decide
    show (Blake3.blockFlags ⟨flags.setWidth 32⟩ (Blake3.blockCount bytes.length) (Blake3.blockCount bytes.length - 1)).toBitVec < 256#32
    generalize (Blake3.blockFlags ⟨flags.setWidth 32⟩ (Blake3.blockCount bytes.length) (Blake3.blockCount bytes.length - 1)).toBitVec = x at e ⊢
    bv_decide
