import Chunkcore
import Proofs
open Aeneas Aeneas.Std Result
open Bridge

/-! # A chunk's state

`ChunkState` (src/chunk_core.rs) keeps a chunk's chaining value after its
blocks so far but the last, and the last in `buf`. Given compression
kernels that meet their contracts, its fields after any bytes `B` are the
specification's chunk node of `B` (`node_eq`). -/

namespace ChunkProof
open chunkcore

/-- The code's 8 words, as the specification's. -/
def wv (a : Std.Array Std.U32 8#usize) : Vector Blake3.Word 8 :=
  ⟨(a.val.map fun x => UInt32.ofBitVec x.bv).toArray, by simp [Std.Array.val, Data.ListN.ListN_length]⟩

/-- One compression of block `j` of `B`, below the chunk's last block. -/
def step0 (mode : Blake3.Word) (B : ByteArray) (t : Blake3.Counter) (r : Vector Blake3.Word 8) (j : Nat) :
    Vector Blake3.Word 8 :=
  Blake3.first8 (Blake3.BLAKE3_COMPRESS r (Blake3.wordsLE B (64 * j) 16) t 64
    (mode ||| if j = 0 then Blake3.CHUNK_START else 0))

theorem toBA_get! (l : List Std.U8) (i : Nat) :
    (toBA l).get! i = ((l[i]?).map fun b => UInt8.ofBitVec b.bv).getD 0 := by
  simp only [toBA, ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  simp [List.getElem?_map]; rfl

/-- `wordsLE` reads only its 64 bytes. -/
theorem wordsLE_congr (X Y : ByteArray) (s t : Nat) (h : ∀ i, i < 64 → X.get! (s + i) = Y.get! (t + i)) :
    Blake3.wordsLE X s 16 = Blake3.wordsLE Y t 16 := by
  unfold Blake3.wordsLE
  congr 1; funext i
  have hi := i.isLt
  simp only
  rw [show s + 4 * i.val + 0 = s + (4 * i.val + 0) by omega, show t + 4 * i.val + 0 = t + (4 * i.val + 0) by omega,
    show s + 4 * i.val + 1 = s + (4 * i.val + 1) by omega, show t + 4 * i.val + 1 = t + (4 * i.val + 1) by omega,
    show s + 4 * i.val + 2 = s + (4 * i.val + 2) by omega, show t + 4 * i.val + 2 = t + (4 * i.val + 2) by omega,
    show s + 4 * i.val + 3 = s + (4 * i.val + 3) by omega, show t + 4 * i.val + 3 = t + (4 * i.val + 3) by omega,
    h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

/-- The specification's chunk node, its chain below the last block as a fold. -/
theorem chunkNode_eq (key : Vector Blake3.Word 8) (mode : Blake3.Word) (B : ByteArray) (t : Nat) :
    Blake3.chunkNode key mode B t =
      { h := (List.range (Blake3.blockCount B.size - 1)).foldl (fun r j =>
              Blake3.first8 (Blake3.BLAKE3_COMPRESS r (Blake3.wordsLE B (64 * j) 16) (UInt64.ofNat t) 64
                ((mode ||| if j = 0 then Blake3.CHUNK_START else 0) |||
                  if j + 1 = Blake3.blockCount B.size then Blake3.CHUNK_END else 0))) key,
        m := Blake3.wordsLE B (64 * (Blake3.blockCount B.size - 1)) 16, t := UInt64.ofNat t,
        len := UInt32.ofNat (B.size - 64 * (Blake3.blockCount B.size - 1)),
        flags := (mode ||| if Blake3.blockCount B.size - 1 = 0 then Blake3.CHUNK_START else 0) |||
          if Blake3.blockCount B.size - 1 + 1 = Blake3.blockCount B.size then Blake3.CHUNK_END else 0 } := by
  simp [Blake3.chunkNode, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, List.range'_eq_map_range]
  rfl

section
variable {P : Type} (key : Vector Blake3.Word 8) (mode : Blake3.Word)

/-- After the bytes `B` of chunk `t`: the blocks before the last chained
into `cv`, the last in `buf` (zero past `buf_len`), never empty once a byte
has come. -/
def Core (t : Nat) (B : List Std.U8) (st : ChunkState P) : Prop :=
  st.chunk_counter.val = t ∧ UInt32.ofNat st.flags.val = mode ∧
  B.length = 64 * st.blocks_compressed.val + st.buf_len.val ∧ st.buf_len.val ≤ 64 ∧ B.length ≤ 1024 ∧
  st.buf.val = B.drop (64 * st.blocks_compressed.val) ++ List.replicate (64 - st.buf_len.val) 0#u8 ∧
  wv st.cv = (List.range st.blocks_compressed.val).foldl (step0 mode (toBA B) (UInt64.ofNat t)) key

def CInv (t : Nat) (B : List Std.U8) (st : ChunkState P) : Prop :=
  Core key mode t B st ∧ (B ≠ [] → 0 < st.buf_len.val)

/-- The state's fields are the specification's chunk node of its bytes. -/
theorem node_eq (t : Nat) (B : List Std.U8) (st : ChunkState P) (h : CInv key mode t B st) :
    Blake3.chunkNode key mode (toBA B) t =
      { h := wv st.cv, m := Blake3.wordsLE (toBA st.buf.val) 0 16, t := UInt64.ofNat t,
        len := UInt32.ofNat st.buf_len.val,
        flags := (mode ||| if st.blocks_compressed.val = 0 then Blake3.CHUNK_START else 0) ||| Blake3.CHUNK_END } := by
  obtain ⟨⟨-, -, hlen, hl64, -, hbuf, hcv⟩, hne⟩ := h
  have hbc : Blake3.blockCount (toBA B).size = st.blocks_compressed.val + 1 := by
    rw [toBA_size]; unfold Blake3.blockCount
    by_cases hB : B = []
    · have : B.length = 0 := by rw [hB]; rfl
      omega
    · have := hne hB; omega
  rw [chunkNode_eq, hbc, Nat.add_sub_cancel, Blake3.Node.mk.injEq]
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · rw [hcv]
    apply List.foldl_ext
    intro r j hj
    simp only [List.mem_range] at hj
    simp only [step0, show ¬ (j + 1 = st.blocks_compressed.val + 1) by omega, ↓reduceIte]
    rw [UInt32.or_zero]
  · apply wordsLE_congr
    intro i hi
    rw [toBA_get!, toBA_get!, hbuf]
    by_cases hil : i < st.buf_len.val
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_drop, Nat.zero_add]
    · rw [List.getElem?_append_right (by simp; omega), List.getElem?_replicate]
      rw [List.getElem?_eq_none (by omega)]
      simp; split <;> rfl
  · rw [toBA_size]; congr 1; omega
  · simp

end

/-! ## The chain, as bytes arrive -/

/-- A U8's bits, widened to a word, commute with or. -/
theorem ofNat_or (a b : Std.U8) : UInt32.ofNat (a ||| b).val = UInt32.ofNat a.val ||| UInt32.ofNat b.val := by
  rw [UScalar.val_or]
  have ha : a.val < 2 ^ 32 := by scalar_tac
  have hb : b.val < 2 ^ 32 := by scalar_tac
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_or, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hb), Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- A block of `B` before its end reads the same after more bytes. -/
theorem wordsLE_append (B X : List Std.U8) (j : Nat) (hj : 64 * (j + 1) ≤ B.length) :
    Blake3.wordsLE (toBA (B ++ X)) (64 * j) 16 = Blake3.wordsLE (toBA B) (64 * j) 16 := by
  apply wordsLE_congr; intro i hi
  rw [toBA_get!, toBA_get!, List.getElem?_append_left (by omega)]

/-- Block `j` of bytes appended at a block boundary, as block `j - b` of them. -/
theorem wordsLE_tail (B X : List Std.U8) (b i : Nat) (hB : B.length = 64 * b) :
    Blake3.wordsLE (toBA (B ++ X)) (64 * (b + i)) 16 = Blake3.wordsLE (toBA X) (64 * i) 16 := by
  apply wordsLE_congr; intro k hk
  rw [toBA_get!, toBA_get!, List.getElem?_append_right (by omega)]
  congr 3; omega

theorem chain_append (mode : Blake3.Word) (t : Blake3.Counter) (B X : List Std.U8) (b : Nat)
    (hb : 64 * b ≤ B.length) (key : Vector Blake3.Word 8) :
    (List.range b).foldl (step0 mode (toBA (B ++ X)) t) key = (List.range b).foldl (step0 mode (toBA B) t) key := by
  apply List.foldl_ext
  intro r j hj
  simp only [List.mem_range] at hj
  simp only [step0, wordsLE_append B X j (by omega)]

/-! ## The code -/

/-- Bytes then zeros, with more bytes written after the first: the bytes,
the new ones, then zeros. -/
theorem setSlice_zeros (D X : List Std.U8) (n : Nat) (hX : X.length ≤ n) :
    (D ++ List.replicate n 0#u8).setSlice! D.length X = D ++ X ++ List.replicate (n - X.length) 0#u8 := by
  simp only [List.setSlice!, List.length_append, List.length_replicate, List.take_left]
  rw [show min X.length (D.length + n - D.length) = X.length by omega, List.take_of_length_le (le_refl _),
    List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    show D.length + X.length - D.length = X.length by omega, List.drop_replicate]

section
variable {P : Type} (BI : Blocks P)

theorem fill_buf_spec (st : ChunkState P) (input : Slice Std.U8) (hl : st.buf_len.val ≤ 64) :
    ChunkState.fill_buf BI st input ⦃ r =>
      r.1.val = min (64 - st.buf_len.val) input.length ∧
      r.2.buf.val = st.buf.val.setSlice! st.buf_len.val (input.val.take r.1.val) ∧
      r.2.buf_len.val = st.buf_len.val + r.1.val ∧
      r.2.cv = st.cv ∧ r.2.chunk_counter = st.chunk_counter ∧ r.2.blocks_compressed = st.blocks_compressed ∧
      r.2.flags = st.flags ∧ r.2.platform = st.platform ⦄ := by
  unfold ChunkState.fill_buf
  have hB : BLOCK_LEN.val = 64 := by simp [BLOCK_LEN]
  step as ⟨i, hi⟩
  step as ⟨want, hwant⟩
  apply WP.spec_bind (Pₘ := fun take : Std.Usize => take.val = min (64 - st.buf_len.val) input.length)
  · split
    · rename_i hlt; simp only [WP.spec_ok]
      have : want.val < input.len.val := hlt
      simp only [Slice.length] at *; scalar_tac
    · rename_i hge; simp only [WP.spec_ok]
      have : ¬ want.val < input.len.val := hge
      simp only [Slice.length] at *; scalar_tac
  · intro take htake
    step*
    · rw [s_post1, s1_post1, i2_post]; omega
    · have hst : start.val = st.buf_len.val := by rw [start_post]; simp
      have hi3 : i3.val = take.val := by
        rw [i3_post]; simp only [UScalar.cast_val_eq]; simp only [Slice.length] at htake
        apply Nat.mod_eq_of_lt; simp [UScalarTy.numBits]; omega
      refine ⟨htake, ?_, by rw [i4_post, hi3]⟩
      rw [s_post2, s2_post, s1_post, List.slice_zero_j, hst]

/-- Bytes into the buffer, where they fit: the state after them. -/
theorem core_fill (key : Vector Blake3.Word 8) (mode : Blake3.Word) (t : Nat) (B X : List Std.U8)
    (st st' : ChunkState P) (hc : Core key mode t B st)
    (hX : st.buf_len.val + X.length ≤ 64) (hB : B.length + X.length ≤ 1024)
    (hbuf : st'.buf.val = st.buf.val.setSlice! st.buf_len.val X) (hl : st'.buf_len.val = st.buf_len.val + X.length)
    (hcv : st'.cv = st.cv) (hcnt : st'.chunk_counter = st.chunk_counter)
    (hbc : st'.blocks_compressed = st.blocks_compressed) (hfl : st'.flags = st.flags) :
    Core key mode t (B ++ X) st' := by
  obtain ⟨h1, h2, hlen, hl64, h1024, hb, hch⟩ := hc
  have hD : (B.drop (64 * st.blocks_compressed.val)).length = st.buf_len.val := by simp; omega
  refine ⟨by rw [hcnt]; exact h1, by rw [hfl]; exact h2, by rw [List.length_append, hbc, hl]; omega,
    by omega, by rw [List.length_append]; omega, ?_, ?_⟩
  · rw [hbuf, hb, ← hD, setSlice_zeros _ _ _ (by omega), hD, hbc, hl, List.drop_append_of_le_length (by omega)]
    congr 2; omega
  · rw [hcv, hch, hbc, chain_append mode _ B X _ (by omega)]

/-- A full buffer compressed into the chain, the buffer emptied. -/
theorem core_compress (key : Vector Blake3.Word 8) (mode : Blake3.Word) (t : Nat) (B : List Std.U8)
    (st st' : ChunkState P) (hc : Core key mode t B st) (hl : st.buf_len.val = 64)
    (hbuf : st'.buf.val = List.replicate 64 0#u8) (hl' : st'.buf_len.val = 0)
    (hbc : st'.blocks_compressed.val = st.blocks_compressed.val + 1)
    (hcv : wv st'.cv = Blake3.first8 (Blake3.BLAKE3_COMPRESS (wv st.cv) (Blake3.wordsLE (toBA st.buf.val) 0 16)
      (UInt64.ofNat t) 64 (mode ||| if st.blocks_compressed.val = 0 then Blake3.CHUNK_START else 0)))
    (hcnt : st'.chunk_counter = st.chunk_counter) (hfl : st'.flags = st.flags) :
    Core key mode t B st' := by
  obtain ⟨h1, h2, hlen, hl64, h1024, hb, hch⟩ := hc
  refine ⟨by rw [hcnt]; exact h1, by rw [hfl]; exact h2, by omega, by omega, h1024, ?_, ?_⟩
  · rw [hbuf, hbc, hl', List.drop_eq_nil_of_le (by omega)]; rfl
  · have hw : Blake3.wordsLE (toBA st.buf.val) 0 16 = Blake3.wordsLE (toBA B) (64 * st.blocks_compressed.val) 16 := by
      apply wordsLE_congr
      intro i hi
      rw [toBA_get!, toBA_get!, hb, hl, Nat.sub_self, List.replicate_zero, List.append_nil, List.getElem?_drop,
        Nat.zero_add]
    rw [hcv, hch, hbc, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hw]
    rfl

/-- Whole blocks compressed from the input into the chain, the buffer empty. -/
theorem core_blocks (key : Vector Blake3.Word 8) (mode : Blake3.Word) (t : Nat) (B X : List Std.U8) (n : Nat)
    (st st' : ChunkState P) (hc : Core key mode t B st) (hl : st.buf_len.val = 0) (hn : 64 * n ≤ X.length)
    (hB : B.length + 64 * n ≤ 1024)
    (hbuf : st'.buf = st.buf) (hl' : st'.buf_len.val = 0)
    (hbc : st'.blocks_compressed.val = st.blocks_compressed.val + n)
    (hcv : wv st'.cv = (List.range n).foldl (fun r i =>
      Blake3.first8 (Blake3.BLAKE3_COMPRESS r (Blake3.wordsLE (toBA X) (64 * i) 16) (UInt64.ofNat t) 64
        (mode ||| if i = 0 then (if st.blocks_compressed.val = 0 then Blake3.CHUNK_START else 0) else 0))) (wv st.cv))
    (hcnt : st'.chunk_counter = st.chunk_counter) (hfl : st'.flags = st.flags) :
    Core key mode t (B ++ X.take (64 * n)) st' := by
  obtain ⟨h1, h2, hlen, hl64, h1024, hb, hch⟩ := hc
  have hBl : B.length = 64 * st.blocks_compressed.val := by omega
  have htl : (X.take (64 * n)).length = 64 * n := by simp; omega
  refine ⟨by rw [hcnt]; exact h1, by rw [hfl]; exact h2, by rw [List.length_append, htl, hbc, hl']; omega,
    by omega, by rw [List.length_append, htl]; omega, ?_, ?_⟩
  · have e1 : B.drop (64 * st.blocks_compressed.val) = [] := List.drop_eq_nil_of_le (by omega)
    have e2 : (B ++ X.take (64 * n)).drop (64 * (st.blocks_compressed.val + n)) = [] :=
      List.drop_eq_nil_of_le (by rw [List.length_append, htl]; omega)
    rw [hbuf, hb, hbc, hl', hl, e1, e2]
  · rw [hcv, hch, hbc, List.range_add, List.foldl_append, List.foldl_map,
      chain_append mode _ B (X.take (64 * n)) _ (by omega)]
    apply List.foldl_ext
    intro r i hi
    simp only [List.mem_range] at hi
    simp only [step0]
    have hw : Blake3.wordsLE (toBA (B ++ X.take (64 * n))) (64 * (st.blocks_compressed.val + i)) 16 =
        Blake3.wordsLE (toBA X) (64 * i) 16 := by
      rw [wordsLE_tail B _ _ i hBl]
      apply wordsLE_congr
      intro k hk
      rw [toBA_get!, toBA_get!, List.getElem?_take, if_pos (by omega)]
    rw [hw]
    by_cases hb0 : st.blocks_compressed.val = 0 <;> by_cases hi0 : i = 0 <;> simp [hb0, hi0]

/-- The compression kernels meet their contracts. -/
structure BlocksContracts (p : P) : Prop where
  in_place : ∀ (cv : Std.Array Std.U32 8#usize) (blk : Std.Array Std.U8 64#usize) (len : Std.U8)
    (cnt : Std.U64) (fl : Std.U8),
    BI.compress_in_place p cv blk len cnt fl ⦃ cv' => wv cv' = Blake3.first8 (Blake3.BLAKE3_COMPRESS (wv cv)
      (Blake3.wordsLE (toBA blk.val) 0 16) (UInt64.ofNat cnt.val) (UInt32.ofNat len.val) (UInt32.ofNat fl.val)) ⦄
  blocks : ∀ (cv : Std.Array Std.U32 8#usize) (blks : Slice Std.U8) (n : Std.Usize) (cnt : Std.U64) (fl fs : Std.U8),
    1 ≤ n.val → n.val ≤ 16 → 64 * n.val ≤ blks.length →
    BI.compress_blocks p cv blks n cnt fl fs ⦃ cv' => wv cv' = (List.range n.val).foldl (fun r i =>
      Blake3.first8 (Blake3.BLAKE3_COMPRESS r (Blake3.wordsLE (toBA blks.val) (64 * i) 16) (UInt64.ofNat cnt.val) 64
        (UInt32.ofNat fl.val ||| if i = 0 then UInt32.ofNat fs.val else 0))) (wv cv) ⦄

theorem start_flag_eq (st : ChunkState P) :
    ChunkState.start_flag BI st = ok (if st.blocks_compressed = 0#u8 then CHUNK_START else 0#u8) := by
  unfold ChunkState.start_flag; split <;> rfl

theorem new_spec (key : Std.Array Std.U32 8#usize) (cnt : Std.U64) (fl : Std.U8) (p : P) :
    ChunkState.new BI key cnt fl p ⦃ st =>
      CInv (wv key) (UInt32.ofNat fl.val) cnt.val [] st ∧ st.platform = p ⦄ := by
  unfold ChunkState.new
  simp only [WP.spec_ok]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩ <;> simp

/-- `absorb`: the state after the bytes so far and `input`. -/
theorem absorb_spec (key : Vector Blake3.Word 8) (mode : Blake3.Word) (t : Nat) (B : List Std.U8)
    (st : ChunkState P) (h : CInv key mode t B st) (hK : BlocksContracts BI st.platform)
    (input : Slice Std.U8) (hlen : B.length + input.length ≤ 1024) :
    ChunkState.absorb BI st input ⦃ st' => CInv key mode t (B ++ input.val) st' ∧ st'.platform = st.platform ⦄ := by
  obtain ⟨hc, hne⟩ := h
  have hB64 : BLOCK_LEN.val = 64 := by simp [BLOCK_LEN]
  have hl64 : st.buf_len.val ≤ 64 := hc.2.2.2.1
  unfold ChunkState.absorb
  apply WP.spec_bind (Pₘ := fun (x : ChunkState P × Slice Std.U8) => ∃ B1, B ++ input.val = B1 ++ x.2.val ∧
    Core key mode t B1 x.1 ∧ x.1.platform = st.platform ∧ (x.2.val ≠ [] → x.1.buf_len.val = 0) ∧
    (B1 ≠ [] → 0 < x.1.buf_len.val ∨ x.2.val ≠ []))
  · split
    · rename_i hpos
      have hpos' : 0 < st.buf_len.val := by scalar_tac
      step with fill_buf_spec BI st input hl64 as ⟨take, st2, htake, hbuf2, hl2, hcv2, hcnt2, hbc2, hfl2, hp2⟩
      step as ⟨input2, hin2, hin2l⟩
      step as ⟨b, hb⟩
      have hsplit : input.val = input.val.take take.val ++ input2.val := by
        rw [hin2]; simp [List.take_append_drop]
      have hc2 : Core key mode t (B ++ input.val.take take.val) st2 :=
        core_fill key mode t B _ st st2 hc
          (by simp only [List.length_take]; simp only [Slice.length] at htake; omega)
          (by simp only [List.length_take]; simp only [Slice.length] at hlen; omega)
          hbuf2 (by rw [hl2]; simp only [List.length_take]; simp only [Slice.length] at htake; omega)
          hcv2 hcnt2 hbc2 hfl2
      split
      · rename_i hbt
        have hr0 : input2.val = [] := by
          have : input2.length = 0 := by rw [← hb]; exact hbt
          simpa [Slice.length] using this
        simp only [Std.bind_ok, WP.spec_ok]
        refine ⟨B ++ input.val.take take.val, by rw [List.append_assoc, ← hsplit], hc2, hp2,
          fun h => absurd hr0 h, fun _ => Or.inl (by omega)⟩
      · rename_i hbf
        have hrpos : input2.val ≠ [] := by
          intro h0; apply hbf; rw [hb]; simp [Slice.length, h0]
        have hfull : st2.buf_len.val = 64 := by
          have : 0 < input2.length := by
            cases h' : input2.val with
            | nil => exact absurd h' hrpos
            | cons _ _ => simp [Slice.length, h']
          simp only [Slice.length] at this hin2l htake; omega
        rw [start_flag_eq]
        simp only [Std.bind_ok, lift]
        have hcs : (UScalar.cast UScalarTy.U8 BLOCK_LEN).val = 64 := by simp [BLOCK_LEN]
        have hk2 : BlocksContracts BI st2.platform := hp2 ▸ hK
        step with hk2.in_place st2.cv st2.buf (UScalar.cast UScalarTy.U8 BLOCK_LEN) st2.chunk_counter
          (st2.flags ||| (if st2.blocks_compressed = 0#u8 then CHUNK_START else 0#u8)) as ⟨a, ha⟩
        have hbc16 : st2.blocks_compressed.val + 1 ≤ 16 := by
          have := hc2.2.2.1; have := hc2.2.2.2.2.1; omega
        step as ⟨i2, hi2⟩
        have hmode : UInt32.ofNat st2.flags.val = mode := hc2.2.1
        have hcnt : st2.chunk_counter.val = t := hc2.1
        refine ⟨B ++ input.val.take take.val, by rw [List.append_assoc, ← hsplit], ?_, hp2,
          fun _ => rfl, fun _ => Or.inr hrpos⟩
        refine core_compress key mode t _ st2 _ hc2 hfull (by simp) rfl (by simp [hi2]) ?_ rfl rfl
        show wv a = _
        rw [ha, hcs, ofNat_or, hmode, hcnt]
        by_cases hb0 : st2.blocks_compressed = 0#u8
        · have : st2.blocks_compressed.val = 0 := by rw [hb0]; rfl
          simp [hb0, this, CHUNK_START, Blake3.CHUNK_START]
        · have : st2.blocks_compressed.val ≠ 0 := by
            intro h0; apply hb0; exact UScalar.eq_of_val_eq (by simpa using h0)
          simp [hb0, this]
    · rename_i hz
      simp only [WP.spec_ok]
      have hz' : st.buf_len.val = 0 := by scalar_tac
      exact ⟨B, rfl, hc, trivial, fun _ => hz', fun h => Or.inl (hne h)⟩
  · rintro ⟨st1, input1⟩ ⟨B1, hsplit1, hc1, hp1, hz1, hne1⟩
    simp only at hsplit1 hc1 hp1 hz1 hne1
    have hk1 : BlocksContracts BI st1.platform := hp1 ▸ hK
    have hlen1 : B1.length + input1.length ≤ 1024 := by
      have := congrArg List.length hsplit1
      simp only [List.length_append] at this; simp only [Slice.length] at hlen ⊢; omega
    apply WP.spec_bind (Pₘ := fun (x : ChunkState P × Slice Std.U8) => ∃ B2, B ++ input.val = B2 ++ x.2.val ∧
      Core key mode t B2 x.1 ∧ x.1.platform = st.platform ∧ x.2.length ≤ 64 ∧
      (x.2.val ≠ [] → x.1.buf_len.val = 0) ∧ (B2 ≠ [] → 0 < x.1.buf_len.val ∨ x.2.val ≠ []))
    · split
      · rename_i hgt
        have hgt' : 64 < input1.length := by
          have : BLOCK_LEN.val < input1.len.val := hgt
          rw [hB64] at this; simp only [Slice.length]; scalar_tac
        have hne1' : input1.val ≠ [] := by intro h0; simp [Slice.length, h0] at hgt'
        have hl1 : st1.buf_len.val = 0 := hz1 hne1'
        step as ⟨i2, hi2⟩
        step as ⟨count, hcount⟩
        rw [start_flag_eq]
        simp only [Std.bind_ok]
        have hcv : count.val = (input1.length - 1) / 64 := by
          rw [hcount, hi2, hB64]; simp only [Slice.length]; scalar_tac
        have hcnt1 : 1 ≤ count.val ∧ count.val ≤ 15 := by
          rw [hcv]; constructor <;> omega
        have hc64 : 64 * count.val ≤ input1.length := by rw [hcv]; omega
        step with hk1.blocks st1.cv input1 count st1.chunk_counter st1.flags
          (if st1.blocks_compressed = 0#u8 then CHUNK_START else 0#u8) hcnt1.1 (by omega) hc64 as ⟨a, ha⟩
        step as ⟨i3, hi3⟩
        have hbc16 : st1.blocks_compressed.val + count.val ≤ 16 := by
          have := hc1.2.2.1; have := hc1.2.2.2.2.1; simp only [Slice.length] at hc64 hlen1; omega
        have hi3v : i3.val = count.val := by
          rw [hi3]; simp only [UScalar.cast_val_eq]; apply Nat.mod_eq_of_lt; simp [UScalarTy.numBits]; omega
        step as ⟨i4, hi4⟩
        step as ⟨i5, hi5⟩
        step as ⟨input3, hin3, hin3l⟩
        try simp only [WP.spec_ok]
        have hmode : UInt32.ofNat st1.flags.val = mode := hc1.2.1
        have hcnt : st1.chunk_counter.val = t := hc1.1
        have hi5v : i5.val = 64 * count.val := by rw [hi5, hB64]; ring
        refine ⟨B1 ++ input1.val.take (64 * count.val), ?_, ?_, hp1, ?_, fun _ => hl1, fun _ => Or.inr ?_⟩
        · rw [hsplit1, List.append_assoc, hin3, hi5v, List.take_append_drop]
        · refine core_blocks key mode t B1 input1.val count.val st1 _ hc1 hl1 hc64 (by simp only [Slice.length] at hlen1 hc64; omega)
            rfl hl1 (by simp only; rw [hi4, hi3v]) ?_ rfl rfl
          show wv a = _
          rw [ha, hmode, hcnt]
          apply List.foldl_ext
          intro r i _
          by_cases hb0 : st1.blocks_compressed = 0#u8
          · have : st1.blocks_compressed.val = 0 := by rw [hb0]; rfl
            simp [hb0, CHUNK_START, Blake3.CHUNK_START]
          · have : st1.blocks_compressed.val ≠ 0 := by
              intro h0; apply hb0; exact UScalar.eq_of_val_eq (by simpa using h0)
            simp [hb0, this]
        · rw [hin3l, hi5v, hcv]; omega
        · intro h0
          have : input3.length = 0 := by simp [Slice.length, h0]
          rw [hin3l, hi5v, hcv] at this; omega
      · rename_i hle
        simp only [WP.spec_ok]
        have hle' : input1.length ≤ 64 := by
          have : ¬ BLOCK_LEN.val < input1.len.val := hle
          rw [hB64] at this; simp only [Slice.length]; scalar_tac
        exact ⟨B1, hsplit1, hc1, hp1, hle', hz1, hne1⟩
    · rintro ⟨st2, input2⟩ ⟨B2, hsplit2, hc2, hp2, hle2, hz2, hne2⟩
      simp only at hsplit2 hc2 hp2 hle2 hz2 hne2
      have hl2 : st2.buf_len.val ≤ 64 := hc2.2.2.2.1
      have hfit : st2.buf_len.val + input2.length ≤ 64 := by
        by_cases h0 : input2.val = []
        · simp [Slice.length, h0]; omega
        · rw [hz2 h0]; omega
      step with fill_buf_spec BI st2 input2 hl2 as ⟨take, st3, htake, hbuf3, hl3, hcv3, hcnt3, hbc3, hfl3, hp3⟩
      try simp only [WP.spec_ok]
      have htk : take.val = input2.length := by omega
      have hall : input2.val.take take.val = input2.val := List.take_of_length_le (by simp only [Slice.length] at htk; omega)
      have hlen2 : B2.length + input2.length ≤ 1024 := by
        have := congrArg List.length hsplit2
        simp only [List.length_append] at this; simp only [Slice.length] at hlen ⊢; omega
      refine ⟨⟨?_, ?_⟩, by rw [hp3, hp2]⟩
      · rw [hsplit2]
        have := core_fill key mode t B2 _ st2 st3 hc2 (by simp only [List.length_take]; omega)
          (by simp only [List.length_take]; simp only [Slice.length] at hlen2; omega) hbuf3
          (by rw [hl3]; simp only [List.length_take]; simp only [Slice.length] at htk; omega) hcv3 hcnt3 hbc3 hfl3
        rwa [hall] at this
      · intro hBI
        rw [hl3, htk]
        by_cases h0 : input2.val = []
        · have hB2 : B2 ≠ [] := by
            intro hb; apply hBI; rw [hsplit2, hb, h0]; rfl
          rcases hne2 hB2 with h1 | h1
          · omega
          · exact absurd h0 h1
        · have : 0 < input2.length := by
            cases h' : input2.val with
            | nil => exact absurd h' h0
            | cons _ _ => simp [Slice.length, h']
          omega

end

end ChunkProof

#print axioms ChunkProof.node_eq
#print axioms ChunkProof.new_spec
#print axioms ChunkProof.absorb_spec
