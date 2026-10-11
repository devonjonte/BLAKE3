import ChunkProofs
import HasherCoreProofs
open Aeneas Aeneas.Std Result
open Bridge

/-! # A node's output, and the Hasher's kernels

`Output` (src/chunk_core.rs) holds a node: the inputs of its last
compression. Given compression kernels that meet their contracts, its
chaining value and its root bytes are the specification's (`cv_spec`,
`root_spec`), a chunk state's output is its chunk's node, and a parent's
the parent node of its children (`chunk_output_spec`, `parent_output_spec`).
So `Kernels` (src/hasher_core.rs) meets the Hasher's contracts, given hooks
that meet theirs (`kernels_contracts`, `kernels_node_contracts`). -/

namespace OutputProof
open hashercore ChunkProof ChildrenProof HasherCoreProof

/-! ## The bytes of words -/

theorem toLEBytes32 (x : BitVec 32) :
    x.toLEBytes = [x.setWidth 8, (x >>> 8).setWidth 8, (x >>> 16).setWidth 8, (x >>> 24).setWidth 8] := by
  rw [BitVec.toLEBytes, if_pos (by omega), BitVec.toLEBytes, if_pos (by omega), BitVec.toLEBytes, if_pos (by omega),
    BitVec.toLEBytes, if_pos (by omega), BitVec.toLEBytes, if_neg (by omega)]
  simp only [List.cons.injEq, and_true, true_and]
  refine ⟨?_, ?_, ?_⟩ <;> ext i hi <;> simp [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]
  all_goals
    simp only [show ∀ a b : Nat, a + (b + i) = a + b + i from fun _ _ => by omega]
    have h1 : 8 + i < 24 := by omega
    have h2 : 8 + i < 16 := by omega
    have h3 : 16 + i < 24 := by omega
    simp [h1, h2, h3]

/-- Byte `j` of the little-endian bytes of the words `w`. -/
def byteOf (w : Std.Array Std.U32 8#usize) (j : Nat) : Std.U8 :=
  ⟨((w.val[j / 4]!).bv >>> (8 * (j % 4))).setWidth 8⟩

theorem le_bytes_loop_spec (w : Std.Array Std.U32 8#usize) (out : Std.Array Std.U8 32#usize) (i : Std.Usize)
    (hi : i.val ≤ 8) (h : ∀ j, j < 4 * i.val → out.val[j]! = byteOf w j) :
    le_bytes_loop w out i ⦃ r => ∀ j, j < 32 → r.val[j]! = byteOf w j ⦄ := by
  unfold le_bytes_loop
  apply loop.spec_decr_nat (fun st : Std.Array Std.U8 32#usize × Std.Usize => 8 - st.2.val)
    (fun st => st.2.val ≤ 8 ∧ ∀ j, j < 4 * st.2.val → st.1.val[j]! = byteOf w j)
  · rintro ⟨o, k⟩ ⟨hk, ho⟩
    unfold le_bytes_loop.body
    by_cases hlt : k < 8#usize
    · simp only [hlt, ↓reduceIte]
      step as ⟨x, hx⟩
      step as ⟨b, hb⟩
      have hb' : b.val = [⟨x.bv.setWidth 8⟩, ⟨(x.bv >>> 8).setWidth 8⟩, ⟨(x.bv >>> 16).setWidth 8⟩,
          ⟨(x.bv >>> 24).setWidth 8⟩] := by rw [hb, toLEBytes32]; rfl
      step*
      simp only at hk ho ⊢
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro j hj
      simp only [a_post, out3_post, out2_post, out1_post, Std.Array.set_val_eq]
      have hk8 : k.val < 8 := by scalar_tac
      by_cases hjk : j < 4 * k.val
      · have := ho j hjk
        simp_lists [this]
      · have hq : j / 4 = k.val := by scalar_tac
        have hwk : w.val[j / 4]! = x := by
          rw [hq, hx, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by scalar_tac)]; rfl
        simp only [byteOf, hwk, i8_post, i6_post, i4_post, i2_post, hb']
        obtain rfl | rfl | rfl | rfl : j = 4 * k.val ∨ j = 4 * k.val + 1 ∨ j = 4 * k.val + 2 ∨ j = 4 * k.val + 3 := by
          scalar_tac
        all_goals simp_lists
        all_goals simp [show ∀ r, r < 4 → (4 * k.val + r) % 4 = r from fun r hr => by omega]
    · simp only [hlt, ↓reduceIte, WP.spec_ok]
      intro j hj
      exact ho j (by simp only; scalar_tac)
  · exact ⟨hi, h⟩

theorem flatMap4_getElem! {α β : Type} [Inhabited α] [Inhabited β] (g : α → List β) (hg : ∀ a, (g a).length = 4) :
    ∀ (l : List α) (j : Nat), j < 4 * l.length → (l.flatMap g)[j]! = (g l[j / 4]!)[j % 4]!
  | [], j, hj => by simp at hj
  | a :: l, j, hj => by
    rw [List.flatMap_cons]
    by_cases h : j < 4
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by rw [hg]; exact h)]
      simp [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, List.getElem!_eq_getElem?_getD]
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by rw [hg]; omega), hg,
        ← List.getElem!_eq_getElem?_getD, flatMap4_getElem! g hg l (j - 4) (by simp at hj; omega)]
      have h1 : j / 4 = (j - 4) / 4 + 1 := by omega
      have h2 : j % 4 = (j - 4) % 4 := by omega
      rw [h1, h2]; simp

theorem length_flatMap4 {α β : Type} (g : α → List β) (hg : ∀ a, (g a).length = 4) :
    ∀ l : List α, (l.flatMap g).length = 4 * l.length
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, List.length_append, hg, length_flatMap4 g hg l]; simp; omega

theorem le_bytes_spec (w : Std.Array Std.U32 8#usize) :
    le_bytes w ⦃ r => toBA r.val = Blake3.bytesLE (ChunkProof.wv w).toList ⦄ := by
  unfold le_bytes
  apply WP.spec_mono (le_bytes_loop_spec w _ 0#usize (by simp) (by simp))
  intro r hr
  simp only [toBA, Blake3.bytesLE, ChunkProof.wv, Vector.toList_mk]
  congr 1; congr 1
  have hrl : r.val.length = 32 := by simp
  have hwl : w.val.length = 8 := by simp
  have hfl := length_flatMap4 (fun (w : Blake3.Word) => [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8,
    (w >>> 24).toUInt8]) (fun _ => rfl) ((w.val.map fun x => UInt32.ofBitVec x.bv).toArray.toList)
  simp only [List.length_map, hwl] at hfl
  apply List.ext_getElem! (by simp only [List.length_map, hrl, hfl])
  intro j
  by_cases hj : j < 32
  · rw [List.getElem!_map_eq _ _ _ (by omega), hr j hj, List.flatMap_map,
      flatMap4_getElem! _ (fun _ => rfl) _ _ (by omega)]
    simp only [byteOf]
    have hq : j / 4 < 8 := by omega
    obtain h0 | h1 | h2 | h3 : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
    all_goals rw [‹j % 4 = _›]; apply UInt8.toBitVec_inj.mp; simp
  · rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by simp [hrl]; omega),
      List.getElem?_eq_none (by omega)]

theorem word_bytes (x : Blake3.Word) :
    (x.toUInt8.toUInt32 <<< 0 ||| (x >>> 8).toUInt8.toUInt32 <<< 8 |||
      (x >>> 16).toUInt8.toUInt32 <<< 16 ||| (x >>> 24).toUInt8.toUInt32 <<< 24) = x := by
  apply UInt32.toBitVec_inj.mp
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32, UInt32.toBitVec_toUInt8,
    UInt32.toBitVec_shiftRight]
  have h0 : UInt32.toBitVec 0 % 32 = 0#32 := rfl
  have h8 : UInt32.toBitVec 8 % 32 = 8#32 := rfl
  have h16 : UInt32.toBitVec 16 % 32 = 16#32 := rfl
  have h24 : UInt32.toBitVec 24 % 32 = 24#32 := rfl
  simp only [h0, h8, h16, h24, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
  ext n hn
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.toNat_ofNat]
  obtain h | h | h | h : n < 8 ∨ (8 ≤ n ∧ n < 16) ∨ (16 ≤ n ∧ n < 24) ∨ (24 ≤ n ∧ n < 32) := by omega
  all_goals simp (disch := omega) [h, show ¬n < 0 by omega]
  · simp [show n < 16 by omega, show n < 24 by omega]
  · simp [show ¬n < 8 by omega, show n - 8 < 8 by omega, show n < 24 by omega]
  · simp [show ¬n < 8 by omega, show ¬n - 8 < 8 by omega, show ¬n < 16 by omega, show n - 16 < 8 by omega]
  · simp [show ¬n < 8 by omega, show ¬n - 8 < 8 by omega, show ¬n < 16 by omega, show ¬n - 16 < 8 by omega,
      show ¬n < 24 by omega, show n - 24 < 8 by omega]

theorem wordsLE_bytesLE (v : Vector Blake3.Word 8) : Blake3.wordsLE (Blake3.bytesLE v.toList) 0 8 = v := by
  apply Vector.ext
  intro i hi
  simp only [Blake3.wordsLE, Vector.getElem_ofFn]
  have hb : ∀ k, k < 4 → (Blake3.bytesLE v.toList).get! (0 + 4 * i + k) = ([v[i].toUInt8, (v[i] >>> 8).toUInt8,
      (v[i] >>> 16).toUInt8, (v[i] >>> 24).toUInt8])[k]! := by
    intro k hk
    simp only [Blake3.bytesLE, ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray]
    rw [← List.getElem!_eq_getElem?_getD, flatMap4_getElem! _ (fun _ => rfl) _ _ (by simp; omega)]
    simp [show (4 * i + k) / 4 = i by omega, show (4 * i + k) % 4 = k by omega, Vector.getElem?_eq_getElem hi]
  rw [hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega)]
  have e0 : Nat.toUInt32 (8 * 0) = 0 := rfl
  have e1 : Nat.toUInt32 (8 * 1) = 8 := rfl
  have e2 : Nat.toUInt32 (8 * 2) = 16 := rfl
  have e3 : Nat.toUInt32 (8 * 3) = 24 := rfl
  rw [e0, e1, e2, e3]
  exact word_bytes v[i]

theorem take_flatMap4 {α β : Type} (g : α → List β) (hg : ∀ a, (g a).length = 4) :
    ∀ (l : List α) (k : Nat), (l.flatMap g).take (4 * k) = (l.take k).flatMap g
  | [], k => by simp
  | a :: l, 0 => by simp
  | a :: l, k + 1 => by
    rw [List.flatMap_cons, List.take_succ_cons, List.flatMap_cons, show 4 * (k + 1) = (g a).length + 4 * k by
      rw [hg]; omega, List.take_length_add_append, take_flatMap4 g hg l k]

/-- The first 32 bytes of 16 words are the bytes of the first 8. -/
theorem bytesLE_first8 (V : Vector Blake3.Word 16) :
    Blake3.bytesLE (Blake3.first8 V).toList = (Blake3.bytesLE V.toList).extract 0 32 := by
  have h8 : (Blake3.first8 V).toList = V.toList.take 8 := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [Blake3.first8, Blake3.lo]
  apply ByteArray.ext
  simp only [Blake3.bytesLE, ByteArray.data_extract, h8]
  rw [List.extract_toArray, ← take_flatMap4 _ (fun _ => rfl) _ 8]
  simp

/-! ## A node's output -/

/-- The code's chaining value, as the specification's words. -/
def cvOf (v : Std.Array Std.U8 32#usize) : Vector Blake3.Word 8 := Blake3.wordsLE (toBA v.val) 0 8

/-- The code's node, as the specification's. -/
def absN {P : Type} (o : Output P) : Blake3.Node :=
  { h := wv o.input_chaining_value, m := Blake3.wordsLE (toBA o.block.val) 0 16, t := UInt64.ofNat o.counter.val,
    len := UInt32.ofNat o.block_len.val, flags := UInt32.ofNat o.flags.val }

/-- The words of two 32-byte halves are the words of each. -/
theorem wordsLE_append (l r : List Std.U8) (hl : l.length = 32) :
    Blake3.wordsLE (toBA (l ++ r)) 0 16 = Blake3.wordsLE (toBA l) 0 8 ++ Blake3.wordsLE (toBA r) 0 8 := by
  apply Vector.ext
  intro i hi
  simp only [Blake3.wordsLE, Vector.getElem_ofFn, toBA_get!]
  rw [Vector.getElem_append]
  by_cases h8 : i < 8
  · simp only [h8, ↓reduceDIte, Vector.getElem_ofFn]
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
      List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  · simp only [h8, ↓reduceDIte, Vector.getElem_ofFn]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hl]
    have e : ∀ k, 0 + 4 * i + k - 32 = 0 + 4 * (i - 8) + k := fun k => by omega
    simp only [e]

theorem cvOf_le_bytes (r : Std.Array Std.U8 32#usize) (w : Std.Array Std.U32 8#usize)
    (h : toBA r.val = Blake3.bytesLE (wv w).toList) : cvOf r = wv w := by
  rw [cvOf, h, wordsLE_bytesLE]

section
variable {P : Type} (BI : Blocks P)

theorem cv_spec (o : Output P) (hK : BlocksContracts BI o.platform) :
    Output.chaining_value BI o ⦃ v => cvOf v = (absN o).cv ⦄ := by
  unfold Output.chaining_value
  step with hK.in_place o.input_chaining_value o.block o.block_len o.counter o.flags as ⟨cv, hcv⟩
  apply WP.spec_mono (le_bytes_spec cv)
  intro r hr
  rw [cvOf_le_bytes r cv hr, hcv]; rfl

theorem root_spec (o : Output P) (hK : BlocksContracts BI o.platform) :
    Output.root_bytes BI o ⦃ v => toBA v.val = Blake3.output (absN o) 32 ⦄ := by
  unfold Output.root_bytes
  step as ⟨i, hi⟩
  step with hK.in_place o.input_chaining_value o.block o.block_len 0#u64 i as ⟨cv, hcv⟩
  apply WP.spec_mono (le_bytes_spec cv)
  intro r hr
  have hroot : UInt32.ofNat i.val = UInt32.ofNat o.flags.val ||| Blake3.ROOT := by
    rw [hi, ofNat_or]; simp [ROOT]; rfl
  rw [hr, hcv, hroot, bytesLE_first8]
  simp [Blake3.output, absN]

theorem chunk_output_spec (cpy : core.marker.Copy P) (key : Vector Blake3.Word 8) (mode : Blake3.Word) (t : Nat)
    (B : List Std.U8) (st : ChunkState P) (h : CInv key mode t B st) :
    ChunkState.output BI cpy st ⦃ o => absN o = Blake3.chunkNode key mode (toBA B) t ∧ o.platform = st.platform ⦄ := by
  unfold ChunkState.output
  rw [start_flag_eq]
  step*
  rw [node_eq key mode t B st h]
  have hmode : UInt32.ofNat st.flags.val = mode := h.1.2.1
  have hfl : UInt32.ofNat i2.val =
      (mode ||| if st.blocks_compressed.val = 0 then Blake3.CHUNK_START else 0) ||| Blake3.CHUNK_END := by
    rw [i2_post, ofNat_or, i1_post, ofNat_or, hmode]
    by_cases hb : st.blocks_compressed = 0#u8
    · have : st.blocks_compressed.val = 0 := by rw [hb]; rfl
      simp [hb, CHUNK_START, CHUNK_END]; rfl
    · have : st.blocks_compressed.val ≠ 0 := fun h' => hb (by scalar_tac)
      simp [hb, this, CHUNK_END]; rfl
  have hcnt : st.chunk_counter.val = t := h.1.1
  simp only [absN, hfl, hcnt]

end

theorem parent_output_spec {P : Type} (left right : Std.Array Std.U8 32#usize) (key : Std.Array Std.U32 8#usize)
    (flags : Std.U8) (p : P) :
    parent_output left right key flags p ⦃ o =>
      absN o = Blake3.parentNode (wv key) (UInt32.ofNat flags.val) (cvOf left) (cvOf right) ∧ o.platform = p ⦄ := by
  unfold parent_output
  step*
  have hblk : (index_mut_back1 s5).val = left.val ++ right.val := by
    rw [s3_post2, s5_post, s4_post, s_post2, s2_post, s1_post]
    apply List.ext_getElem! (by simp)
    intro j
    by_cases hj : j < 32
    · simp_lists
    · by_cases hj64 : j < 64
      · rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega, by simp; omega, by simp; omega⟩]
        simp only [Std.Array.to_slice, List.getElem!_eq_getElem?_getD,
          List.getElem?_append_right (by simp; omega : left.val.length ≤ j)]
        simp
      · rw [List.getElem!_setSlice!_suffix _ _ _ _ (by simp; omega)]
        simp only [List.getElem!_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hfl : UInt32.ofNat i1.val = UInt32.ofNat flags.val ||| Blake3.PARENT := by
    rw [i1_post, ofNat_or]; simp [PARENT]; rfl
  have hlen : UInt32.ofNat i.val = 64 := by rw [i_post]; simp [BLOCK_LEN]
  have hlr := wordsLE_append left.val right.val (by simp)
  simp only [absN, Blake3.parentNode, hblk, hfl, hlen]
  rw [hlr]; rfl

/-! ## The Hasher's kernels -/

section
variable {P H : Type} (BI : Blocks P) (cpy : core.marker.Copy P) (HI : Hooks H)

/-- The hooks meet their contracts, as the Hasher's Contracts state them for
`ones`, `subtree_len`, `subtree_cv`, and `children`. -/
structure HookContracts (h : H) (key : Vector Blake3.Word 8) (mode : Blake3.Word) : Prop where
  ones : ∀ x, HI.ones h x ⦃ r => r.val = HasherProof.ones x.val ⦄
  subtree_len : ∀ (c : Std.U64) (r : Std.Usize), 1024 < r.val →
    HI.subtree_len h c r ⦃ q => ∃ j, q.val = 1024 * 2 ^ j ∧ 2 ^ j ∣ c.val ∧ q.val ≤ r.val ⦄
  subtree_cv : ∀ (x : Slice Std.U8) (a : Std.Usize) (c : Std.U64), 1024 ≤ x.length →
    HI.subtree_cv h x a c ⦃ o => ∀ v, o = some v →
      cvOf v = (goIdx (leafN key mode x.val c.val) (nodeOp key mode) c.val (chunks x.length)).cv ⦄
  children : ∀ (x : Slice Std.U8) (a : Std.Usize) (c : Std.U64), 1024 < x.length →
    HI.children h x a c ⦃ r => ∃ L R : Blake3.Node,
      nodeOp key mode L R = goIdx (leafN key mode x.val c.val) (nodeOp key mode) c.val (chunks x.length) ∧
      r.val.map cvOf = [L.cv, R.cv] ⦄

theorem kernels_parent_spec (k : Kernels P H) (hK : BlocksContracts BI k.platform) (a b : StackProof.Cv) :
    Kernels.Insts.HashercoreParent.parent BI cpy k a b ⦃ v => cvOf v =
      cvOp (wv k.key) (UInt32.ofNat k.flags.val) (cvOf a) (cvOf b) ⦄ := by
  unfold Kernels.Insts.HashercoreParent.parent
  step with parent_output_spec a b k.key k.flags k.platform as ⟨o, ho, hp⟩
  apply WP.spec_mono (cv_spec BI o (hp ▸ hK))
  intro v hv
  rw [hv, ho]; rfl

/-- `Kernels` meets the Hasher's contracts, on a platform whose compression
kernels meet theirs and hooks that meet theirs. -/
theorem kernels_contracts (k : Kernels P H) (key : Vector Blake3.Word 8) (mode : Blake3.Word)
    (hkey : wv k.key = key) (hmode : UInt32.ofNat k.flags.val = mode)
    (hK : BlocksContracts BI k.platform) (hH : HookContracts HI k.hooks key mode) :
    Contracts (ChunkState.Insts.HashercoreChunk BI) (Kernels.Insts.HashercoreFeedChunkState BI cpy HI) k
      key mode cvOf (Rel BI key mode) where
  counter := inst_counter BI key mode
  len := inst_len BI key mode
  update := fun ch c P x h hl => inst_update BI key mode ch c P x h hl
  advance := fun ch c n h hm => inst_advance BI key mode ch c n h hm
  parent := fun a b => by
    have h := kernels_parent_spec BI cpy k hK a b
    rw [hkey, hmode] at h; exact h
  ones := hH.ones
  subtree_len := hH.subtree_len
  new_chunk := fun c => by
    apply WP.spec_mono (new_spec BI k.key c k.flags k.platform)
    rintro st ⟨h, hp⟩
    exact ⟨hkey ▸ hmode ▸ h, hp ▸ hK⟩
  chunk_cv := fun ch c P h _ => by
    simp only [Kernels.Insts.HashercoreFeedChunkState.chunk_cv]
    step with chunk_output_spec BI cpy key mode c P ch h.1 as ⟨o, ho, hp⟩
    apply WP.spec_mono (cv_spec BI o (hp ▸ h.2))
    intro v hv; rw [hv, ho]
  whole_chunk_cv := fun x c hx => by
    simp only [Kernels.Insts.HashercoreFeedChunkState.whole_chunk_cv]
    step with new_spec BI k.key c k.flags k.platform as ⟨st, h0, hp0⟩
    step with absorb_spec BI (wv k.key) (UInt32.ofNat k.flags.val) c.val [] st h0 (hp0 ▸ hK) x (by simp [hx])
      as ⟨st1, h1, hp1⟩
    step with chunk_output_spec BI cpy _ _ c.val _ st1 h1 as ⟨o, ho, hp⟩
    apply WP.spec_mono (cv_spec BI o (by rw [hp, hp1, hp0]; exact hK))
    intro v hv; rw [hv, ho, hkey, hmode]; simp
  subtree_cv := hH.subtree_cv
  children := hH.children

/-- A node stands for the specification's node `X`: it reads as `X`, on a
platform whose compression kernels meet their contracts. -/
def NRel (o : Output P) (X : Blake3.Node) : Prop := absN o = X ∧ BlocksContracts BI o.platform

/-- `Kernels` meets the Hasher's node contracts, on a platform whose
compression kernels meet theirs. -/
theorem kernels_node_contracts (k : Kernels P H) (key : Vector Blake3.Word 8) (mode : Blake3.Word)
    (hkey : wv k.key = key) (hmode : UInt32.ofNat k.flags.val = mode)
    (hK : BlocksContracts BI k.platform) :
    NodeContracts (ChunkState.Insts.HashercoreChunk BI) (Kernels.Insts.HashercoreNodesChunkStateOutput H BI cpy) k
      key mode cvOf (Rel BI key mode) (NRel BI) where
  len := inst_len BI key mode
  chunk_node := fun ch c P h => by
    simp only [Kernels.Insts.HashercoreNodesChunkStateOutput.chunk_node]
    apply WP.spec_mono (chunk_output_spec BI cpy key mode c P ch h.1)
    exact fun o ho => ⟨ho.1, ho.2 ▸ h.2⟩
  parent_node := fun a b => by
    simp only [Kernels.Insts.HashercoreNodesChunkStateOutput.parent_node]
    apply WP.spec_mono (parent_output_spec a b k.key k.flags k.platform)
    intro o ho; exact ⟨by rw [ho.1, hkey, hmode], ho.2 ▸ hK⟩
  node_cv := fun n X h => by
    simp only [Kernels.Insts.HashercoreNodesChunkStateOutput.node_cv]
    apply WP.spec_mono (cv_spec BI n h.2)
    intro v hv; rw [hv, h.1]

/-- The Hasher's root node after `pieces`, on the chunk state `ch0`: each
update's `fill` on `k₁`, its `feed` on `k₂`, then `final_node` on `k₃`, as
src/lib.rs runs them. -/
def rootNode (k₁ k₂ k₃ : Kernels P H) (ch0 : ChunkState P) (pieces : List (Slice Std.U8)) :
    Result (Output P) := do
  let (ch, st) ← updates (ChunkState.Insts.HashercoreChunk BI) (Kernels.Insts.HashercoreFeedChunkState BI cpy HI)
    (Kernels.Insts.HashercoreFeedChunkState BI cpy HI) k₁ k₂ ch0 ⟨none, 0#usize⟩ pieces
  final_node (ChunkState.Insts.HashercoreChunk BI) (Kernels.Insts.HashercoreNodesChunkStateOutput H BI cpy) k₃ ch st

/-- The Hasher on `Kernels` over hooks that meet their contracts: a new chunk
state on the key and flags, any updates, and the first 32 bytes of the
root's output are the specification's hash of all the updates' bytes. -/
theorem hasher_hash (k₁ k₂ k₃ : Kernels P H) (key : Std.Array Std.U32 8#usize) (flags : Std.U8) (p : P)
    (hK : BlocksContracts BI p)
    (h₁ : k₁.key = key ∧ k₁.flags = flags ∧ k₁.platform = p)
    (h₂ : k₂.key = key ∧ k₂.flags = flags ∧ k₂.platform = p)
    (h₃ : k₃.key = key ∧ k₃.flags = flags ∧ k₃.platform = p)
    (hH₁ : HookContracts HI k₁.hooks (wv key) (UInt32.ofNat flags.val))
    (hH₂ : HookContracts HI k₂.hooks (wv key) (UInt32.ofNat flags.val))
    (pieces : List (Slice Std.U8)) (hbound : (pieces.map (fun x => x.length)).sum < 1024 * 2 ^ 54) :
    (do
      let ch0 ← ChunkState.new BI key 0#u64 flags p
      let n ← rootNode BI cpy HI k₁ k₂ k₃ ch0 pieces
      Output.root_bytes BI n) ⦃ r =>
      toBA r.val = Blake3.blake3 (wv key) (UInt32.ofNat flags.val) (toBA (pieces.map (fun x => x.val)).flatten) 32 ⦄ := by
  obtain ⟨hk1, hf1, hp1⟩ := h₁
  obtain ⟨hk2, hf2, hp2⟩ := h₂
  obtain ⟨hk3, hf3, hp3⟩ := h₃
  step with new_spec BI key 0#u64 flags p as ⟨ch0, h0, hp0⟩
  apply WP.spec_bind (Pₘ := fun n => NRel BI n (RootNode (wv key) (UInt32.ofNat flags.val)
    (pieces.map (fun x => x.val)).flatten))
  · exact hasher_spec (wv key) (UInt32.ofNat flags.val) cvOf _ _ _ _ k₁ k₂ k₃
      (Rel BI (wv key) (UInt32.ofNat flags.val)) (NRel BI)
      (kernels_contracts BI cpy HI k₁ _ _ (by rw [hk1]) (by rw [hf1]) (hp1 ▸ hK) hH₁)
      (kernels_contracts BI cpy HI k₂ _ _ (by rw [hk2]) (by rw [hf2]) (hp2 ▸ hK) hH₂)
      (kernels_node_contracts BI cpy k₃ _ _ (by rw [hk3]) (by rw [hf3]) (hp3 ▸ hK))
      ch0 ⟨h0, hp0 ▸ hK⟩ pieces hbound
  rintro n ⟨hn, hnp⟩
  apply WP.spec_mono (root_spec BI n hnp)
  intro r hr
  rw [hr, hn, blake3_root]

end

end OutputProof

#print axioms OutputProof.le_bytes_spec
#print axioms OutputProof.cv_spec
#print axioms OutputProof.root_spec
#print axioms OutputProof.chunk_output_spec
#print axioms OutputProof.parent_output_spec
#print axioms OutputProof.kernels_contracts
#print axioms OutputProof.kernels_node_contracts
#print axioms OutputProof.hasher_hash
