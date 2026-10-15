import Schedule

open Schedule

/-! `run_eq`: the schedule, run, is the specification's 32-byte output. -/


theorem get!_def (b : ByteArray) (k : Nat) : b.get! k = (b.data[k]?).getD 0 := by
  cases b; simp only [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]; rfl

theorem extract_get! (b : ByteArray) (s e k : Nat) (hk : s + k < e) :
    (b.extract s e).get! k = b.get! (s + k) := by
  rw [get!_def, get!_def, ByteArray.data_extract, Array.getElem?_extract]
  have hs : b.size = b.data.size := rfl
  by_cases h : k < min e b.data.size - s
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, Array.getElem?_eq_none (by omega : b.data.size ≤ s + k)]

theorem msgWord_chunk (b : ByteArray) (i j w : Nat) (hj : j < 16) (hw : w < 16) :
    msgWord b (256 * i + 16 * j + w) =
      (Blake3.wordsLE (b.extract (1024 * i) (1024 * (i + 1))) (64 * j) 16)[w]'hw := by
  simp only [msgWord, Blake3.wordsLE, Vector.getElem_ofFn]
  have e : ∀ k, k < 4 → (b.extract (1024 * i) (1024 * (i + 1))).get! (64 * j + 4 * w + k) =
      b.get! (4 * (256 * i + 16 * j + w) + 4 * 0 + k) := by
    intro k hk
    rw [extract_get! _ _ _ _ (by omega)]
    congr 1; omega
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]

section
variable (key : Vector Blake3.Word 8) (mode : Blake3.Word) (b : ByteArray)

/-- One entry performed: its chaining value appended. -/
def step (cvs : List (Vector Blake3.Word 8)) (e : Entry) : List (Vector Blake3.Word 8) :=
  cvs ++ [Blake3.first8 (compressEntry key mode b cvs e 0)]

theorem cvsOf_eq (es : List Entry) : cvsOf key mode b es = es.foldl (step key mode b) [] := rfl

/-- The node an entry stands for, given the chaining values before it. -/
def nodeOf (cvs : List (Vector Blake3.Word 8)) (e : Entry) : Blake3.Node :=
  { h := Vector.ofFn fun i => word key b cvs (e.h[i.val]!)
    m := Vector.ofFn fun i => word key b cvs (e.m[i.val]!)
    t := e.t.toUInt64, len := e.len.toUInt32, flags := mode ||| e.flags.toUInt32 }

theorem compressEntry_eq (cvs : List (Vector Blake3.Word 8)) (e : Entry) (extra : Blake3.Word) :
    compressEntry key mode b cvs e extra =
      Blake3.BLAKE3_COMPRESS (nodeOf key mode b cvs e).h (nodeOf key mode b cvs e).m
        (nodeOf key mode b cvs e).t (nodeOf key mode b cvs e).len ((nodeOf key mode b cvs e).flags ||| extra) := rfl

theorem step_eq (cvs : List (Vector Blake3.Word 8)) (e : Entry) :
    step key mode b cvs e = cvs ++ [(nodeOf key mode b cvs e).cv] := by
  rw [step, compressEntry_eq, UInt32.or_zero]; rfl

theorem keyWords (cvs : List (Vector Blake3.Word 8)) :
    (Vector.ofFn fun i : Fin 8 => word key b cvs (((List.range 8).map Src.key)[i.val]!)) = key := by
  apply Vector.ext; intro i hi
  simp [word]

theorem cvWords (cvs : List (Vector Blake3.Word 8)) (e : Nat) (he : e < cvs.length) :
    (Vector.ofFn fun i : Fin 8 => word key b cvs (((List.range 8).map (Src.cv e))[i.val]!)) = cvs[e] := by
  apply Vector.ext; intro i hi
  simp [word, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem he]
end

theorem flags_eq (mode : Blake3.Word) (j blocks : Nat) :
    mode ||| (((if j = 0 then 1 else 0) ||| (if j + 1 = blocks then 2 else 0) : Nat)).toUInt32 =
      (mode ||| if j = 0 then Blake3.CHUNK_START else 0) ||| if j + 1 = blocks then Blake3.CHUNK_END else 0 := by
  by_cases h1 : j = 0 <;> by_cases h2 : j + 1 = blocks
  · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h1, ite_eq_left h2, UInt32.or_assoc]; rfl
  · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1, ite_eq_right h2, UInt32.or_zero]; rfl
  · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1, ite_eq_left h2, UInt32.or_zero]; rfl
  · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2, UInt32.or_zero]; rfl

section chunk
variable (key : Vector Blake3.Word 8) (mode : Blake3.Word) (b : ByteArray) (i base : Nat)

/-- Chunk `i`'s bytes. -/
abbrev chunkB : ByteArray := b.extract (1024 * i) (1024 * (i + 1))

theorem chunkB_size : (chunkB b i).size = chunkSize b.size i := by
  simp [chunkB, chunkSize, ByteArray.size_extract]; omega

/-- The chain's value after `k` blocks, as `chunkNode_eq` writes it. -/
def chainH (k : Nat) : Vector Blake3.Word 8 :=
  (List.range k).foldl (fun r j =>
    Blake3.first8 (Blake3.BLAKE3_COMPRESS r (Blake3.wordsLE (chunkB b i) (64 * j) 16) (UInt64.ofNat i) 64
      ((mode ||| if j = 0 then Blake3.CHUNK_START else 0) |||
        if j + 1 = Blake3.blockCount (chunkB b i).size then Blake3.CHUNK_END else 0))) key

theorem blockCount_le (n : Nat) : Blake3.blockCount (min 1024 n) ≤ 16 := by
  unfold Blake3.blockCount; omega

theorem msgWords (cvs : List (Vector Blake3.Word 8)) (j : Nat) (hj : j < 16) :
    (Vector.ofFn fun w : Fin 16 =>
      word key b cvs (((List.range 16).map fun w => Src.msg (256 * i + 16 * j + w))[w.val]!)) =
      Blake3.wordsLE (chunkB b i) (64 * j) 16 := by
  apply Vector.ext; intro w hw
  simp only [Vector.getElem_ofFn]
  rw [show ((List.range 16).map fun w => Src.msg (256 * i + 16 * j + w))[w]! = Src.msg (256 * i + 16 * j + w) by
    simp [hw]]
  exact msgWord_chunk b i j w hj hw

theorem chainH_succ (k : Nat) : chainH key mode b i (k + 1) =
    Blake3.first8 (Blake3.BLAKE3_COMPRESS (chainH key mode b i k) (Blake3.wordsLE (chunkB b i) (64 * k) 16)
      (UInt64.ofNat i) 64 ((mode ||| if k = 0 then Blake3.CHUNK_START else 0) |||
        if k + 1 = Blake3.blockCount (chunkB b i).size then Blake3.CHUNK_END else 0)) := by
  simp only [chainH, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem chunkEntries_length (size : Nat) : (chunkEntries base i size).length = Blake3.blockCount size := by
  simp [chunkEntries]

/-- Entry `k` of chunk `i`, after chaining values whose entry `base + k - 1` is the chain's. -/
theorem entry_node (k : Nat) (hk : k < Blake3.blockCount (chunkSize b.size i))
    (cvs : List (Vector Blake3.Word 8)) (hc : base + k ≤ cvs.length)
    (hv : ∀ h : 0 < k, cvs[base + k - 1]'(by omega) = chainH key mode b i k) :
    nodeOf key mode b cvs ((chunkEntries base i (chunkSize b.size i))[k]'(by
        rw [chunkEntries_length]; exact hk)) =
      { h := chainH key mode b i k, m := Blake3.wordsLE (chunkB b i) (64 * k) 16, t := UInt64.ofNat i,
        len := (if k + 1 = Blake3.blockCount (chunkB b i).size then chunkSize b.size i - 64 * k else 64 : Nat).toUInt32,
        flags := (mode ||| if k = 0 then Blake3.CHUNK_START else 0) |||
          if k + 1 = Blake3.blockCount (chunkB b i).size then Blake3.CHUNK_END else 0 } := by
  have h16 := blockCount_le (b.size - 1024 * i)
  have hE : (chunkEntries base i (chunkSize b.size i))[k]'(by rw [chunkEntries_length]; exact hk) =
      { h := if k = 0 then (List.range 8).map Src.key else (List.range 8).map (Src.cv (base + k - 1))
        m := (List.range 16).map fun w => Src.msg (256 * i + 16 * k + w)
        t := i
        len := if k + 1 = Blake3.blockCount (chunkSize b.size i) then chunkSize b.size i - 64 * k else 64
        flags := (if k = 0 then 1 else 0) ||| (if k + 1 = Blake3.blockCount (chunkSize b.size i) then 2 else 0) } := by
    simp only [chunkEntries, List.getElem_map, List.getElem_range]
  rw [hE, nodeOf, Blake3.Node.mk.injEq, chunkB_size]
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · by_cases h0 : k = 0
    · subst h0; exact keyWords key b cvs
    · simp only [ite_eq_right h0]
      rw [cvWords key b cvs _ (by omega)]; exact hv (by omega)
  · exact msgWords key b i cvs k (by simp only [chunkSize] at hk h16; omega)
  · by_cases h : k + 1 = Blake3.blockCount (chunkSize b.size i)
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
  · exact flags_eq mode k _

theorem chain (k : Nat) (hk : k + 1 ≤ Blake3.blockCount (chunkSize b.size i))
    (cvs : List (Vector Blake3.Word 8)) (hc : cvs.length = base) :
    ((chunkEntries base i (chunkSize b.size i)).take k).foldl (step key mode b) cvs =
      cvs ++ (List.range k).map fun j => chainH key mode b i (j + 1) := by
  have h16 := blockCount_le (b.size - 1024 * i)
  induction k with
  | zero => simp
  | succ k ih =>
    have hlen := chunkEntries_length i base (chunkSize b.size i)
    rw [List.take_add_one, List.foldl_append, ih (by omega), List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, step_eq, List.range_succ, List.map_append,
      List.map_cons, List.map_nil, List.append_assoc]
    congr 2
    rw [chainH_succ, Blake3.Node.cv, entry_node key mode b i base k (by omega) _ (by simp; omega)]
    · simp only [chunkB_size, ite_eq_right (by omega : ¬ k + 1 = Blake3.blockCount (chunkSize b.size i))]; rfl
    · intro h0
      rw [List.getElem_append_right (by omega)]
      simp only [List.getElem_map, List.getElem_range]
      congr 1; omega

/-- The specification's chunk node, its chain below the last block as a fold (as in `ChunkProofs`). -/
theorem chunkNode_eq (B : ByteArray) (t : Nat) :
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

theorem blockCount_pos (n : Nat) : 1 ≤ Blake3.blockCount n := by unfold Blake3.blockCount; omega

/-- A chunk's entries: all but the last chain as the specification's chunk does, and the last
is its chunk node. -/
theorem chunk_entries (cvs : List (Vector Blake3.Word 8)) (hc : cvs.length = base) :
    let E := chunkEntries base i (chunkSize b.size i)
    ∃ Y, E.dropLast.foldl (step key mode b) cvs = cvs ++ Y ∧ Y.length = E.length - 1 ∧
      ∃ hE : E ≠ [], nodeOf key mode b (cvs ++ Y) (E.getLast hE) = Blake3.chunkNode key mode (chunkB b i) i := by
  intro E
  have hlen : E.length = Blake3.blockCount (chunkSize b.size i) := chunkEntries_length i base _
  have hpos := blockCount_pos (chunkSize b.size i)
  have hne : E ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
  refine ⟨(List.range (Blake3.blockCount (chunkSize b.size i) - 1)).map fun j => chainH key mode b i (j + 1),
    ?_, ?_, hne, ?_⟩
  · rw [List.dropLast_eq_take, hlen]
    exact chain key mode b i base _ (by omega) cvs hc
  · simp [hlen]
  · rw [List.getLast_eq_getElem]
    simp only [hlen]
    rw [entry_node key mode b i base _ (by omega) _ (by simp; omega), chunkNode_eq, chunkB_size]
    · simp only [ite_eq_left (by omega : Blake3.blockCount (chunkSize b.size i) - 1 + 1 = Blake3.blockCount (chunkSize b.size i))]
      rw [Blake3.Node.mk.injEq]
      exact ⟨by simp only [chainH, chunkB_size], rfl, rfl, rfl, rfl⟩
    · intro h0
      rw [List.getElem_append_right (by omega)]
      simp only [List.getElem_map, List.getElem_range]
      congr 1; omega
end chunk

section tree
variable (key : Vector Blake3.Word 8) (mode : Blake3.Word) (b : ByteArray)

/-- The specification's chunk nodes of `b` (as in `Blake3.blake3`). -/
def chunksOf : Array Blake3.Node :=
  (Array.range (max 1 ((b.size + 1023) / 1024))).map fun i =>
    Blake3.chunkNode key mode (b.extract (1024 * i) (1024 * (i + 1))) i

theorem chunksOf_get (i : Nat) (hi : i < max 1 ((b.size + 1023) / 1024)) :
    (chunksOf key mode b)[i]! = Blake3.chunkNode key mode (chunkB b i) i := by
  simp [chunksOf, hi]

/-- Performing entries appends one chaining value each. -/
theorem fold_append (es : List Entry) (cvs : List (Vector Blake3.Word 8)) :
    ∃ X, es.foldl (step key mode b) cvs = cvs ++ X ∧ X.length = es.length := by
  induction es generalizing cvs with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons e es ih =>
    obtain ⟨X, h1, h2⟩ := ih (step key mode b cvs e)
    exact ⟨[(nodeOf key mode b cvs e).cv] ++ X, by rw [List.foldl_cons, h1, step_eq, List.append_assoc], by simp [h2]⟩

theorem parentWords (cvs : List (Vector Blake3.Word 8)) (l r : Nat) (hl : l < cvs.length) (hr : r < cvs.length) :
    (Vector.ofFn fun i : Fin 16 =>
      word key b cvs ((((List.range 8).map (Src.cv l)) ++ (List.range 8).map (Src.cv r))[i.val]!)) =
      cvs[l] ++ cvs[r] := by
  apply Vector.ext; intro i hi
  have hlen : (((List.range 8).map (Src.cv l)) ++ (List.range 8).map (Src.cv r)).length = 16 := by simp
  simp only [Vector.getElem_ofFn]
  rw [getElem!_pos _ i (by omega)]
  by_cases h : i < 8
  · rw [List.getElem_append_left (by simp; omega)]
    simp [word, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    rw [Vector.getElem_append_left h, getElem!_pos cvs[l] i h]
  · rw [List.getElem_append_right (by simp; omega)]
    simp [word, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hr]
    rw [Vector.getElem_append_right (by omega) (by omega), getElem!_pos _ _ (by omega)]

/-- What a subtree's entries do, from chaining values `cvs`: all but the last append `Y`, and the
last is the specification's subtree node. -/
def SubOk (base start cnt : Nat) (cvs : List (Vector Blake3.Word 8)) : Prop :=
  ∃ (hS : subtree b.size base start cnt ≠ []) (Y : List (Vector Blake3.Word 8)),
    (subtree b.size base start cnt).dropLast.foldl (step key mode b) cvs = cvs ++ Y ∧
    Y.length = (subtree b.size base start cnt).length - 1 ∧
    nodeOf key mode b (cvs ++ Y) ((subtree b.size base start cnt).getLast hS) =
      Blake3.tree.go key mode (chunksOf key mode b) start cnt

theorem sub_full (base start cnt : Nat) (cvs : List (Vector Blake3.Word 8)) (h : SubOk key mode b base start cnt cvs) :
    ∃ Y, (subtree b.size base start cnt).foldl (step key mode b) cvs =
      cvs ++ Y ++ [(Blake3.tree.go key mode (chunksOf key mode b) start cnt).cv] ∧
      Y.length = (subtree b.size base start cnt).length - 1 := by
  obtain ⟨hS, Y, h1, h2, h3⟩ := h
  refine ⟨Y, ?_, h2⟩
  conv => lhs; rw [← List.dropLast_concat_getLast hS]
  rw [List.foldl_append, h1, List.foldl_cons, List.foldl_nil, step_eq, h3]

/-- A parent's entry, its children's chaining values those of entries `l` and `r`. -/
def pEntry (l r : Nat) : Entry :=
  { h := (List.range 8).map Src.key, m := (List.range 8).map (Src.cv l) ++ (List.range 8).map (Src.cv r),
    t := 0, len := 64, flags := 4 }

theorem getElem_mid {α : Type} (A B : List α) (x : α) (i : Nat) (hi : i = A.length) (h : i < (A ++ x :: B).length) :
    (A ++ x :: B)[i] = x := by
  subst hi; simp

theorem sub (cnt : Nat) : ∀ start base (cvs : List (Vector Blake3.Word 8)), cvs.length = base → 1 ≤ cnt →
    start + cnt ≤ max 1 ((b.size + 1023) / 1024) → SubOk key mode b base start cnt cvs := by
  induction cnt using Nat.strongRecOn with
  | _ cnt ih =>
  intro start base cvs hc h1 hcnt
  by_cases hle : cnt ≤ 1
  · have hS : subtree b.size base start cnt = chunkEntries base start (chunkSize b.size start) := by
      rw [subtree, ite_eq_left hle]
    obtain ⟨Y, hY1, hY2, hE, hY3⟩ := chunk_entries key mode b start base cvs hc
    refine ⟨hS ▸ hE, Y, by rw [hS]; exact hY1, by rw [hS]; exact hY2, ?_⟩
    have hg : Blake3.tree.go key mode (chunksOf key mode b) start cnt = (chunksOf key mode b)[start]! := by
      rw [Blake3.tree.go, dite_eq_left hle]
    rw [hg, chunksOf_get key mode b start (by omega)]
    simp only [hS]; exact hY3
  · have hk := Blake3.leftCount_lt cnt (by omega)
    have hk0 := Blake3.leftCount_pos cnt
    generalize hK : Blake3.leftCount cnt = k at hk hk0
    have hl := ih k hk start base cvs hc hk0 (by omega)
    have hLne := hl.1
    obtain ⟨Yl, hl1, hl2⟩ := sub_full key mode b _ _ _ _ hl
    generalize hLdef : subtree b.size base start k = left at hl1 hl2 hLne
    have hLlen : 1 ≤ left.length := List.length_pos_iff.mpr hLne
    have hr := ih (cnt - k) (by omega) (start + k) (base + left.length)
      (cvs ++ Yl ++ [(Blake3.tree.go key mode (chunksOf key mode b) start k).cv]) (by simp; omega) (by omega) (by omega)
    have hRne := hr.1
    obtain ⟨Yr, hr1, hr2⟩ := sub_full key mode b _ _ _ _ hr
    generalize hRdef : subtree b.size (base + left.length) (start + k) (cnt - k) = right at hr1 hr2 hRne
    have hRlen : 1 ≤ right.length := List.length_pos_iff.mpr hRne
    let pe := pEntry (base + left.length - 1) (base + left.length + right.length - 1)
    have hS : subtree b.size base start cnt = left ++ right ++ [pe] := by
      rw [subtree, ite_eq_right hle]; simp only [hK, hLdef, hRdef]; rfl
    have hne : subtree b.size base start cnt ≠ [] := by rw [hS]; simp
    let Ln := (Blake3.tree.go key mode (chunksOf key mode b) start k).cv
    let Rn := (Blake3.tree.go key mode (chunksOf key mode b) (start + k) (cnt - k)).cv
    refine ⟨hne, Yl ++ [Ln] ++ Yr ++ [Rn], ?_, ?_, ?_⟩
    · rw [hS, List.dropLast_concat, List.foldl_append, hl1, hr1]; simp [Ln, Rn]
    · rw [hS]; simp; omega
    · have hg : Blake3.tree.go key mode (chunksOf key mode b) start cnt =
          Blake3.parentNode key mode Ln Rn := by
        rw [Blake3.tree.go, dite_eq_right hle]; simp only [hK, Ln, Rn]
      rw [hg]
      simp only [hS, List.getLast_concat]
      rw [nodeOf, Blake3.parentNode, Blake3.Node.mk.injEq]
      simp only [pe, pEntry]
      refine ⟨keyWords key b _, ?_, rfl, rfl, rfl⟩
      rw [parentWords key b _ _ _ (by simp; omega) (by simp; omega)]
      congr 1
      · have : cvs ++ (Yl ++ [Ln] ++ Yr ++ [Rn]) = (cvs ++ Yl) ++ Ln :: (Yr ++ [Rn]) := by simp
        simp only [this]; exact getElem_mid _ _ _ _ (by simp; omega) _
      · have : cvs ++ (Yl ++ [Ln] ++ Yr ++ [Rn]) = (cvs ++ Yl ++ [Ln] ++ Yr) ++ Rn :: [] := by simp
        simp only [this]; exact getElem_mid _ _ _ _ (by simp; omega) _
end tree

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

theorem go_t (key : Vector Blake3.Word 8) (mode : Blake3.Word) (b : ByteArray) (cnt : Nat) (_ : 1 ≤ cnt) :
    (Blake3.tree.go key mode (chunksOf key mode b) 0 cnt).t = 0 := by
  rw [Blake3.tree.go]
  split
  · rw [chunksOf_get key mode b 0 (by omega), chunkNode_eq]; rfl
  · rfl

/-- The schedule's run is the specification's 32-byte output, for every key, mode, and input. -/
theorem run_eq (key : Vector Blake3.Word 8) (mode : Blake3.Word) (b : ByteArray) :
    run key mode b = Blake3.blake3 key mode b 32 := by
  have hcnt : 1 ≤ max 1 ((b.size + 1023) / 1024) := by omega
  obtain ⟨hS, Y, h1, -, h3⟩ := sub key mode b _ 0 0 [] rfl hcnt (by omega)
  have hroot := go_t key mode b _ hcnt
  simp only [run, sched, cvsOf_eq] at *
  rw [List.nil_append] at h3
  rw [List.getLast!_of_getLast? (List.getLast?_eq_some_getLast hS), h1, List.nil_append, compressEntry_eq, h3]
  have hsize : (chunksOf key mode b).size = max 1 ((b.size + 1023) / 1024) := by simp [chunksOf]
  have hrhs : Blake3.blake3 key mode b 32 =
      Blake3.output (Blake3.tree.go key mode (chunksOf key mode b) 0 (max 1 ((b.size + 1023) / 1024))) 32 := by
    rw [← hsize]; rfl
  rw [hrhs]
  generalize Blake3.tree.go key mode (chunksOf key mode b) 0 (max 1 ((b.size + 1023) / 1024)) = R at hroot ⊢
  have hr : (32 + 63) / 64 = 1 := rfl
  simp only [Blake3.output, hr, List.range_one, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, ← bytesLE_first8, hroot]
  rfl
#print axioms run_eq
