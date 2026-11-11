import MergeParts
open X86

namespace MergeCode

/-! What one whole turn of `merge`'s loop shows. Written by tracegen.py. -/

theorem stepsL_add (prog : Nat → Option (Instr × Nat)) (a b : Nat) (s : LState) :
    stepsL prog (a + b) s = (stepsL prog a s).bind (stepsL prog b) := by
  induction a generalizing s with
  | zero => simp [stepsL]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp only [stepsL]
    cases prog s.core.pc with
    | none => rfl
    | some x =>
      obtain ⟨i, next⟩ := x
      simp only []
      cases stepL i next s with
      | none => rfl
      | some s1 => simp only [Option.bind_some, ih]

theorem lstate_eq (S : LState) (c : State) (l : List Obs) (h1 : S.core = c) (h2 : S.leak = l) : S = ⟨c, l⟩ := by
  cases S; simp only at h1 h2; subst h1 h2; rfl

/-- The recorded run's state is the model's run's. -/
theorem core_of {prog : Nat → Option (Instr × Nat)} {N : Nat} {c : State} {l : List Obs} {S : LState} {s' : State}
    (hS : stepsL prog N ⟨c, l⟩ = some S) (hs : steps prog N c = some s') : S.core = s' := by
  have h := stepsL_core prog N ⟨c, l⟩
  rw [hS, hs] at h
  exact Option.some.inj h

/-- Two recorded runs, one after the other: the second's trace on top of the first's. -/
theorem stepsL_chain (prog : Nat → Option (Instr × Nat)) (a b : Nat) (c c1 : State) (l1 : List Obs) (S2 : LState)
    (h1 : stepsL prog a ⟨c, []⟩ = some ⟨c1, l1⟩) (h2 : stepsL prog b ⟨c1, []⟩ = some S2) :
    stepsL prog (a + b) ⟨c, []⟩ = some ⟨S2.core, S2.leak ++ l1⟩ := by
  rw [stepsL_add, h1, Option.bind_some]
  have h := stepsL_seen prog b c1 [] l1
  rw [List.nil_append] at h
  rw [h, h2]; rfl

/-- A result proved of the model's run holds of the recorded run's state. -/
theorem both {prog : Nat → Option (Instr × Nat)} {N : Nat} {c : State} {L : List Obs} {P : State → Prop}
    (hc : ∃ s', steps prog N c = some s' ∧ P s') (hl : ∃ S, stepsL prog N ⟨c, []⟩ = some S ∧ S.leak = L) :
    ∃ S, stepsL prog N ⟨c, []⟩ = some S ∧ S.leak = L ∧ P S.core := by
  obtain ⟨s', hs, hp⟩ := hc
  obtain ⟨S, hS, hL⟩ := hl
  have h := stepsL_core prog N ⟨c, []⟩
  rw [hS, hs] at h
  have e : S.core = s' := Option.some.inj h
  exact ⟨S, hS, hL, by rw [e]; exact hp⟩

/-- What each one-block kernel shows, as a function of the three addresses it is given and its return
address (`Leak.lean` proves there is one). -/
noncomputable def avxShows (rdi rsi rsp ra : BitVec 64) : List Obs :=
  Classical.choose (avx512_kernel_shows_only_addresses rdi rsi rsp ra)
noncomputable def sseShows (rdi rsi rsp ra : BitVec 64) : List Obs :=
  Classical.choose (sse41_kernel_shows_only_addresses rdi rsi rsp ra)
theorem avxShows_spec (rdi rsi rsp ra : BitVec 64) : ∀ (s : State) (cv0 cv1 b0 b1 b2 b3 : V),
    s.pc = 0x30000 → s.rdi = rdi → s.rsi = rsi → s.rsp = rsp →
    Vec s.mem (s.rdi + 0) cv0 → Vec s.mem (s.rdi + 16) cv1 →
    Vec s.mem (s.rsi + 0) b0 → Vec s.mem (s.rsi + 16) b1 → Vec s.mem (s.rsi + 32) b2 → Vec s.mem (s.rsi + 48) b3 →
    s.mem.read s.rsp 64 = some ra → (∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) →
    ∃ S, stepsL Code.prog 362 ⟨s, []⟩ = some S ∧ S.leak = avxShows rdi rsi rsp ra :=
  Classical.choose_spec (avx512_kernel_shows_only_addresses rdi rsi rsp ra)
theorem sseShows_spec (rdi rsi rsp ra : BitVec 64) : ∀ (s : State) (cv0 cv1 b0 b1 b2 b3 : V),
    s.pc = 0x20000 → s.rdi = rdi → s.rsi = rsi → s.rsp = rsp →
    Vec s.mem (s.rdi + 0) cv0 → Vec s.mem (s.rdi + 16) cv1 →
    Vec s.mem (s.rsi + 0) b0 → Vec s.mem (s.rsi + 16) b1 → Vec s.mem (s.rsi + 32) b2 → Vec s.mem (s.rsi + 48) b3 →
    s.mem.read s.rsp 64 = some ra → (∀ x, (x - s.rsp).toNat < 8 → 32 ≤ (x - s.rdi).toNat) →
    ∃ S, stepsL Code.prog 467 ⟨s, []⟩ = some S ∧ S.leak = sseShows rdi rsi rsp ra :=
  Classical.choose_spec (sse41_kernel_shows_only_addresses rdi rsi rsp ra)

/-- What one turn by the AVX-512 kernel shows: its last part, the kernel, its first part. -/
noncomputable def turn_avx_shows (self arr keyp fp len : BitVec 64) (last : Bool) : List Obs :=
  post_avx_shows self arr fp ((len + 18446744073709551614#64) <<< 5) last ++
    (avxShows (fp + 64#64) (fp + 128#64) (fp + 18446744073709551608#64) 262235#64 ++ pre_avx_shows self arr keyp fp len)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem turn_avx_leak (self arr keyp fp len n : BitVec 64) (l0 l1 r0 r1 k0 k1 : V) (fl : BitVec 8) (m : Mem)
    (rcx rdx rbp rsi rdi r8 r9 r13 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V)
    (hlo : 2#64 ≤ len) (hhi : len ≤ 55#64) (hfp : fp &&& 63#64 = 0#64)
    (hTag : m (self + 8#64) = some 1#8) (hLen : Quad m (self + 0#64) len)
    (hL0 : Vec m (arr + ((len + 18446744073709551614#64) <<< 5) + 0#64) l0) (hL1 : Vec m (arr + ((len + 18446744073709551614#64) <<< 5) + 16#64) l1)
    (hR0 : Vec m (arr + ((len + 18446744073709551615#64) <<< 5) + 0#64) r0) (hR1 : Vec m (arr + ((len + 18446744073709551615#64) <<< 5) + 16#64) r1)
    (hK0 : Vec m (keyp + 0#64) k0) (hK1 : Vec m (keyp + 16#64) k1)
    (hOwn : ∀ d : BitVec 64, inF d = true → (m (fp + d)).isSome = true)
    (hPlat : m (fp + 58#64) = some 5#8) (hFl : m (fp + 59#64) = some fl)
    (hF0 : m (fp + 60#64) = some fl) (hF1 : m (fp + 61#64) = some 0#8) (hF2 : m (fp + 62#64) = some 0#8) (hF3 : m (fp + 63#64) = some 0#8)
    -- the stack's two slots, the key, and the stack's length and tag are not in `merge`'s frame
    (oSlot : ∀ x : BitVec 64, (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat < 64 → inF (x - fp) = false)
    (oKey : ∀ x : BitVec 64, (x - keyp).toNat < 32 → inF (x - fp) = false)
    (oSelf : ∀ x : BitVec 64, (x - self).toNat < 9 → inF (x - fp) = false)
    -- the length is not in the lower slot
    (hLS : ∀ x : BitVec 64, (x - self).toNat < 8 → 32 ≤ (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat) :
    ∃ S, stepsL Code.prog (52 + (362 + 12)) ⟨⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m, 0x40094⟩, []⟩ = some S ∧
      S.leak = turn_avx_shows self arr keyp fp len (decide (n - 1#64 = 0#64)) := by
  -- the checks' flags, from the bounds
  have h1 : len.ult 1#64 = false := by bv_decide
  have h2 : (len - 1#64 == 0#64) = false := by bv_decide
  have h3 : (len + 18446744073709551614#64).ult 55#64 = true := by bv_decide
  have h4 : len.ult 56#64 = true := by bv_decide
  have eR : arr + ((len + 18446744073709551615#64) <<< 5) = arr + ((len + 18446744073709551614#64) <<< 5) + 32#64 := by bv_decide
  have eA : ((len + 18446744073709551614#64) <<< 5) + arr = arr + ((len + 18446744073709551614#64) <<< 5) := by bv_decide
  -- what the first part needs: reads outside the frame are reads of `m`
  have blk : ∀ (c : BitVec 64), c.toNat ≤ 48 → ∀ x : BitVec 64, (x - (arr + ((len + 18446744073709551614#64) <<< 5) + c)).toNat < 16 → inF (x - fp) = false := by
    intro c hc x hx; exact oSlot x (by bv_omega)
  have rTag : ∀ fF, (over m fp inF fF).read (self + 8#64) 8 = some 1#64 := by
    intro fF; rw [over_read8 _ _ _ _ _ (oSelf _ (by bv_omega))]; simp [Mem.read, Mem.read8, hTag]
  have rL0 : ∀ fF, (over m fp inF fF).read128 (arr + ((len + 18446744073709551614#64) <<< 5) + 0#64) = some l0 := by
    intro fF; rw [over_read128 _ _ _ _ _ (blk 0#64 (by decide)), read_vec hL0]
  have rL1 : ∀ fF, (over m fp inF fF).read128 (arr + ((len + 18446744073709551614#64) <<< 5) + 16#64) = some l1 := by
    intro fF; rw [over_read128 _ _ _ _ _ (blk 16#64 (by decide)), read_vec hL1]
  have rR0 : ∀ fF, (over m fp inF fF).read128 (arr + ((len + 18446744073709551615#64) <<< 5) + 0#64) = some r0 := by
    intro fF; rw [over_read128 _ _ _ _ _ (by rw [eR]; intro x hx; exact oSlot x (by bv_omega)), read_vec hR0]
  have rR1 : ∀ fF, (over m fp inF fF).read128 (arr + ((len + 18446744073709551615#64) <<< 5) + 16#64) = some r1 := by
    intro fF; rw [over_read128 _ _ _ _ _ (by rw [eR]; intro x hx; exact oSlot x (by bv_omega)), read_vec hR1]
  have rK0 : ∀ fF, (over m fp inF fF).read128 (keyp + 0#64) = some k0 := by
    intro fF; rw [over_read128 _ _ _ _ _ (fun x hx => oKey x (by bv_omega)), read_vec hK0]
  have rK1 : ∀ fF, (over m fp inF fF).read128 (keyp + 16#64) = some k1 := by
    intro fF; rw [over_read128 _ _ _ _ _ (fun x hx => oKey x (by bv_omega)), read_vec hK1]
  obtain ⟨S1, e1, pc1, di1, si1, dx1, cx1, r81, sp1, bx1, bp1, c12, c13, c14, c15, vK0, vK1, vL0, vL1, vR0, vR1, hret1, own1, out1,
      f58, f59, f60, f61, f62, f63⟩ :=
    pre_avx self arr keyp fp len n l0 l1 r0 r1 k0 k1 fl m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      h1 h2 h3 h4 hfp rTag rL0 rL1 rR0 rR1 rK0 rK1 hOwn hPlat hFl hF0 hF1 hF2 hF3
  rw [over_none] at e1
  -- the kernel, by its contract
  have hc0 : Vec S1.mem (S1.rdi + 0) k0 := by rw [di1, show fp + 64#64 + 0 = fp + 64#64 by bv_decide]; exact vK0
  have hc1 : Vec S1.mem (S1.rdi + 16) k1 := by rw [di1, show fp + 64#64 + 16 = fp + 80#64 by bv_decide]; exact vK1
  have hb0 : Vec S1.mem (S1.rsi + 0) l0 := by rw [si1, show fp + 128#64 + 0 = fp + 128#64 by bv_decide]; exact vL0
  have hb1 : Vec S1.mem (S1.rsi + 16) l1 := by rw [si1, show fp + 128#64 + 16 = fp + 144#64 by bv_decide]; exact vL1
  have hb2 : Vec S1.mem (S1.rsi + 32) r0 := by rw [si1, show fp + 128#64 + 32 = fp + 160#64 by bv_decide]; exact vR0
  have hb3 : Vec S1.mem (S1.rsi + 48) r1 := by rw [si1, show fp + 128#64 + 48 = fp + 176#64 by bv_decide]; exact vR1
  have hret : S1.mem.read S1.rsp 64 = some 262235#64 := by rw [sp1]; exact hret1
  have hapart : ∀ x, (x - S1.rsp).toNat < 8 → 32 ≤ (x - S1.rdi).toNat := by rw [sp1, di1]; intro x hx; bv_omega
  obtain ⟨s2, e2, pc2, sp2, mem2, bx2, bp2, d12, d13, d14, d15⟩ := Avx.contract k0 k1 l0 l1 r0 r1 262235#64 S1 pc1 hc0 hc1 hb0 hb1 hb2 hb3 hret hapart
  have pc2' : s2.pc = 0x4005B := pc2
  have sp2' : s2.rsp = fp := by rw [sp2, sp1]; bv_decide
  have mem2' : s2.mem = (S1.mem.put128 (fp + 64#64) (merged k0 k1 l0 l1 r0 r1 fl).1).put128 (fp + 80#64) (merged k0 k1 l0 l1 r0 r1 fl).2 := by
    have e8 : (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.setWidth 64 fl))) = BitVec.setWidth 32 fl := by bv_decide
    have e64 : (BitVec.setWidth 32 (BitVec.setWidth 8 (64#64))) = 64#32 := by decide
    rw [cx1, dx1, r81, e8, e64] at mem2
    rw [mem2, di1, show fp + 64#64 + 0 = fp + 64#64 by bv_decide, show fp + 64#64 + 16 = fp + 80#64 by bv_decide]
    rfl
  -- the last part, on the kernel's memory
  obtain ⟨rax2, rcx2, rdx2, rbx2, rsp2, rbp2, rsi2, rdi2, r82, r92, r122, r132, r142, r152, zf2, cf2,
    y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, b, pcv⟩ := s2
  simp only at pc2' sp2' mem2' bx2 bp2 d12 d13 d14 d15
  rw [bx1] at bx2; rw [bp1] at bp2; rw [c12] at d12; rw [c13] at d13; rw [c14] at d14; rw [c15] at d15
  subst pcv rsp2 rbx2 rbp2 r122 r132 r142 r152
  have b_out : ∀ x : BitVec 64, inF (x - fp) = false → b x = m x := by
    intro x hx
    have hx' : 392 ≤ (x - fp + 8#64).toNat := by simp only [inF, BitVec.ult] at hx; simpa using hx
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega), out1 x hx]
  have b_own : ∀ d : BitVec 64, inF d = true → (b (fp + d)).isSome = true := by
    intro d hd; rw [mem2']; exact put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (own1 d hd))
  have hC0 : Vec b (fp + 64#64) (merged k0 k1 l0 l1 r0 r1 fl).1 := by
    rw [mem2']; exact vec_congr (fun x hx => by rw [put128_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
  have hC1 : Vec b (fp + 80#64) (merged k0 k1 l0 l1 r0 r1 fl).2 := by rw [mem2']; exact vec_put128 _ _ _
  have oA1 : ∀ x : BitVec 64, (x - (((len + 18446744073709551614#64) <<< 5) + arr + 16#64)).toNat < 16 → inF (x - fp) = false := by
    rw [eA]; exact blk 16#64 (by decide)
  have oA0 : ∀ x : BitVec 64, (x - (((len + 18446744073709551614#64) <<< 5) + arr + 0#64)).toNat < 16 → inF (x - fp) = false := by
    rw [eA]; exact blk 0#64 (by decide)
  have oLen : ∀ x : BitVec 64, (x - (self + 0#64)).toNat < 8 → inF (x - fp) = false := fun x hx => oSelf x (by bv_omega)
  have ownA1 : Owned16 b (((len + 18446744073709551614#64) <<< 5) + arr + 16#64) := by
    rw [eA]; exact owned16_congr (fun x hx => b_out x (blk 16#64 (by decide) x hx)) (vec_owned hL1)
  have ownA0 : Owned16 b (((len + 18446744073709551614#64) <<< 5) + arr + 0#64) := by
    rw [eA]; exact owned16_congr (fun x hx => b_out x (blk 0#64 (by decide) x hx)) (vec_owned hL0)
  have lenB : ∀ (v w : V), Quad ((b.put128 (((len + 18446744073709551614#64) <<< 5) + arr + 16#64) w).put128 (((len + 18446744073709551614#64) <<< 5) + arr + 0#64) v) (self + 0#64) len := by
    intro v w
    refine quad_congr (fun x hx => ?_) hLen
    have := hLS x (by bv_omega)
    rw [put128_other _ _ _ _ (by rw [eA]; bv_omega), put128_other _ _ _ _ (by rw [eA]; bv_omega), b_out x (oLen x hx)]
  have notLen : ∀ x : BitVec 64, (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat < 32 → 8 ≤ (x - (self + 0#64)).toNat := fun x hx =>
    Nat.le_of_not_lt (fun h => by have := hLS x (by bv_omega); omega)
  have frameNotLen : ∀ d : BitVec 64, inF d = true → 8 ≤ (fp + d - (self + 0#64)).toNat := fun d hd =>
    Nat.le_of_not_lt (fun h => by have := oSelf (fp + d) (by bv_omega); rw [add_sub_self] at this; simp [hd] at this)
  have frameNotSlot : ∀ d : BitVec 64, inF d = true →
      16 ≤ (fp + d - (((len + 18446744073709551614#64) <<< 5) + arr + 0#64)).toNat ∧ 16 ≤ (fp + d - (((len + 18446744073709551614#64) <<< 5) + arr + 16#64)).toNat := fun d hd =>
    ⟨Nat.le_of_not_lt (fun h => by have := oSlot (fp + d) (by rw [← eA]; bv_omega); rw [add_sub_self] at this; simp [hd] at this),
     Nat.le_of_not_lt (fun h => by have := oSlot (fp + d) (by rw [← eA]; bv_omega); rw [add_sub_self] at this; simp [hd] at this)⟩
  have bF58 : b (fp + 58#64) = some 5#8 := by
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)]; exact f58
  have bF59 : b (fp + 59#64) = some fl := by
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)]; exact f59
  have bF60 : b (fp + 60#64) = some fl := by
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)]; exact f60
  have bF61 : b (fp + 61#64) = some 0#8 := by
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)]; exact f61
  have bF62 : b (fp + 62#64) = some 0#8 := by
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)]; exact f62
  have bF63 : b (fp + 63#64) = some 0#8 := by
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)]; exact f63
  obtain ⟨s3, e3, pc3, ax3, r153, bx3, sp3, bp3, r123, r143, fF, mem3, g58, g59, g60, g61, g62, g63⟩ :=
    post_avx self arr keyp fp len n ((len + 18446744073709551614#64) <<< 5) (merged k0 k1 l0 l1 r0 r1 fl).1 (merged k0 k1 l0 l1 r0 r1 fl).2 b
      rax2 rcx2 rdx2 rbp rsi2 rdi2 r82 r92 zf2 cf2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
      hfp hC0 hC1 b_own
      (fun fF v => over_write128 _ _ _ _ _ _ ownA1 oA1)
      (fun fF v w => over_write128 _ _ _ _ _ _ (owned16_put128 _ _ _ _ ownA0) oA0)
      (fun fF v w => by rw [over_read64 _ _ _ _ _ oLen]; exact read_quad (lenB v w))
      (fun fF v w x => over_write64 _ _ _ _ _ _ (quad_owned (lenB v w)) oLen)
  rw [over_none] at e3
  obtain ⟨SL1, hSL1, hL1⟩ :=
    pre_avx_leak self arr keyp fp len n l0 l1 r0 r1 k0 k1 fl m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      h1 h2 h3 h4 hfp rTag rL0 rL1 rR0 rR1 rK0 rK1 hOwn hPlat hFl hF0 hF1 hF2 hF3
  rw [over_none] at hSL1
  obtain ⟨SLk, hSLk, hLk⟩ := avxShows_spec (fp + 64#64) (fp + 128#64) (fp + 18446744073709551608#64) 262235#64 S1 k0 k1 l0 l1 r0 r1
    pc1 di1 si1 sp1 hc0 hc1 hb0 hb1 hb2 hb3 hret hapart
  obtain ⟨SL3, hSL3, hL3⟩ :=
    post_avx_leak self arr keyp fp len n ((len + 18446744073709551614#64) <<< 5) (merged k0 k1 l0 l1 r0 r1 fl).1 (merged k0 k1 l0 l1 r0 r1 fl).2 b
      rax2 rcx2 rdx2 rbp rsi2 rdi2 r82 r92 zf2 cf2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
      hfp hC0 hC1 b_own
      (fun fF v => over_write128 _ _ _ _ _ _ ownA1 oA1)
      (fun fF v w => over_write128 _ _ _ _ _ _ (owned16_put128 _ _ _ _ ownA0) oA0)
      (fun fF v w => by rw [over_read64 _ _ _ _ _ oLen]; exact read_quad (lenB v w))
      (fun fF v w x => over_write64 _ _ _ _ _ _ (quad_owned (lenB v w)) oLen)
  rw [over_none] at hSL3
  have c1 : SL1.core = S1 := core_of hSL1 e1
  have ck := core_of hSLk e2
  have hA := hSL1; rw [lstate_eq SL1 _ _ c1 hL1] at hA
  have hB := hSLk; rw [lstate_eq SLk _ _ ck hLk] at hB
  have hBC := stepsL_chain Code.prog 362 12 _ _ _ SL3 hB hSL3
  have hABC := stepsL_chain Code.prog 52 (362 + 12) _ _ _ _ hA hBC
  exact ⟨_, hABC, by simp only [turn_avx_shows, hL3, List.append_assoc]⟩

/-- What one turn by the SSE4.1 kernel shows: its last part, the kernel, its first part. -/
noncomputable def turn_sse_shows (self arr keyp fp len : BitVec 64) (last : Bool) : List Obs :=
  post_sse_shows self arr fp ((len + 18446744073709551614#64) <<< 5) last ++
    (sseShows (fp + 64#64) (fp + 128#64) (fp + 18446744073709551608#64) 262566#64 ++ pre_sse_shows self arr keyp fp len)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem turn_sse_leak (self arr keyp fp len n : BitVec 64) (l0 l1 r0 r1 k0 k1 : V) (fl : BitVec 8) (m : Mem)
    (rcx rdx rbp rsi rdi r8 r9 r13 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V)
    (hlo : 2#64 ≤ len) (hhi : len ≤ 55#64) (hfp : fp &&& 63#64 = 0#64)
    (hTag : m (self + 8#64) = some 1#8) (hLen : Quad m (self + 0#64) len)
    (hL0 : Vec m (arr + ((len + 18446744073709551614#64) <<< 5) + 0#64) l0) (hL1 : Vec m (arr + ((len + 18446744073709551614#64) <<< 5) + 16#64) l1)
    (hR0 : Vec m (arr + ((len + 18446744073709551615#64) <<< 5) + 0#64) r0) (hR1 : Vec m (arr + ((len + 18446744073709551615#64) <<< 5) + 16#64) r1)
    (hK0 : Vec m (keyp + 0#64) k0) (hK1 : Vec m (keyp + 16#64) k1)
    (hOwn : ∀ d : BitVec 64, inF d = true → (m (fp + d)).isSome = true)
    (plat : BitVec 8) (h5 : plat ≠ 5#8) (hPlat : m (fp + 58#64) = some plat) (hFl : m (fp + 59#64) = some fl)
    (hF0 : m (fp + 60#64) = some fl) (hF1 : m (fp + 61#64) = some 0#8) (hF2 : m (fp + 62#64) = some 0#8) (hF3 : m (fp + 63#64) = some 0#8)
    -- the stack's two slots, the key, and the stack's length and tag are not in `merge`'s frame
    (oSlot : ∀ x : BitVec 64, (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat < 64 → inF (x - fp) = false)
    (oKey : ∀ x : BitVec 64, (x - keyp).toNat < 32 → inF (x - fp) = false)
    (oSelf : ∀ x : BitVec 64, (x - self).toNat < 9 → inF (x - fp) = false)
    -- the length is not in the lower slot
    (hLS : ∀ x : BitVec 64, (x - self).toNat < 8 → 32 ≤ (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat) :
    ∃ S, stepsL Code.prog (52 + (467 + 13)) ⟨⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m, 0x40094⟩, []⟩ = some S ∧
      S.leak = turn_sse_shows self arr keyp fp len (decide (n - 1#64 = 0#64)) := by
  -- the checks' flags, from the bounds
  have h1 : len.ult 1#64 = false := by bv_decide
  have h2 : (len - 1#64 == 0#64) = false := by bv_decide
  have h3 : (len + 18446744073709551614#64).ult 55#64 = true := by bv_decide
  have h4 : len.ult 56#64 = true := by bv_decide
  have eR : arr + ((len + 18446744073709551615#64) <<< 5) = arr + ((len + 18446744073709551614#64) <<< 5) + 32#64 := by bv_decide
  have eA : ((len + 18446744073709551614#64) <<< 5) + arr = arr + ((len + 18446744073709551614#64) <<< 5) := by bv_decide
  -- what the first part needs: reads outside the frame are reads of `m`
  have blk : ∀ (c : BitVec 64), c.toNat ≤ 48 → ∀ x : BitVec 64, (x - (arr + ((len + 18446744073709551614#64) <<< 5) + c)).toNat < 16 → inF (x - fp) = false := by
    intro c hc x hx; exact oSlot x (by bv_omega)
  have rTag : ∀ fF, (over m fp inF fF).read (self + 8#64) 8 = some 1#64 := by
    intro fF; rw [over_read8 _ _ _ _ _ (oSelf _ (by bv_omega))]; simp [Mem.read, Mem.read8, hTag]
  have rL0 : ∀ fF, (over m fp inF fF).read128 (arr + ((len + 18446744073709551614#64) <<< 5) + 0#64) = some l0 := by
    intro fF; rw [over_read128 _ _ _ _ _ (blk 0#64 (by decide)), read_vec hL0]
  have rL1 : ∀ fF, (over m fp inF fF).read128 (arr + ((len + 18446744073709551614#64) <<< 5) + 16#64) = some l1 := by
    intro fF; rw [over_read128 _ _ _ _ _ (blk 16#64 (by decide)), read_vec hL1]
  have rR0 : ∀ fF, (over m fp inF fF).read128 (arr + ((len + 18446744073709551615#64) <<< 5) + 0#64) = some r0 := by
    intro fF; rw [over_read128 _ _ _ _ _ (by rw [eR]; intro x hx; exact oSlot x (by bv_omega)), read_vec hR0]
  have rR1 : ∀ fF, (over m fp inF fF).read128 (arr + ((len + 18446744073709551615#64) <<< 5) + 16#64) = some r1 := by
    intro fF; rw [over_read128 _ _ _ _ _ (by rw [eR]; intro x hx; exact oSlot x (by bv_omega)), read_vec hR1]
  have rK0 : ∀ fF, (over m fp inF fF).read128 (keyp + 0#64) = some k0 := by
    intro fF; rw [over_read128 _ _ _ _ _ (fun x hx => oKey x (by bv_omega)), read_vec hK0]
  have rK1 : ∀ fF, (over m fp inF fF).read128 (keyp + 16#64) = some k1 := by
    intro fF; rw [over_read128 _ _ _ _ _ (fun x hx => oKey x (by bv_omega)), read_vec hK1]
  obtain ⟨S1, e1, pc1, di1, si1, dx1, cx1, r81, sp1, bx1, bp1, c12, c13, c14, c15, vK0, vK1, vL0, vL1, vR0, vR1, hret1, own1, out1,
      f58, f59, f60, f61, f62, f63⟩ :=
    pre_sse self arr keyp fp len n l0 l1 r0 r1 k0 k1 fl m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      h1 h2 h3 h4 hfp rTag rL0 rL1 rR0 rR1 rK0 rK1 hOwn plat (by bv_decide) hPlat hFl hF0 hF1 hF2 hF3
  rw [over_none] at e1
  -- the kernel, by its contract
  have hc0 : Vec S1.mem (S1.rdi + 0) k0 := by rw [di1, show fp + 64#64 + 0 = fp + 64#64 by bv_decide]; exact vK0
  have hc1 : Vec S1.mem (S1.rdi + 16) k1 := by rw [di1, show fp + 64#64 + 16 = fp + 80#64 by bv_decide]; exact vK1
  have hb0 : Vec S1.mem (S1.rsi + 0) l0 := by rw [si1, show fp + 128#64 + 0 = fp + 128#64 by bv_decide]; exact vL0
  have hb1 : Vec S1.mem (S1.rsi + 16) l1 := by rw [si1, show fp + 128#64 + 16 = fp + 144#64 by bv_decide]; exact vL1
  have hb2 : Vec S1.mem (S1.rsi + 32) r0 := by rw [si1, show fp + 128#64 + 32 = fp + 160#64 by bv_decide]; exact vR0
  have hb3 : Vec S1.mem (S1.rsi + 48) r1 := by rw [si1, show fp + 128#64 + 48 = fp + 176#64 by bv_decide]; exact vR1
  have hret : S1.mem.read S1.rsp 64 = some 262566#64 := by rw [sp1]; exact hret1
  have hapart : ∀ x, (x - S1.rsp).toNat < 8 → 32 ≤ (x - S1.rdi).toNat := by rw [sp1, di1]; intro x hx; bv_omega
  obtain ⟨s2, e2, pc2, sp2, mem2, bx2, bp2, d12, d13, d14, d15⟩ := Sse.contract k0 k1 l0 l1 r0 r1 64#32 262566#64 S1 pc1 hc0 hc1 hb0 hb1 hb2 hb3 (by rw [dx1]; rfl) hret hapart
  have pc2' : s2.pc = 0x401A6 := pc2
  have sp2' : s2.rsp = fp := by rw [sp2, sp1]; bv_decide
  have mem2' : s2.mem = (S1.mem.put128 (fp + 64#64) (merged k0 k1 l0 l1 r0 r1 fl).1).put128 (fp + 80#64) (merged k0 k1 l0 l1 r0 r1 fl).2 := by
    have e8 : (BitVec.setWidth 32 (BitVec.setWidth 64 fl)) = BitVec.setWidth 32 fl := by bv_decide
    rw [cx1, r81, e8] at mem2
    rw [mem2, di1, show fp + 64#64 + 0 = fp + 64#64 by bv_decide, show fp + 64#64 + 16 = fp + 80#64 by bv_decide]
    rfl
  -- the last part, on the kernel's memory
  obtain ⟨rax2, rcx2, rdx2, rbx2, rsp2, rbp2, rsi2, rdi2, r82, r92, r122, r132, r142, r152, zf2, cf2,
    y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, b, pcv⟩ := s2
  simp only at pc2' sp2' mem2' bx2 bp2 d12 d13 d14 d15
  rw [bx1] at bx2; rw [bp1] at bp2; rw [c12] at d12; rw [c13] at d13; rw [c14] at d14; rw [c15] at d15
  subst pcv rsp2 rbx2 rbp2 r122 r132 r142 r152
  have b_out : ∀ x : BitVec 64, inF (x - fp) = false → b x = m x := by
    intro x hx
    have hx' : 392 ≤ (x - fp + 8#64).toNat := by simp only [inF, BitVec.ult] at hx; simpa using hx
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega), out1 x hx]
  have b_own : ∀ d : BitVec 64, inF d = true → (b (fp + d)).isSome = true := by
    intro d hd; rw [mem2']; exact put128_isSome _ _ _ _ (put128_isSome _ _ _ _ (own1 d hd))
  have hC0 : Vec b (fp + 64#64) (merged k0 k1 l0 l1 r0 r1 fl).1 := by
    rw [mem2']; exact vec_congr (fun x hx => by rw [put128_other _ _ _ x (by bv_omega)]) (vec_put128 _ _ _)
  have hC1 : Vec b (fp + 80#64) (merged k0 k1 l0 l1 r0 r1 fl).2 := by rw [mem2']; exact vec_put128 _ _ _
  have oA1 : ∀ x : BitVec 64, (x - (((len + 18446744073709551614#64) <<< 5) + arr + 16#64)).toNat < 16 → inF (x - fp) = false := by
    rw [eA]; exact blk 16#64 (by decide)
  have oA0 : ∀ x : BitVec 64, (x - (((len + 18446744073709551614#64) <<< 5) + arr + 0#64)).toNat < 16 → inF (x - fp) = false := by
    rw [eA]; exact blk 0#64 (by decide)
  have oLen : ∀ x : BitVec 64, (x - (self + 0#64)).toNat < 8 → inF (x - fp) = false := fun x hx => oSelf x (by bv_omega)
  have ownA1 : Owned16 b (((len + 18446744073709551614#64) <<< 5) + arr + 16#64) := by
    rw [eA]; exact owned16_congr (fun x hx => b_out x (blk 16#64 (by decide) x hx)) (vec_owned hL1)
  have ownA0 : Owned16 b (((len + 18446744073709551614#64) <<< 5) + arr + 0#64) := by
    rw [eA]; exact owned16_congr (fun x hx => b_out x (blk 0#64 (by decide) x hx)) (vec_owned hL0)
  have lenB : ∀ (v w : V), Quad ((b.put128 (((len + 18446744073709551614#64) <<< 5) + arr + 16#64) w).put128 (((len + 18446744073709551614#64) <<< 5) + arr + 0#64) v) (self + 0#64) len := by
    intro v w
    refine quad_congr (fun x hx => ?_) hLen
    have := hLS x (by bv_omega)
    rw [put128_other _ _ _ _ (by rw [eA]; bv_omega), put128_other _ _ _ _ (by rw [eA]; bv_omega), b_out x (oLen x hx)]
  have notLen : ∀ x : BitVec 64, (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat < 32 → 8 ≤ (x - (self + 0#64)).toNat := fun x hx =>
    Nat.le_of_not_lt (fun h => by have := hLS x (by bv_omega); omega)
  have frameNotLen : ∀ d : BitVec 64, inF d = true → 8 ≤ (fp + d - (self + 0#64)).toNat := fun d hd =>
    Nat.le_of_not_lt (fun h => by have := oSelf (fp + d) (by bv_omega); rw [add_sub_self] at this; simp [hd] at this)
  have frameNotSlot : ∀ d : BitVec 64, inF d = true →
      16 ≤ (fp + d - (((len + 18446744073709551614#64) <<< 5) + arr + 0#64)).toNat ∧ 16 ≤ (fp + d - (((len + 18446744073709551614#64) <<< 5) + arr + 16#64)).toNat := fun d hd =>
    ⟨Nat.le_of_not_lt (fun h => by have := oSlot (fp + d) (by rw [← eA]; bv_omega); rw [add_sub_self] at this; simp [hd] at this),
     Nat.le_of_not_lt (fun h => by have := oSlot (fp + d) (by rw [← eA]; bv_omega); rw [add_sub_self] at this; simp [hd] at this)⟩
  have bF58 : b (fp + 58#64) = some plat := by
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)]; exact f58
  have bF59 : b (fp + 59#64) = some fl := by
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)]; exact f59
  have bF60 : b (fp + 60#64) = some fl := by
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)]; exact f60
  have bF61 : b (fp + 61#64) = some 0#8 := by
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)]; exact f61
  have bF62 : b (fp + 62#64) = some 0#8 := by
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)]; exact f62
  have bF63 : b (fp + 63#64) = some 0#8 := by
    rw [mem2', put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)]; exact f63
  obtain ⟨s3, e3, pc3, ax3, r153, bx3, sp3, bp3, r123, r143, fF, mem3, g58, g59, g60, g61, g62, g63⟩ :=
    post_sse self arr keyp fp len n ((len + 18446744073709551614#64) <<< 5) (merged k0 k1 l0 l1 r0 r1 fl).1 (merged k0 k1 l0 l1 r0 r1 fl).2 b
      rax2 rcx2 rdx2 rbp rsi2 rdi2 r82 r92 zf2 cf2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
      hfp hC0 hC1 b_own
      (fun fF v => over_write128 _ _ _ _ _ _ ownA1 oA1)
      (fun fF v w => over_write128 _ _ _ _ _ _ (owned16_put128 _ _ _ _ ownA0) oA0)
      (fun fF v w => by rw [over_read64 _ _ _ _ _ oLen]; exact read_quad (lenB v w))
      (fun fF v w x => over_write64 _ _ _ _ _ _ (quad_owned (lenB v w)) oLen)
  rw [over_none] at e3
  obtain ⟨SL1, hSL1, hL1⟩ :=
    pre_sse_leak self arr keyp fp len n l0 l1 r0 r1 k0 k1 fl m rcx rdx rbp rsi rdi r8 r9 r13 zf cf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      h1 h2 h3 h4 hfp rTag rL0 rL1 rR0 rR1 rK0 rK1 hOwn plat (by bv_decide) hPlat hFl hF0 hF1 hF2 hF3
  rw [over_none] at hSL1
  obtain ⟨SLk, hSLk, hLk⟩ := sseShows_spec (fp + 64#64) (fp + 128#64) (fp + 18446744073709551608#64) 262566#64 S1 k0 k1 l0 l1 r0 r1
    pc1 di1 si1 sp1 hc0 hc1 hb0 hb1 hb2 hb3 hret hapart
  obtain ⟨SL3, hSL3, hL3⟩ :=
    post_sse_leak self arr keyp fp len n ((len + 18446744073709551614#64) <<< 5) (merged k0 k1 l0 l1 r0 r1 fl).1 (merged k0 k1 l0 l1 r0 r1 fl).2 b
      rax2 rcx2 rdx2 rbp rsi2 rdi2 r82 r92 zf2 cf2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
      hfp hC0 hC1 b_own
      (fun fF v => over_write128 _ _ _ _ _ _ ownA1 oA1)
      (fun fF v w => over_write128 _ _ _ _ _ _ (owned16_put128 _ _ _ _ ownA0) oA0)
      (fun fF v w => by rw [over_read64 _ _ _ _ _ oLen]; exact read_quad (lenB v w))
      (fun fF v w x => over_write64 _ _ _ _ _ _ (quad_owned (lenB v w)) oLen)
  rw [over_none] at hSL3
  have c1 : SL1.core = S1 := core_of hSL1 e1
  have ck := core_of hSLk e2
  have hA := hSL1; rw [lstate_eq SL1 _ _ c1 hL1] at hA
  have hB := hSLk; rw [lstate_eq SLk _ _ ck hLk] at hB
  have hBC := stepsL_chain Code.prog 467 13 _ _ _ SL3 hB hSL3
  have hABC := stepsL_chain Code.prog 52 (467 + 13) _ _ _ _ hA hBC
  exact ⟨_, hABC, by simp only [turn_sse_shows, hL3, List.append_assoc]⟩

end MergeCode
