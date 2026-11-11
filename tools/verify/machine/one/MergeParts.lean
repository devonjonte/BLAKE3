import MergeWhole
import Leak
open X86

namespace MergeCode

/-! What each part of `merge` shows an observer. Written by leakgen.py from the proved parts. -/

set_option maxRecDepth 100000 in
/-- `run_merge`, with the observer. -/
macro "run_merge_leak" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) (disch := decide) only [stepsL_mk, stepsL_zero, stepL, touched, srcObs, opObs, branches,
    List.nil_append, List.cons_append, List.append_nil,
    steps_mk, steps_zero, step, src,
    X86.read, write, State.get, State.set, State.xmm, State.setx, trunc, merge_at,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp, Option.isSome_some,
    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq,
    Mem.read8, Mem.write8, upd_apply, none_apply, Option.some_or, Option.none_or,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceEq,
    BitVec.reduceBEq, BitVec.reduceULT, BitVec.reduceSetWidth, BitVec.reduceShiftLeft, BitVec.reduceHShiftLeft, BitVec.xor_self,
    BitVec.or_zero, BitVec.zero_or,
    Nat.reduceAdd, Nat.reduceMul, Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, Bool.or_false, Bool.false_or,
    Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_self,
    zmask8, zmask8', byte_zext, cat_by8, unbyte64, BitVec.reduceNeg, Option.isSome_or, Bool.true_or, Bool.or_true, and_self, and_true, $hs,*])

/-- What this part shows. -/
def pre_avx_shows (self arr keyp fp len : BitVec 64) : List Obs :=
  [Obs.pc 196608, Obs.addr (fp + 18446744073709551608#64), Obs.addr (fp + 60#64), Obs.pc 262224, Obs.addr (fp + 64#64), Obs.addr (fp + 80#64), Obs.addr (keyp + 16#64), Obs.addr (keyp + 0#64), Obs.addr (fp + 241#64), Obs.addr (fp + 58#64), Obs.addr (fp + 240#64), Obs.addr (fp + 59#64), Obs.addr (fp + 232#64), Obs.addr (fp + 224#64), Obs.addr (fp + 208#64), Obs.addr (fp + 192#64), Obs.addr (keyp + 16#64), Obs.addr (keyp + 0#64), Obs.addr (fp + 128#64), Obs.addr (fp + 144#64), Obs.addr (fp + 160#64), Obs.addr (fp + 176#64), Obs.addr (fp + 112#64), Obs.addr (fp + 96#64), Obs.addr (fp + 80#64), Obs.addr (fp + 64#64), Obs.addr (fp + 96#64), Obs.addr (fp + 112#64), Obs.addr (arr + (len + 18446744073709551615#64) <<< 5 + 16#64), Obs.addr (arr + (len + 18446744073709551615#64) <<< 5 + 0#64), Obs.addr (fp + 64#64), Obs.addr (fp + 80#64), Obs.addr (arr + (len + 18446744073709551614#64) <<< 5 + 16#64), Obs.addr (arr + (len + 18446744073709551614#64) <<< 5 + 0#64), Obs.pc 262336, Obs.pc 262322, Obs.pc 262308, Obs.addr (self + 8#64), Obs.pc 262302]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pre_avx_leak (self arr keyp fp len n : BitVec 64) (l0 l1 r0 r1 k0 k1 : V) (fl : BitVec 8) (m : Mem)
    (rcx rdx rbp rsi rdi r8 r9 r13 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V)
    (h1 : len.ult 1#64 = false) (h2 : (len - 1#64 == 0#64) = false)
    (h3 : (len + 18446744073709551614#64).ult 55#64 = true) (h4 : len.ult 56#64 = true)
    (hfp : fp &&& 63#64 = 0#64)
    (hTag : ∀ fF, (over m fp inF fF).read (self + 8#64) 8 = some 1#64)
    (hL0 : ∀ fF, (over m fp inF fF).read128 (arr + (len + 18446744073709551614#64) <<< 5 + 0#64) = some l0)
    (hL1 : ∀ fF, (over m fp inF fF).read128 (arr + (len + 18446744073709551614#64) <<< 5 + 16#64) = some l1)
    (hR0 : ∀ fF, (over m fp inF fF).read128 (arr + (len + 18446744073709551615#64) <<< 5 + 0#64) = some r0)
    (hR1 : ∀ fF, (over m fp inF fF).read128 (arr + (len + 18446744073709551615#64) <<< 5 + 16#64) = some r1)
    (hK0 : ∀ fF, (over m fp inF fF).read128 (keyp + 0#64) = some k0)
    (hK1 : ∀ fF, (over m fp inF fF).read128 (keyp + 16#64) = some k1)
    (hOwn : ∀ d : BitVec 64, inF d = true → (m (fp + d)).isSome = true)
    (hPlat : m (fp + 58#64) = some 5#8) (hFl : m (fp + 59#64) = some fl)
    (hF0 : m (fp + 60#64) = some fl) (hF1 : m (fp + 61#64) = some 0#8) (hF2 : m (fp + 62#64) = some 0#8) (hF3 : m (fp + 63#64) = some 0#8) :
    ∃ S, stepsL Code.prog 52 ⟨⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, over m fp inF none', 0x40094⟩, []⟩ = some S ∧ S.leak = pre_avx_shows self arr keyp fp len := by
  let mm (fF : Written) : Mem := over m fp inF fF
  have wF : ∀ (fF : Written) (d : BitVec 64) (v : BitVec 8), inF d = true → (mm fF).put8 (fp + d) v = mm (upd fF d v) := by
    intro fF d v hd; simp only [mm]; rw [put8_over_in _ _ _ _ _ _ hd]
  have rF : ∀ (fF : Written) (d : BitVec 64), inF d = true → mm fF (fp + d) = (fF d).or (m (fp + d)) := by
    intro fF d hd; simp only [mm]; rw [over_in _ _ _ _ _ hd]
  have fp_add : ∀ c d : BitVec 64, fp + c + d = fp + (c + d) := by intro c d; bv_decide
  have alF : ∀ c : BitVec 64, (c &&& 15#64 == 0#64) = true → aligned16 (fp + c) = true := by
    intro c hc; simp only [aligned16]; bv_decide
  have rd128F := fun (fF : Written) (c : BitVec 64) => Mem.read128.eq_1 (mm fF) (fp + c)
  have wr128F := fun (fF : Written) (c : BitVec 64) (v : V) => Mem.write128.eq_1 (mm fF) (fp + c) v
  have fp_sub : ∀ c : BitVec 64, fp - c = fp + (-c) := by intro c; bv_decide
  have rdF64 : ∀ (fF : Written) (c : BitVec 64), (mm fF).read (fp + c) 64 = (do
      let b0 ← (mm fF).read8 (fp + c); let b1 ← (mm fF).read8 (fp + c + 1); let b2 ← (mm fF).read8 (fp + c + 2); let b3 ← (mm fF).read8 (fp + c + 3)
      let b4 ← (mm fF).read8 (fp + c + 4); let b5 ← (mm fF).read8 (fp + c + 5); let b6 ← (mm fF).read8 (fp + c + 6); let b7 ← (mm fF).read8 (fp + c + 7)
      pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56))) := fun _ _ => rfl
  have rdF8 : ∀ (fF : Written) (c : BitVec 64), (mm fF).read (fp + c) 8 = (mm fF).read8 (fp + c) := fun _ _ => rfl
  have rdF32 : ∀ (fF : Written) (c : BitVec 64), (mm fF).read (fp + c) 32 = (do
      let b0 ← (mm fF).read8 (fp + c); let b1 ← (mm fF).read8 (fp + c + 1); let b2 ← (mm fF).read8 (fp + c + 2); let b3 ← (mm fF).read8 (fp + c + 3)
      pure (b0 ||| b1 <<< 8 ||| b2 <<< 16 ||| b3 <<< 24)) := fun _ _ => rfl
  have wrF8 : ∀ (fF : Written) (c v : BitVec 64), (mm fF).write (fp + c) v 8 = (mm fF).write8 (fp + c) (byte v 0) := fun _ _ _ => rfl
  have wrF32 : ∀ (fF : Written) (c v : BitVec 64), (mm fF).write (fp + c) v 32 = (do
      let m ← (mm fF).write8 (fp + c) (byte v 0); let m ← m.write8 (fp + c + 1) (byte v 1)
      let m ← m.write8 (fp + c + 2) (byte v 2); m.write8 (fp + c + 3) (byte v 3)) := fun _ _ _ => rfl
  have wrF64 : ∀ (fF : Written) (c v : BitVec 64), (mm fF).write (fp + c) v 64 = (do
      let m ← (mm fF).write8 (fp + c) (byte v 0); let m ← m.write8 (fp + c + 1) (byte v 1)
      let m ← m.write8 (fp + c + 2) (byte v 2); let m ← m.write8 (fp + c + 3) (byte v 3)
      let m ← m.write8 (fp + c + 4) (byte v 4); let m ← m.write8 (fp + c + 5) (byte v 5)
      let m ← m.write8 (fp + c + 6) (byte v 6); m.write8 (fp + c + 7) (byte v 7)) := fun _ _ _ => rfl
  have hTag' : ∀ fF, (mm fF).read (self + 8#64) 8 = some 1#64 := hTag
  have hL0' : ∀ fF, (mm fF).read128 (arr + (len + 18446744073709551614#64) <<< 5 + 0#64) = some l0 := hL0
  have hL1' : ∀ fF, (mm fF).read128 (arr + (len + 18446744073709551614#64) <<< 5 + 16#64) = some l1 := hL1
  have hR0' : ∀ fF, (mm fF).read128 (arr + (len + 18446744073709551615#64) <<< 5 + 0#64) = some r0 := hR0
  have hR1' : ∀ fF, (mm fF).read128 (arr + (len + 18446744073709551615#64) <<< 5 + 16#64) = some r1 := hR1
  have hK0' : ∀ fF, (mm fF).read128 (keyp + 0#64) = some k0 := hK0
  have hK1' : ∀ fF, (mm fF).read128 (keyp + 16#64) = some k1 := hK1
  show ∃ S, stepsL Code.prog 52 ⟨⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mm none', 0x40094⟩, []⟩ = some S ∧ _
  run_merge_leak [wF, rF, fp_add, fp_sub, rdF64, alF, rd128F, wr128F, rdF8, rdF32, wrF8, wrF32, wrF64, h1, h2, h3, h4, hTag', hL0', hL1', hR0', hR1', hK0', hK1', hOwn, hPlat, hFl, hF0, hF1, hF2, hF3]
  refine ⟨_, rfl, ?_⟩
  simp only [pre_avx_shows]
  try rfl

/-- What this part shows. -/
def pre_sse_shows (self arr keyp fp len : BitVec 64) : List Obs :=
  [Obs.pc 131072, Obs.addr (fp + 18446744073709551608#64), Obs.addr (fp + 60#64), Obs.pc 262555, Obs.addr (fp + 64#64), Obs.addr (fp + 80#64), Obs.addr (keyp + 16#64), Obs.addr (keyp + 0#64), Obs.addr (fp + 241#64), Obs.addr (fp + 58#64), Obs.addr (fp + 240#64), Obs.addr (fp + 59#64), Obs.addr (fp + 232#64), Obs.addr (fp + 224#64), Obs.addr (fp + 208#64), Obs.addr (fp + 192#64), Obs.addr (keyp + 16#64), Obs.addr (keyp + 0#64), Obs.addr (fp + 128#64), Obs.addr (fp + 144#64), Obs.addr (fp + 160#64), Obs.addr (fp + 176#64), Obs.addr (fp + 112#64), Obs.addr (fp + 96#64), Obs.addr (fp + 80#64), Obs.addr (fp + 64#64), Obs.addr (fp + 96#64), Obs.addr (fp + 112#64), Obs.addr (arr + (len + 18446744073709551615#64) <<< 5 + 16#64), Obs.addr (arr + (len + 18446744073709551615#64) <<< 5 + 0#64), Obs.addr (fp + 64#64), Obs.addr (fp + 80#64), Obs.addr (arr + (len + 18446744073709551614#64) <<< 5 + 16#64), Obs.addr (arr + (len + 18446744073709551614#64) <<< 5 + 0#64), Obs.pc 262336, Obs.pc 262322, Obs.pc 262308, Obs.addr (self + 8#64), Obs.pc 262302]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pre_sse_leak (self arr keyp fp len n : BitVec 64) (l0 l1 r0 r1 k0 k1 : V) (fl : BitVec 8) (m : Mem)
    (rcx rdx rbp rsi rdi r8 r9 r13 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V)
    (h1 : len.ult 1#64 = false) (h2 : (len - 1#64 == 0#64) = false)
    (h3 : (len + 18446744073709551614#64).ult 55#64 = true) (h4 : len.ult 56#64 = true)
    (hfp : fp &&& 63#64 = 0#64)
    (hTag : ∀ fF, (over m fp inF fF).read (self + 8#64) 8 = some 1#64)
    (hL0 : ∀ fF, (over m fp inF fF).read128 (arr + (len + 18446744073709551614#64) <<< 5 + 0#64) = some l0)
    (hL1 : ∀ fF, (over m fp inF fF).read128 (arr + (len + 18446744073709551614#64) <<< 5 + 16#64) = some l1)
    (hR0 : ∀ fF, (over m fp inF fF).read128 (arr + (len + 18446744073709551615#64) <<< 5 + 0#64) = some r0)
    (hR1 : ∀ fF, (over m fp inF fF).read128 (arr + (len + 18446744073709551615#64) <<< 5 + 16#64) = some r1)
    (hK0 : ∀ fF, (over m fp inF fF).read128 (keyp + 0#64) = some k0)
    (hK1 : ∀ fF, (over m fp inF fF).read128 (keyp + 16#64) = some k1)
    (hOwn : ∀ d : BitVec 64, inF d = true → (m (fp + d)).isSome = true)
    (plat : BitVec 8) (h5 : (BitVec.setWidth 64 plat - 5#64 &&& 255#64 == 0#64) = false)
    (hPlat : m (fp + 58#64) = some plat) (hFl : m (fp + 59#64) = some fl)
    (hF0 : m (fp + 60#64) = some fl) (hF1 : m (fp + 61#64) = some 0#8) (hF2 : m (fp + 62#64) = some 0#8) (hF3 : m (fp + 63#64) = some 0#8) :
    ∃ S, stepsL Code.prog 52 ⟨⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, over m fp inF none', 0x40094⟩, []⟩ = some S ∧ S.leak = pre_sse_shows self arr keyp fp len := by
  let mm (fF : Written) : Mem := over m fp inF fF
  have wF : ∀ (fF : Written) (d : BitVec 64) (v : BitVec 8), inF d = true → (mm fF).put8 (fp + d) v = mm (upd fF d v) := by
    intro fF d v hd; simp only [mm]; rw [put8_over_in _ _ _ _ _ _ hd]
  have rF : ∀ (fF : Written) (d : BitVec 64), inF d = true → mm fF (fp + d) = (fF d).or (m (fp + d)) := by
    intro fF d hd; simp only [mm]; rw [over_in _ _ _ _ _ hd]
  have fp_add : ∀ c d : BitVec 64, fp + c + d = fp + (c + d) := by intro c d; bv_decide
  have alF : ∀ c : BitVec 64, (c &&& 15#64 == 0#64) = true → aligned16 (fp + c) = true := by
    intro c hc; simp only [aligned16]; bv_decide
  have rd128F := fun (fF : Written) (c : BitVec 64) => Mem.read128.eq_1 (mm fF) (fp + c)
  have wr128F := fun (fF : Written) (c : BitVec 64) (v : V) => Mem.write128.eq_1 (mm fF) (fp + c) v
  have fp_sub : ∀ c : BitVec 64, fp - c = fp + (-c) := by intro c; bv_decide
  have rdF64 : ∀ (fF : Written) (c : BitVec 64), (mm fF).read (fp + c) 64 = (do
      let b0 ← (mm fF).read8 (fp + c); let b1 ← (mm fF).read8 (fp + c + 1); let b2 ← (mm fF).read8 (fp + c + 2); let b3 ← (mm fF).read8 (fp + c + 3)
      let b4 ← (mm fF).read8 (fp + c + 4); let b5 ← (mm fF).read8 (fp + c + 5); let b6 ← (mm fF).read8 (fp + c + 6); let b7 ← (mm fF).read8 (fp + c + 7)
      pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56))) := fun _ _ => rfl
  have rdF8 : ∀ (fF : Written) (c : BitVec 64), (mm fF).read (fp + c) 8 = (mm fF).read8 (fp + c) := fun _ _ => rfl
  have rdF32 : ∀ (fF : Written) (c : BitVec 64), (mm fF).read (fp + c) 32 = (do
      let b0 ← (mm fF).read8 (fp + c); let b1 ← (mm fF).read8 (fp + c + 1); let b2 ← (mm fF).read8 (fp + c + 2); let b3 ← (mm fF).read8 (fp + c + 3)
      pure (b0 ||| b1 <<< 8 ||| b2 <<< 16 ||| b3 <<< 24)) := fun _ _ => rfl
  have wrF8 : ∀ (fF : Written) (c v : BitVec 64), (mm fF).write (fp + c) v 8 = (mm fF).write8 (fp + c) (byte v 0) := fun _ _ _ => rfl
  have wrF32 : ∀ (fF : Written) (c v : BitVec 64), (mm fF).write (fp + c) v 32 = (do
      let m ← (mm fF).write8 (fp + c) (byte v 0); let m ← m.write8 (fp + c + 1) (byte v 1)
      let m ← m.write8 (fp + c + 2) (byte v 2); m.write8 (fp + c + 3) (byte v 3)) := fun _ _ _ => rfl
  have wrF64 : ∀ (fF : Written) (c v : BitVec 64), (mm fF).write (fp + c) v 64 = (do
      let m ← (mm fF).write8 (fp + c) (byte v 0); let m ← m.write8 (fp + c + 1) (byte v 1)
      let m ← m.write8 (fp + c + 2) (byte v 2); let m ← m.write8 (fp + c + 3) (byte v 3)
      let m ← m.write8 (fp + c + 4) (byte v 4); let m ← m.write8 (fp + c + 5) (byte v 5)
      let m ← m.write8 (fp + c + 6) (byte v 6); m.write8 (fp + c + 7) (byte v 7)) := fun _ _ _ => rfl
  have hTag' : ∀ fF, (mm fF).read (self + 8#64) 8 = some 1#64 := hTag
  have hL0' : ∀ fF, (mm fF).read128 (arr + (len + 18446744073709551614#64) <<< 5 + 0#64) = some l0 := hL0
  have hL1' : ∀ fF, (mm fF).read128 (arr + (len + 18446744073709551614#64) <<< 5 + 16#64) = some l1 := hL1
  have hR0' : ∀ fF, (mm fF).read128 (arr + (len + 18446744073709551615#64) <<< 5 + 0#64) = some r0 := hR0
  have hR1' : ∀ fF, (mm fF).read128 (arr + (len + 18446744073709551615#64) <<< 5 + 16#64) = some r1 := hR1
  have hK0' : ∀ fF, (mm fF).read128 (keyp + 0#64) = some k0 := hK0
  have hK1' : ∀ fF, (mm fF).read128 (keyp + 16#64) = some k1 := hK1
  show ∃ S, stepsL Code.prog 52 ⟨⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mm none', 0x40094⟩, []⟩ = some S ∧ _
  run_merge_leak [wF, rF, fp_add, fp_sub, rdF64, alF, rd128F, wr128F, rdF8, rdF32, wrF8, wrF32, wrF64, h1, h2, h3, h4, h5, hTag', hL0', hL1', hR0', hR1', hK0', hK1', hOwn, hPlat, hFl, hF0, hF1, hF2, hF3]
  refine ⟨_, rfl, ?_⟩
  simp only [pre_sse_shows]
  try rfl

/-- What this part shows: `last` when no turn is left. -/
def post_avx_shows (self arr fp oL : BitVec 64) (last : Bool) : List Obs :=
  if last then [Obs.pc 262571, Obs.addr (self + 0#64), Obs.addr (self + 0#64), Obs.addr (oL + arr + 0#64), Obs.addr (oL + arr + 16#64), Obs.addr (fp + 288#64), Obs.addr (fp + 304#64), Obs.addr (fp + 80#64), Obs.addr (fp + 64#64)]
  else [Obs.pc 262292, Obs.addr (self + 0#64), Obs.addr (self + 0#64), Obs.addr (oL + arr + 0#64), Obs.addr (oL + arr + 16#64), Obs.addr (fp + 288#64), Obs.addr (fp + 304#64), Obs.addr (fp + 80#64), Obs.addr (fp + 64#64)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem post_avx_leak (self arr keyp fp len n oL : BitVec 64) (c0 c1 : V) (b : Mem)
    (rax rcx rdx rbp rsi rdi r8 r9 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V)
    (hfp : fp &&& 63#64 = 0#64)
    (hC0 : Vec b (fp + 64#64) c0) (hC1 : Vec b (fp + 80#64) c1)
    (hOwn : ∀ d : BitVec 64, inF d = true → (b (fp + d)).isSome = true)
    (wrA1 : ∀ (fF : Written) (v : V), (over b fp inF fF).write128 (oL + arr + 16#64) v = some (over (b.put128 (oL + arr + 16#64) v) fp inF fF))
    (wrA0 : ∀ (fF : Written) (v w : V), (over (b.put128 (oL + arr + 16#64) w) fp inF fF).write128 (oL + arr + 0#64) v =
      some (over ((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v) fp inF fF))
    (rdLen : ∀ (fF : Written) (v w : V), (over ((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v) fp inF fF).read (self + 0#64) 64 = some len)
    (wrLen : ∀ (fF : Written) (v w : V) (x : BitVec 64), (over ((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v) fp inF fF).write (self + 0#64) x 64 =
      some (over (((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v).put64 (self + 0#64) x) fp inF fF)) :
    ∃ S, stepsL Code.prog 12 ⟨⟨rax, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, oL, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, over b fp inF none', 0x4005B⟩, []⟩ = some S ∧ S.leak = post_avx_shows self arr fp oL (decide (n - 1#64 = 0#64)) := by
  let mm (B : Mem) (fF : Written) : Mem := over B fp inF fF
  have wF : ∀ (B : Mem) (fF : Written) (d : BitVec 64) (v : BitVec 8), inF d = true → (mm B fF).put8 (fp + d) v = mm B (upd fF d v) := by
    intro B fF d v hd; simp only [mm]; rw [put8_over_in _ _ _ _ _ _ hd]
  have rF : ∀ (B : Mem) (fF : Written) (d : BitVec 64), inF d = true → mm B fF (fp + d) = (fF d).or (B (fp + d)) := by
    intro B fF d hd; simp only [mm]; rw [over_in _ _ _ _ _ hd]
  have fp_add : ∀ c d : BitVec 64, fp + c + d = fp + (c + d) := by intro c d; bv_decide
  have alF : ∀ c : BitVec 64, (c &&& 15#64 == 0#64) = true → aligned16 (fp + c) = true := by
    intro c hc; simp only [aligned16]; bv_decide
  have rd128F := fun (B : Mem) (fF : Written) (c : BitVec 64) => Mem.read128.eq_1 (mm B fF) (fp + c)
  have wr128F := fun (B : Mem) (fF : Written) (c : BitVec 64) (v : V) => Mem.write128.eq_1 (mm B fF) (fp + c) v
  have wrA1' : ∀ (fF : Written) (v : V), (mm b fF).write128 (oL + arr + 16#64) v = some (mm (b.put128 (oL + arr + 16#64) v) fF) := wrA1
  have wrA0' : ∀ (fF : Written) (v w : V), (mm (b.put128 (oL + arr + 16#64) w) fF).write128 (oL + arr + 0#64) v = some (mm ((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v) fF) := wrA0
  have rdLen' : ∀ (fF : Written) (v w : V), (mm ((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v) fF).read (self + 0#64) 64 = some len := rdLen
  have wrLen' : ∀ (fF : Written) (v w : V) (x : BitVec 64), (mm ((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v) fF).write (self + 0#64) x 64 =
      some (mm (((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v).put64 (self + 0#64) x) fF) := wrLen
  have hc0 := hC0
  have hc1 := hC1
  simp only [Vec, fp_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at hc0 hc1
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := hc0
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩ := hc1
  show ∃ S, stepsL Code.prog 12 ⟨⟨rax, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, oL, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mm b none', 0x4005B⟩, []⟩ = some S ∧ _
  by_cases hz : n - 1#64 = 0#64
  · have hz' : (n - 1#64 == 0#64) = true := by simpa using hz
    run_merge_leak [wF, rF, fp_add, alF, rd128F, wr128F, wrA1', wrA0', rdLen', wrLen', hOwn, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, hz']
    refine ⟨_, rfl, ?_⟩
    simp only [post_avx_shows, hz, decide_true, decide_false, ↓reduceIte, if_true, if_false, Bool.false_eq_true]
    try rfl
  · have hz' : (n - 1#64 == 0#64) = false := by simpa using hz
    run_merge_leak [wF, rF, fp_add, alF, rd128F, wr128F, wrA1', wrA0', rdLen', wrLen', hOwn, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, hz']
    refine ⟨_, rfl, ?_⟩
    simp only [post_avx_shows, hz, decide_true, decide_false, ↓reduceIte, if_true, if_false, Bool.false_eq_true]
    try rfl

/-- What this part shows: `last` when no turn is left. -/
def post_sse_shows (self arr fp oL : BitVec 64) (last : Bool) : List Obs :=
  if last then [Obs.pc 262571, Obs.addr (self + 0#64), Obs.addr (self + 0#64), Obs.addr (oL + arr + 0#64), Obs.addr (oL + arr + 16#64), Obs.addr (fp + 288#64), Obs.addr (fp + 304#64), Obs.addr (fp + 80#64), Obs.addr (fp + 64#64), Obs.pc 262235]
  else [Obs.pc 262292, Obs.addr (self + 0#64), Obs.addr (self + 0#64), Obs.addr (oL + arr + 0#64), Obs.addr (oL + arr + 16#64), Obs.addr (fp + 288#64), Obs.addr (fp + 304#64), Obs.addr (fp + 80#64), Obs.addr (fp + 64#64), Obs.pc 262235]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem post_sse_leak (self arr keyp fp len n oL : BitVec 64) (c0 c1 : V) (b : Mem)
    (rax rcx rdx rbp rsi rdi r8 r9 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V)
    (hfp : fp &&& 63#64 = 0#64)
    (hC0 : Vec b (fp + 64#64) c0) (hC1 : Vec b (fp + 80#64) c1)
    (hOwn : ∀ d : BitVec 64, inF d = true → (b (fp + d)).isSome = true)
    (wrA1 : ∀ (fF : Written) (v : V), (over b fp inF fF).write128 (oL + arr + 16#64) v = some (over (b.put128 (oL + arr + 16#64) v) fp inF fF))
    (wrA0 : ∀ (fF : Written) (v w : V), (over (b.put128 (oL + arr + 16#64) w) fp inF fF).write128 (oL + arr + 0#64) v =
      some (over ((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v) fp inF fF))
    (rdLen : ∀ (fF : Written) (v w : V), (over ((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v) fp inF fF).read (self + 0#64) 64 = some len)
    (wrLen : ∀ (fF : Written) (v w : V) (x : BitVec 64), (over ((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v) fp inF fF).write (self + 0#64) x 64 =
      some (over (((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v).put64 (self + 0#64) x) fp inF fF)) :
    ∃ S, stepsL Code.prog 13 ⟨⟨rax, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, oL, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, over b fp inF none', 0x401A6⟩, []⟩ = some S ∧ S.leak = post_sse_shows self arr fp oL (decide (n - 1#64 = 0#64)) := by
  let mm (B : Mem) (fF : Written) : Mem := over B fp inF fF
  have wF : ∀ (B : Mem) (fF : Written) (d : BitVec 64) (v : BitVec 8), inF d = true → (mm B fF).put8 (fp + d) v = mm B (upd fF d v) := by
    intro B fF d v hd; simp only [mm]; rw [put8_over_in _ _ _ _ _ _ hd]
  have rF : ∀ (B : Mem) (fF : Written) (d : BitVec 64), inF d = true → mm B fF (fp + d) = (fF d).or (B (fp + d)) := by
    intro B fF d hd; simp only [mm]; rw [over_in _ _ _ _ _ hd]
  have fp_add : ∀ c d : BitVec 64, fp + c + d = fp + (c + d) := by intro c d; bv_decide
  have alF : ∀ c : BitVec 64, (c &&& 15#64 == 0#64) = true → aligned16 (fp + c) = true := by
    intro c hc; simp only [aligned16]; bv_decide
  have rd128F := fun (B : Mem) (fF : Written) (c : BitVec 64) => Mem.read128.eq_1 (mm B fF) (fp + c)
  have wr128F := fun (B : Mem) (fF : Written) (c : BitVec 64) (v : V) => Mem.write128.eq_1 (mm B fF) (fp + c) v
  have wrA1' : ∀ (fF : Written) (v : V), (mm b fF).write128 (oL + arr + 16#64) v = some (mm (b.put128 (oL + arr + 16#64) v) fF) := wrA1
  have wrA0' : ∀ (fF : Written) (v w : V), (mm (b.put128 (oL + arr + 16#64) w) fF).write128 (oL + arr + 0#64) v = some (mm ((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v) fF) := wrA0
  have rdLen' : ∀ (fF : Written) (v w : V), (mm ((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v) fF).read (self + 0#64) 64 = some len := rdLen
  have wrLen' : ∀ (fF : Written) (v w : V) (x : BitVec 64), (mm ((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v) fF).write (self + 0#64) x 64 =
      some (mm (((b.put128 (oL + arr + 16#64) w).put128 (oL + arr + 0#64) v).put64 (self + 0#64) x) fF) := wrLen
  have hc0 := hC0
  have hc1 := hC1
  simp only [Vec, fp_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at hc0 hc1
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := hc0
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩ := hc1
  show ∃ S, stepsL Code.prog 13 ⟨⟨rax, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, oL, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mm b none', 0x401A6⟩, []⟩ = some S ∧ _
  by_cases hz : n - 1#64 = 0#64
  · have hz' : (n - 1#64 == 0#64) = true := by simpa using hz
    run_merge_leak [wF, rF, fp_add, alF, rd128F, wr128F, wrA1', wrA0', rdLen', wrLen', hOwn, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, hz']
    refine ⟨_, rfl, ?_⟩
    simp only [post_sse_shows, hz, decide_true, decide_false, ↓reduceIte, if_true, if_false, Bool.false_eq_true]
    try rfl
  · have hz' : (n - 1#64 == 0#64) = false := by simpa using hz
    run_merge_leak [wF, rF, fp_add, alF, rd128F, wr128F, wrA1', wrA0', rdLen', wrLen', hOwn, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, hz']
    refine ⟨_, rfl, ?_⟩
    simp only [post_sse_shows, hz, decide_true, decide_false, ↓reduceIte, if_true, if_false, Bool.false_eq_true]
    try rfl

/-- What this part shows. -/
def prologue_shows (self p rsp0 fp : BitVec 64) : List Obs :=
  [Obs.pc 262292, Obs.addr (fp + 60#64), Obs.addr (fp + 59#64), Obs.addr (fp + 58#64), Obs.addr (p + 41#64), Obs.addr (p + 40#64), Obs.addr (p + 0#64), Obs.pc 262183, Obs.addr (self + 0#64), Obs.addr (rsp0 + 18446744073709551568#64), Obs.addr (rsp0 + 18446744073709551576#64), Obs.addr (rsp0 + 18446744073709551584#64), Obs.addr (rsp0 + 18446744073709551592#64), Obs.addr (rsp0 + 18446744073709551600#64), Obs.addr (rsp0 + 18446744073709551608#64)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem prologue_leak (self p keyp rsp0 fp len target : BitVec 64) (flags plat : BitVec 8) (m : Mem)
    (rax rcx rbx rbp r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V)
    (hfp : ((rsp0 + 18446744073709551568#64) &&& 18446744073709551552#64) - 384#64 = fp)
    (hsp : 1024#64 ≤ rsp0) (hsp2 : rsp0 ≤ 18446744073709551600#64)
    (hlt : target < len)
    (hLen : Quad m (self + 0#64) len) (hKeyp : Quad m (p + 0#64) keyp)
    (hFlags : m (p + 40#64) = some flags) (hPlat : m (p + 41#64) = some plat)
    (hOwnP : ∀ d : BitVec 64, inP d = true → (m (rsp0 + d)).isSome = true)
    (hOwnF : ∀ d : BitVec 64, inF d = true → (m (fp + d)).isSome = true)
    -- the `CvStack`'s length and the kernels' structure are in neither the frame nor the pushed bytes
    (gLen : ∀ x : BitVec 64, (x - (self + 0#64)).toNat < 8 → inF (x - fp) = false ∧ inP (x - rsp0) = false)
    (gP : ∀ x : BitVec 64, (x - p).toNat < 42 → inF (x - fp) = false ∧ inP (x - rsp0) = false)
    (ra : BitVec 64) (hRa : m.read (rsp0 + 0#64) 64 = some ra) :
    ∃ S, stepsL Code.prog 24 ⟨⟨rax, rcx, target, rbx, rsp0, rbp, p, self, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m, 0x40000⟩, []⟩ = some S ∧ S.leak = prologue_shows self p rsp0 fp := by
  let mm (fP fF : Written) : Mem := over (over m rsp0 inP fP) fp inF fF
  have hm : m = mm none' none' := by simp only [mm, over_none]
  have pNotF : ∀ d : BitVec 64, inP d = true → inF (rsp0 + d - fp) = false := by
    intro d hd; simp only [inP, inF] at hd ⊢; bv_decide
  have fNotP : ∀ d : BitVec 64, inF d = true → inP (fp + d - rsp0) = false := by
    intro d hd; simp only [inP, inF] at hd ⊢; bv_decide
  have wP : ∀ (fP fF : Written) (d : BitVec 64) (v : BitVec 8), inP d = true → (mm fP fF).put8 (rsp0 + d) v = mm (upd fP d v) fF := by
    intro fP fF d v hd; simp only [mm]; rw [put8_over_out _ _ _ _ _ _ (pNotF d hd), put8_over_in _ _ _ _ _ _ hd]
  have rP : ∀ (fP fF : Written) (d : BitVec 64), inP d = true → mm fP fF (rsp0 + d) = (fP d).or (m (rsp0 + d)) := by
    intro fP fF d hd; simp only [mm]; rw [over_out _ _ _ _ _ (pNotF d hd), over_in _ _ _ _ _ hd]
  have wF : ∀ (fP fF : Written) (d : BitVec 64) (v : BitVec 8), inF d = true → (mm fP fF).put8 (fp + d) v = mm fP (upd fF d v) := by
    intro fP fF d v hd; simp only [mm]; rw [put8_over_in _ _ _ _ _ _ hd]
  have rF : ∀ (fP fF : Written) (d : BitVec 64), inF d = true → mm fP fF (fp + d) = (fF d).or (m (fp + d)) := by
    intro fP fF d hd; simp only [mm]; rw [over_in _ _ _ _ _ hd, over_out _ _ _ _ _ (fNotP d hd)]
  have r_sub : ∀ c : BitVec 64, rsp0 - c = rsp0 + (-c) := by intro c; bv_decide
  have r_add : ∀ c d : BitVec 64, rsp0 + c + d = rsp0 + (c + d) := by intro c d; bv_decide
  have r_sub2 : ∀ c d : BitVec 64, rsp0 + c - d = rsp0 + (c - d) := by intro c d; bv_decide
  have fp_add : ∀ c d : BitVec 64, fp + c + d = fp + (c + d) := by intro c d; bv_decide
  have wrP64 : ∀ (fP fF : Written) (c v : BitVec 64), (mm fP fF).write (rsp0 + c) v 64 = (do
      let m ← (mm fP fF).write8 (rsp0 + c) (byte v 0); let m ← m.write8 (rsp0 + c + 1) (byte v 1)
      let m ← m.write8 (rsp0 + c + 2) (byte v 2); let m ← m.write8 (rsp0 + c + 3) (byte v 3)
      let m ← m.write8 (rsp0 + c + 4) (byte v 4); let m ← m.write8 (rsp0 + c + 5) (byte v 5)
      let m ← m.write8 (rsp0 + c + 6) (byte v 6); m.write8 (rsp0 + c + 7) (byte v 7)) := fun _ _ _ _ => rfl
  have rdP64 : ∀ (fP fF : Written) (c : BitVec 64), (mm fP fF).read (rsp0 + c) 64 = (do
      let b0 ← (mm fP fF).read8 (rsp0 + c); let b1 ← (mm fP fF).read8 (rsp0 + c + 1); let b2 ← (mm fP fF).read8 (rsp0 + c + 2); let b3 ← (mm fP fF).read8 (rsp0 + c + 3)
      let b4 ← (mm fP fF).read8 (rsp0 + c + 4); let b5 ← (mm fP fF).read8 (rsp0 + c + 5); let b6 ← (mm fP fF).read8 (rsp0 + c + 6); let b7 ← (mm fP fF).read8 (rsp0 + c + 7)
      pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56))) := fun _ _ _ => rfl
  have wrF8 : ∀ (fP fF : Written) (c v : BitVec 64), (mm fP fF).write (fp + c) v 8 = (mm fP fF).write8 (fp + c) (byte v 0) := fun _ _ _ _ => rfl
  have wrF32 : ∀ (fP fF : Written) (c v : BitVec 64), (mm fP fF).write (fp + c) v 32 = (do
      let m ← (mm fP fF).write8 (fp + c) (byte v 0); let m ← m.write8 (fp + c + 1) (byte v 1)
      let m ← m.write8 (fp + c + 2) (byte v 2); m.write8 (fp + c + 3) (byte v 3)) := fun _ _ _ _ => rfl
  have rdLen : ∀ (fP fF : Written), (mm fP fF).read (self + 0#64) 64 = some len := by
    intro fP fF; simp only [mm]
    rw [over_read64 _ _ _ _ _ (fun x hx => (gLen x hx).1), over_read64 _ _ _ _ _ (fun x hx => (gLen x hx).2), read_quad hLen]
  have rdKeyp : ∀ (fP fF : Written), (mm fP fF).read (p + 0#64) 64 = some keyp := by
    intro fP fF; simp only [mm]
    rw [over_read64 _ _ _ _ _ (fun x hx => (gP x (by bv_omega)).1), over_read64 _ _ _ _ _ (fun x hx => (gP x (by bv_omega)).2), read_quad hKeyp]
  have rdFlags : ∀ (fP fF : Written), (mm fP fF).read (p + 40#64) 8 = some (flags.setWidth 64) := by
    intro fP fF; simp only [mm]
    rw [over_read8 _ _ _ _ _ (gP _ (by bv_omega)).1, over_read8 _ _ _ _ _ (gP _ (by bv_omega)).2]; simp [Mem.read, Mem.read8, hFlags]
  have rdPlat : ∀ (fP fF : Written), (mm fP fF).read (p + 41#64) 8 = some (plat.setWidth 64) := by
    intro fP fF; simp only [mm]
    rw [over_read8 _ _ _ _ _ (gP _ (by bv_omega)).1, over_read8 _ _ _ _ _ (gP _ (by bv_omega)).2]; simp [Mem.read, Mem.read8, hPlat]
  have hc : len.ult target = false := by bv_decide
  have hz : (len - target == 0#64) = false := by bv_decide
  rw [hm]
  run_merge_leak [wP, rP, wF, rF, r_sub, r_sub2, r_add, fp_add, wrP64, wrF8, wrF32, rdLen, rdKeyp, rdFlags, rdPlat, hOwnP, hOwnF, hfp, hc, hz]
  refine ⟨_, rfl, ?_⟩
  simp only [prologue_shows]
  try rfl

/-- What this part shows. -/
def epilogue_shows (rsp0 ra : BitVec 64) : List Obs :=
  [Obs.pc ra.toNat, Obs.addr (rsp0 + 0#64), Obs.addr (rsp0 + 18446744073709551608#64), Obs.addr (rsp0 + 18446744073709551600#64), Obs.addr (rsp0 + 18446744073709551592#64), Obs.addr (rsp0 + 18446744073709551584#64), Obs.addr (rsp0 + 18446744073709551576#64), Obs.addr (rsp0 + 18446744073709551568#64)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem epilogue_leak (rsp0 : BitVec 64) (b : Mem) (v0 v12 v13 v14 v15 vbp ra : BitVec 64)
    (rax rcx rdx rbx rsp rsi rdi r8 r9 r12 r13 r14 r15 : BitVec 64) (zf cf : Option Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : V)
    (h48 : b.read (rsp0 + 18446744073709551568#64) 64 = some v0) (h40 : b.read (rsp0 + 18446744073709551576#64) 64 = some v12)
    (h32 : b.read (rsp0 + 18446744073709551584#64) 64 = some v13) (h24 : b.read (rsp0 + 18446744073709551592#64) 64 = some v14)
    (h16 : b.read (rsp0 + 18446744073709551600#64) 64 = some v15) (h8 : b.read (rsp0 + 18446744073709551608#64) 64 = some vbp)
    (hra : b.read (rsp0 + 0#64) 64 = some ra) :
    ∃ S, stepsL Code.prog 8 ⟨⟨rax, rcx, rdx, rbx, rsp, rsp0 + 18446744073709551608#64, rsi, rdi, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, b, 0x401AB⟩, []⟩ = some S ∧ S.leak = epilogue_shows rsp0 ra := by
  have r_add : ∀ c d : BitVec 64, rsp0 + c + d = rsp0 + (c + d) := by intro c d; bv_decide
  run_merge_leak [r_add, h48, h40, h32, h24, h16, h8, hra]
  refine ⟨_, rfl, ?_⟩
  simp only [epilogue_shows]
  try rfl

end MergeCode
