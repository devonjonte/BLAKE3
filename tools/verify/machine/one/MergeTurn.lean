import Machine
import MemLemmas
import Code
import RegionsX
import SseProof
import AvxProof
open X86

/-! # One turn of `CvStack::merge`'s loop, as compiled

`merge` (hasher.rs) is `for _ in target..len { cvs[len-2] = parent(cvs[len-2], cvs[len-1]); len -= 1 }`.
Its machine code (rustc 1.99.1, the two-crate trial) is 100 instructions with three panic sites and a
call to either one-block kernel. This file is about one turn of its loop. -/

/-- The frame `merge` makes: 0x180 bytes from its stack pointer, and the eight below it where a
call's return address goes. -/
def inF (d : BitVec 64) : Bool := (d + 8#64).ult 392#64

theorem zmask8 (b : BitVec 8) : b.setWidth 64 &&& 4294967295#64 = b.setWidth 64 := by bv_decide
theorem zmask8' (b : BitVec 8) : b.setWidth 64 &&& 255#64 = b.setWidth 64 := by bv_decide
theorem byte_zext (c : BitVec 8) : byte (c.setWidth 64) 0 = c := by simp only [byte]; bv_decide
/-- Sixteen bytes of a vector, put together again. -/
theorem cat_by8 (v : V) : by8 v 15 ++ by8 v 14 ++ by8 v 13 ++ by8 v 12 ++ by8 v 11 ++ by8 v 10 ++ by8 v 9 ++ by8 v 8 ++ by8 v 7 ++ by8 v 6 ++ by8 v 5 ++ by8 v 4 ++ by8 v 3 ++ by8 v 2 ++ by8 v 1 ++ by8 v 0 = v := by simp only [by8]; bv_decide

/-- Eight bytes written and read back are the value. -/
theorem unbyte64 (v : BitVec 64) : BitVec.setWidth 64 (byte v 0) ||| BitVec.setWidth 64 (byte v 1) <<< 8 ||| BitVec.setWidth 64 (byte v 2) <<< 16 ||| BitVec.setWidth 64 (byte v 3) <<< 24 ||| BitVec.setWidth 64 (byte v 4) <<< 32 ||| BitVec.setWidth 64 (byte v 5) <<< 40 ||| BitVec.setWidth 64 (byte v 6) <<< 48 ||| BitVec.setWidth 64 (byte v 7) <<< 56 = v := by
  simp only [byte]; bv_decide

/-- Run `merge`'s instructions on a state that is written out; its frame's bytes are kept by region. -/
macro "run_merge" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) (disch := decide) only [steps_mk, steps_zero, step, src,
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- From the loop's head to the call of the AVX-512 kernel: the checks pass, the two values on top of the
stack and the key are copied into a parent node in the frame, and the kernel is called on it. -/
theorem pre_avx (self arr keyp fp len n : BitVec 64) (l0 l1 r0 r1 k0 k1 : V) (fl : BitVec 8) (m : Mem)
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
    ∃ s', steps Code.prog 52 ⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, over m fp inF none', 0x40094⟩ = some s' ∧ s'.pc = 0x30000 ∧
      s'.rdi = fp + 64#64 ∧ s'.rsi = fp + 128#64 ∧ s'.rdx = 64#64 ∧ s'.rcx = 0#64 ∧ s'.r8 = fl.setWidth 64 ∧
      s'.rsp = fp + 18446744073709551608#64 ∧ s'.rbx = self ∧ s'.rbp = rbp ∧ s'.r12 = arr ∧
      s'.r13 = (len + 18446744073709551614#64) <<< 5 ∧ s'.r14 = keyp ∧ s'.r15 = n ∧
      Vec s'.mem (fp + 64#64) k0 ∧ Vec s'.mem (fp + 80#64) k1 ∧ Vec s'.mem (fp + 128#64) l0 ∧ Vec s'.mem (fp + 144#64) l1 ∧
      Vec s'.mem (fp + 160#64) r0 ∧ Vec s'.mem (fp + 176#64) r1 ∧
      s'.mem.read (fp + 18446744073709551608#64) 64 = some 262235#64 ∧
      (∀ d : BitVec 64, inF d = true → (s'.mem (fp + d)).isSome = true) ∧
      (∀ x : BitVec 64, inF (x - fp) = false → s'.mem x = m x) ∧
      s'.mem (fp + 58#64) = some 5#8 ∧ s'.mem (fp + 59#64) = some fl ∧ s'.mem (fp + 60#64) = some fl ∧
      s'.mem (fp + 61#64) = some 0#8 ∧ s'.mem (fp + 62#64) = some 0#8 ∧ s'.mem (fp + 63#64) = some 0#8 := by
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
  show ∃ s', steps Code.prog 52 ⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mm none', 0x40094⟩ = some s' ∧ _
  run_merge [wF, rF, fp_add, fp_sub, rdF64, alF, rd128F, wr128F, rdF8, rdF32, wrF8, wrF32, wrF64, h1, h2, h3, h4, hTag', hL0', hL1', hR0', hR1', hK0', hK1', hOwn, hPlat, hFl, hF0, hF1, hF2, hF3]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro x hx; show mm _ x = m x; simp only [mm]; rw [over_out _ _ _ _ _ hx]; done)
    | (intro d hd; simp (disch := assumption) only [rF, Option.isSome_or, hOwn, Bool.or_true]; done)
    | simp (config := {maxSteps := 10000000}) (disch := decide) only [Vec, fp_add, rdF64, Mem.read8, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, rF, upd_apply, none_apply,
        BitVec.reduceEq, ↓reduceIte, Option.some_or, Option.none_or, and_self, hPlat, hFl, hF0, hF1, hF2, hF3, unbyte64,
        Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 1000000 in
set_option pp.deepTerms true in
/-- From the loop's head to the call of the SSE4.1 kernel: the checks pass, the two values on top of the
stack and the key are copied into a parent node in the frame, and the kernel is called on it. -/
theorem pre_sse (self arr keyp fp len n : BitVec 64) (l0 l1 r0 r1 k0 k1 : V) (fl : BitVec 8) (m : Mem)
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
    ∃ s', steps Code.prog 52 ⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, over m fp inF none', 0x40094⟩ = some s' ∧ s'.pc = 0x20000 ∧
      s'.rdi = fp + 64#64 ∧ s'.rsi = fp + 128#64 ∧ s'.rdx = 64#64 ∧ s'.rcx = 0#64 ∧ s'.r8 = fl.setWidth 64 ∧
      s'.rsp = fp + 18446744073709551608#64 ∧ s'.rbx = self ∧ s'.rbp = rbp ∧ s'.r12 = arr ∧
      s'.r13 = (len + 18446744073709551614#64) <<< 5 ∧ s'.r14 = keyp ∧ s'.r15 = n ∧
      Vec s'.mem (fp + 64#64) k0 ∧ Vec s'.mem (fp + 80#64) k1 ∧ Vec s'.mem (fp + 128#64) l0 ∧ Vec s'.mem (fp + 144#64) l1 ∧
      Vec s'.mem (fp + 160#64) r0 ∧ Vec s'.mem (fp + 176#64) r1 ∧
      s'.mem.read (fp + 18446744073709551608#64) 64 = some 262566#64 ∧
      (∀ d : BitVec 64, inF d = true → (s'.mem (fp + d)).isSome = true) ∧
      (∀ x : BitVec 64, inF (x - fp) = false → s'.mem x = m x) ∧
      s'.mem (fp + 58#64) = some plat ∧ s'.mem (fp + 59#64) = some fl ∧ s'.mem (fp + 60#64) = some fl ∧
      s'.mem (fp + 61#64) = some 0#8 ∧ s'.mem (fp + 62#64) = some 0#8 ∧ s'.mem (fp + 63#64) = some 0#8 := by
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
  show ∃ s', steps Code.prog 52 ⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mm none', 0x40094⟩ = some s' ∧ _
  run_merge [wF, rF, fp_add, fp_sub, rdF64, alF, rd128F, wr128F, rdF8, rdF32, wrF8, wrF32, wrF64, h1, h2, h3, h4, h5, hTag', hL0', hL1', hR0', hR1', hK0', hK1', hOwn, hPlat, hFl, hF0, hF1, hF2, hF3]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro x hx; show mm _ x = m x; simp only [mm]; rw [over_out _ _ _ _ _ hx]; done)
    | (intro d hd; simp (disch := assumption) only [rF, Option.isSome_or, hOwn, Bool.or_true]; done)
    | simp (config := {maxSteps := 10000000}) (disch := decide) only [Vec, fp_add, rdF64, Mem.read8, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, rF, upd_apply, none_apply,
        BitVec.reduceEq, ↓reduceIte, Option.some_or, Option.none_or, and_self, hPlat, hFl, hF0, hF1, hF2, hF3, unbyte64,
        Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- The parent chaining value the kernels leave, as the two vectors of its slot: the first eight words
of the specification's compression of the key, the block `l ‖ r`, counter 0, length 64 and the flags. -/
def merged (k0 k1 l0 l1 r0 r1 : V) (fl : BitVec 8) : V × V :=
  let c := specCv (cvWords k0 k1) (blockWords l0 l1 r0 r1) 0 64 (fl.setWidth 32)
  (mk4 c[0] c[1] c[2] c[3], mk4 c[4] c[5] c[6] c[7])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- After the kernel: its result goes from the frame to the stack's slot, the length goes down by one, and
the count of turns left decides between the loop's head and its exit. -/
theorem post_avx (self arr keyp fp len n oL : BitVec 64) (c0 c1 : V) (b : Mem)
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
    ∃ s', steps Code.prog 12 ⟨rax, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, oL, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, over b fp inF none', 0x4005B⟩ = some s' ∧
      s'.pc = (if n - 1#64 = 0#64 then 0x401AB else 0x40094) ∧ s'.rax = len - 1#64 ∧ s'.r15 = n - 1#64 ∧
      s'.rbx = self ∧ s'.rsp = fp ∧ s'.rbp = rbp ∧ s'.r12 = arr ∧ s'.r14 = keyp ∧
      ∃ fF : Written, s'.mem = over (((b.put128 (oL + arr + 16#64) c1).put128 (oL + arr + 0#64) c0).put64 (self + 0#64) (len - 1#64)) fp inF fF ∧
        fF 58#64 = none ∧ fF 59#64 = none ∧ fF 60#64 = none ∧ fF 61#64 = none ∧ fF 62#64 = none ∧ fF 63#64 = none := by
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
  show ∃ s', steps Code.prog 12 ⟨rax, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, oL, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mm b none', 0x4005B⟩ = some s' ∧ _
  by_cases hz : n - 1#64 = 0#64
  · have hz' : (n - 1#64 == 0#64) = true := by simpa using hz
    rw [if_pos hz]
    run_merge [wF, rF, fp_add, alF, rd128F, wr128F, wrA1', wrA0', rdLen', wrLen', hOwn, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, hz']
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have hz' : (n - 1#64 == 0#64) = false := by simpa using hz
    rw [if_neg hz]
    run_merge [wF, rF, fp_add, alF, rd128F, wr128F, wrA1', wrA0', rdLen', wrLen', hOwn, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, hz']
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- After the kernel: its result goes from the frame to the stack's slot, the length goes down by one, and
the count of turns left decides between the loop's head and its exit. -/
theorem post_sse (self arr keyp fp len n oL : BitVec 64) (c0 c1 : V) (b : Mem)
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
    ∃ s', steps Code.prog 13 ⟨rax, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, oL, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, over b fp inF none', 0x401A6⟩ = some s' ∧
      s'.pc = (if n - 1#64 = 0#64 then 0x401AB else 0x40094) ∧ s'.rax = len - 1#64 ∧ s'.r15 = n - 1#64 ∧
      s'.rbx = self ∧ s'.rsp = fp ∧ s'.rbp = rbp ∧ s'.r12 = arr ∧ s'.r14 = keyp ∧
      ∃ fF : Written, s'.mem = over (((b.put128 (oL + arr + 16#64) c1).put128 (oL + arr + 0#64) c0).put64 (self + 0#64) (len - 1#64)) fp inF fF ∧
        fF 58#64 = none ∧ fF 59#64 = none ∧ fF 60#64 = none ∧ fF 61#64 = none ∧ fF 62#64 = none ∧ fF 63#64 = none := by
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
  show ∃ s', steps Code.prog 13 ⟨rax, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, oL, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mm b none', 0x401A6⟩ = some s' ∧ _
  by_cases hz : n - 1#64 = 0#64
  · have hz' : (n - 1#64 == 0#64) = true := by simpa using hz
    rw [if_pos hz]
    run_merge [wF, rF, fp_add, alF, rd128F, wr128F, wrA1', wrA0', rdLen', wrLen', hOwn, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, hz']
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have hz' : (n - 1#64 == 0#64) = false := by simpa using hz
    rw [if_neg hz]
    run_merge [wF, rF, fp_add, alF, rd128F, wr128F, wrA1', wrA0', rdLen', wrLen', hOwn, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, hz']
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **One turn of the compiled loop, by the AVX-512 kernel.** At the loop's head with `len` values on the stack
(`2 ≤ len ≤ 55`), `n` turns to go, the two top values `l` and `r` in their slots, the key and the flags
where `merge` put them: 426 instructions later the lower slot holds the parent chaining value of `l` and
`r` (`merged`), the length is `len - 1`, the turns to go `n - 1`, and the program is at the loop's head
or, when no turn is left, at its exit. Nothing else changes outside `merge`'s own frame. The three panic
sites are not reached. -/
theorem turn_avx (self arr keyp fp len n : BitVec 64) (l0 l1 r0 r1 k0 k1 : V) (fl : BitVec 8) (m : Mem)
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
    ∃ s', steps Code.prog (52 + (362 + 12)) ⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m, 0x40094⟩ = some s' ∧
      s'.pc = (if n - 1#64 = 0#64 then 0x401AB else 0x40094) ∧ s'.rax = len - 1#64 ∧ s'.r15 = n - 1#64 ∧
      s'.rbx = self ∧ s'.rsp = fp ∧ s'.rbp = rbp ∧ s'.r12 = arr ∧ s'.r14 = keyp ∧
      Vec s'.mem (arr + ((len + 18446744073709551614#64) <<< 5) + 0#64) (merged k0 k1 l0 l1 r0 r1 fl).1 ∧
      Vec s'.mem (arr + ((len + 18446744073709551614#64) <<< 5) + 16#64) (merged k0 k1 l0 l1 r0 r1 fl).2 ∧
      Quad s'.mem (self + 0#64) (len - 1#64) ∧
      (∀ d : BitVec 64, inF d = true → (s'.mem (fp + d)).isSome = true) ∧
      s'.mem (fp + 58#64) = some 5#8 ∧ s'.mem (fp + 59#64) = some fl ∧ s'.mem (fp + 60#64) = some fl ∧
      s'.mem (fp + 61#64) = some 0#8 ∧ s'.mem (fp + 62#64) = some 0#8 ∧ s'.mem (fp + 63#64) = some 0#8 ∧
      (∀ x : BitVec 64, inF (x - fp) = false → 32 ≤ (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat → 8 ≤ (x - self).toNat → s'.mem x = m x) := by
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
  refine ⟨s3, by rw [steps_add, e1, Option.bind_some, steps_add, e2, Option.bind_some, e3], pc3, ax3, r153, bx3, sp3, bp3, r123, r143,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem3, ← eA]
    refine vec_congr (m := (b.put128 (((len + 18446744073709551614#64) <<< 5) + arr + 16#64) (merged k0 k1 l0 l1 r0 r1 fl).2).put128 (((len + 18446744073709551614#64) <<< 5) + arr + 0#64) (merged k0 k1 l0 l1 r0 r1 fl).1)
      (fun x hx => ?_) (vec_put128 _ _ _)
    rw [over_out _ _ _ _ x (oA0 x hx), put64_other _ _ _ _ (notLen x (by rw [eA] at hx; bv_omega))]
  · rw [mem3, ← eA]
    refine vec_congr (m := b.put128 (((len + 18446744073709551614#64) <<< 5) + arr + 16#64) (merged k0 k1 l0 l1 r0 r1 fl).2) (fun x hx => ?_) (vec_put128 _ _ _)
    rw [over_out _ _ _ _ x (oA1 x hx), put64_other _ _ _ _ (notLen x (by rw [eA] at hx; bv_omega)), put128_other _ _ _ _ (by bv_omega)]
  · rw [mem3]; exact quad_congr (fun x hx => over_out _ _ _ _ x (oLen x hx)) (quad_put64 _ _ _)
  · intro d hd
    rw [mem3, over_in _ _ _ _ _ hd, Option.isSome_or]
    have := put64_isSome _ (self + 0#64) (len - 1#64) _ (put128_isSome _ (((len + 18446744073709551614#64) <<< 5) + arr + 0#64) (merged k0 k1 l0 l1 r0 r1 fl).1 _
      (put128_isSome _ (((len + 18446744073709551614#64) <<< 5) + arr + 16#64) (merged k0 k1 l0 l1 r0 r1 fl).2 _ (b_own d hd)))
    rw [this, Bool.or_true]
  all_goals first
    | (intro x hx hs hl
       rw [mem3, over_out _ _ _ _ x hx, put64_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by rw [eA]; bv_omega),
         put128_other _ _ _ _ (by rw [eA]; bv_omega), b_out x hx]; done)
    | (rw [mem3, over_in _ _ _ _ _ (by decide)]
       simp only [g58, g59, g60, g61, g62, g63, Option.none_or]
       rw [put64_other _ _ _ _ (frameNotLen _ (by decide)), put128_other _ _ _ _ (frameNotSlot _ (by decide)).1,
         put128_other _ _ _ _ (frameNotSlot _ (by decide)).2]
       first | exact bF58 | exact bF59 | exact bF60 | exact bF61 | exact bF62 | exact bF63)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **One turn of the compiled loop, by the SSE4.1 kernel.** At the loop's head with `len` values on the stack
(`2 ≤ len ≤ 55`), `n` turns to go, the two top values `l` and `r` in their slots, the key and the flags
where `merge` put them: 532 instructions later the lower slot holds the parent chaining value of `l` and
`r` (`merged`), the length is `len - 1`, the turns to go `n - 1`, and the program is at the loop's head
or, when no turn is left, at its exit. Nothing else changes outside `merge`'s own frame. The three panic
sites are not reached. -/
theorem turn_sse (self arr keyp fp len n : BitVec 64) (l0 l1 r0 r1 k0 k1 : V) (fl : BitVec 8) (m : Mem)
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
    ∃ s', steps Code.prog (52 + (467 + 13)) ⟨len, rcx, rdx, self, fp, rbp, rsi, rdi, r8, r9, arr, r13, keyp, n, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m, 0x40094⟩ = some s' ∧
      s'.pc = (if n - 1#64 = 0#64 then 0x401AB else 0x40094) ∧ s'.rax = len - 1#64 ∧ s'.r15 = n - 1#64 ∧
      s'.rbx = self ∧ s'.rsp = fp ∧ s'.rbp = rbp ∧ s'.r12 = arr ∧ s'.r14 = keyp ∧
      Vec s'.mem (arr + ((len + 18446744073709551614#64) <<< 5) + 0#64) (merged k0 k1 l0 l1 r0 r1 fl).1 ∧
      Vec s'.mem (arr + ((len + 18446744073709551614#64) <<< 5) + 16#64) (merged k0 k1 l0 l1 r0 r1 fl).2 ∧
      Quad s'.mem (self + 0#64) (len - 1#64) ∧
      (∀ d : BitVec 64, inF d = true → (s'.mem (fp + d)).isSome = true) ∧
      s'.mem (fp + 58#64) = some plat ∧ s'.mem (fp + 59#64) = some fl ∧ s'.mem (fp + 60#64) = some fl ∧
      s'.mem (fp + 61#64) = some 0#8 ∧ s'.mem (fp + 62#64) = some 0#8 ∧ s'.mem (fp + 63#64) = some 0#8 ∧
      (∀ x : BitVec 64, inF (x - fp) = false → 32 ≤ (x - (arr + ((len + 18446744073709551614#64) <<< 5))).toNat → 8 ≤ (x - self).toNat → s'.mem x = m x) := by
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
  refine ⟨s3, by rw [steps_add, e1, Option.bind_some, steps_add, e2, Option.bind_some, e3], pc3, ax3, r153, bx3, sp3, bp3, r123, r143,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem3, ← eA]
    refine vec_congr (m := (b.put128 (((len + 18446744073709551614#64) <<< 5) + arr + 16#64) (merged k0 k1 l0 l1 r0 r1 fl).2).put128 (((len + 18446744073709551614#64) <<< 5) + arr + 0#64) (merged k0 k1 l0 l1 r0 r1 fl).1)
      (fun x hx => ?_) (vec_put128 _ _ _)
    rw [over_out _ _ _ _ x (oA0 x hx), put64_other _ _ _ _ (notLen x (by rw [eA] at hx; bv_omega))]
  · rw [mem3, ← eA]
    refine vec_congr (m := b.put128 (((len + 18446744073709551614#64) <<< 5) + arr + 16#64) (merged k0 k1 l0 l1 r0 r1 fl).2) (fun x hx => ?_) (vec_put128 _ _ _)
    rw [over_out _ _ _ _ x (oA1 x hx), put64_other _ _ _ _ (notLen x (by rw [eA] at hx; bv_omega)), put128_other _ _ _ _ (by bv_omega)]
  · rw [mem3]; exact quad_congr (fun x hx => over_out _ _ _ _ x (oLen x hx)) (quad_put64 _ _ _)
  · intro d hd
    rw [mem3, over_in _ _ _ _ _ hd, Option.isSome_or]
    have := put64_isSome _ (self + 0#64) (len - 1#64) _ (put128_isSome _ (((len + 18446744073709551614#64) <<< 5) + arr + 0#64) (merged k0 k1 l0 l1 r0 r1 fl).1 _
      (put128_isSome _ (((len + 18446744073709551614#64) <<< 5) + arr + 16#64) (merged k0 k1 l0 l1 r0 r1 fl).2 _ (b_own d hd)))
    rw [this, Bool.or_true]
  all_goals first
    | (intro x hx hs hl
       rw [mem3, over_out _ _ _ _ x hx, put64_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by rw [eA]; bv_omega),
         put128_other _ _ _ _ (by rw [eA]; bv_omega), b_out x hx]; done)
    | (rw [mem3, over_in _ _ _ _ _ (by decide)]
       simp only [g58, g59, g60, g61, g62, g63, Option.none_or]
       rw [put64_other _ _ _ _ (frameNotLen _ (by decide)), put128_other _ _ _ _ (frameNotSlot _ (by decide)).1,
         put128_other _ _ _ _ (frameNotSlot _ (by decide)).2]
       first | exact bF58 | exact bF59 | exact bF60 | exact bF61 | exact bF62 | exact bF63)

#print axioms turn_avx
#print axioms turn_sse
