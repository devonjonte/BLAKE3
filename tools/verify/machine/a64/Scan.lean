import A64
import Code
import Mem
open A64

/-! # `scan` on AArch64: the same loop, the same theorem, a second machine

The Lean function is the x86-64 experiment's. The code is rustc's for AArch64: nine
instructions, no stack. -/

namespace Spec

/-- One word folded in: rotate left by five, xor the word. -/
def step (a w : BitVec 32) : BitVec 32 := a.rotateLeft 5 ^^^ w

/-- Every word folded into `a`, first to last. -/
def fold (a : BitVec 32) : List (BitVec 32) → BitVec 32
  | [] => a
  | w :: ws => fold (step a w) ws

/-- Each word replaced by the fold up to and including it. -/
def scan (a : BitVec 32) : List (BitVec 32) → List (BitVec 32)
  | [] => []
  | w :: ws => step a w :: scan (step a w) ws

end Spec

/-- The words of `ws`, in order from address `q`, each owned. -/
def Holds (m : Mem) : BitVec 64 → List (BitVec 32) → Prop
  | _, [] => True
  | q, w :: ws => Word m q w ∧ Holds m (q + 4) ws

theorem steps_mk (prog : Nat → Option Instr) (k : Nat) (x0 x1 x2 x8 x9 x30 : BitVec 64) (z : Option Bool) (mem : Mem)
    (pc : Nat) (leak : List Obs) :
    steps prog (k + 1) ⟨x0, x1, x2, x8, x9, x30, z, mem, pc, leak⟩ =
      match prog pc with
      | none => none
      | some i => (step i ⟨x0, x1, x2, x8, x9, x30, z, mem, pc, leak⟩).bind (steps prog k) := rfl

theorem steps_zero (prog : Nat → Option Instr) (s : State) : steps prog 0 s = some s := rfl

theorem steps_add (prog : Nat → Option Instr) (a b : Nat) (s : State) :
    steps prog (a + b) s = (steps prog a s).bind (steps prog b) := by
  induction a generalizing s with
  | zero => simp [steps]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp only [steps]
    cases prog s.pc with
    | none => rfl
    | some i =>
      simp only []
      cases step i s with
      | none => rfl
      | some s1 => simp only [Option.bind_some, ih]

/-- Run the instructions of a state that is written out. -/
macro "run_code" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := {maxSteps := 10000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step, State.get, State.set,
    Code.at_1000, Code.at_1004, Code.at_1008, Code.at_100C, Code.at_1010, Code.at_1014, Code.at_1018, Code.at_101C, Code.at_1020,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp,
    Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq, $hs,*])

theorem holds_congr {m m' : Mem} : ∀ (ws : List (BitVec 32)) (q : BitVec 64), 4 * ws.length < 2 ^ 63 →
    (∀ x, (x - q).toNat < 4 * ws.length → m' x = m x) → Holds m q ws → Holds m' q ws := by
  intro ws
  induction ws with
  | nil => intros; trivial
  | cons w ws ih =>
    intro q hn h ⟨hw, ht⟩
    simp only [List.length_cons] at hn h
    refine ⟨?_, ih (q + 4) (by omega) (fun x hx => h x (by bv_omega)) ht⟩
    obtain ⟨h0, h1, h2, h3⟩ := hw
    exact ⟨by rw [h q (by bv_omega)]; exact h0, by rw [h (q + 1) (by bv_omega)]; exact h1,
      by rw [h (q + 2) (by bv_omega)]; exact h2, by rw [h (q + 3) (by bv_omega)]; exact h3⟩

/-- What one turn of the compiled loop computes is the specification's step: a rotation right by 27 is one left by 5. -/
theorem turn64 (a w : BitVec 32) : w ^^^ a.rotateRight 27 = Spec.step a w := by
  simp only [Spec.step]; bv_decide

theorem more_words (n : Nat) (h : 4 * (n + 1 + 1) < 2 ^ 63) : BitVec.ofNat 64 (4 * (n + 1 + 1)) - 4 ≠ 0 := by bv_omega

theorem add0 (x : BitVec 64) : x + 0 = x := by bv_decide

theorem low32 (v : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 v) = v := by bv_decide

/-- What the loop lets an observer see, from its head with `n + 1` words from `p`: each word's
address twice (its read, its write) and where the branch after it goes. -/
def loopLeak : BitVec 64 → Nat → List Obs → List Obs
  | p, 0, seen => .pc 0x101C :: .addr p :: .addr (p + 0) :: seen
  | p, n + 1, seen => loopLeak (p + 4) n (.pc 0x1008 :: .addr p :: .addr (p + 0) :: seen)

/-- **The loop.** From its head with the words `w :: rest` at X0 and four times their number in
X8, five instructions a word bring it to the instruction after the loop with the fold in W2 and
the scan in their place; no other byte is changed. -/
theorem loop (rest : List (BitVec 32)) : ∀ (w : BitVec 32) (x0 x1 x2 x8 x9 x30 : BitVec 64) (z : Option Bool) (m : Mem)
    (leak : List Obs),
    Holds m x0 (w :: rest) →
    x8 = BitVec.ofNat 64 (4 * (rest.length + 1)) →
    4 * (rest.length + 1) < 2 ^ 63 →
    ∃ s', steps Code.prog (5 * (rest.length + 1)) ⟨x0, x1, x2, x8, x9, x30, z, m, 0x1008, leak⟩ = some s' ∧
      s'.pc = 0x101C ∧ s'.x2 = (Spec.fold (x2.setWidth 32) (w :: rest)).setWidth 64 ∧ s'.x30 = x30 ∧
      Holds s'.mem x0 (Spec.scan (x2.setWidth 32) (w :: rest)) ∧
      (∀ x, 4 * (rest.length + 1) ≤ (x - x0).toNat → s'.mem x = m x) ∧
      s'.leak = loopLeak x0 rest.length leak := by
  induction rest with
  | nil =>
    intro w x0 x1 x2 x8 x9 x30 z m leak ⟨hw, _⟩ h8 _
    subst h8
    have hw0 : Word m (x0 + 0) w := by rw [add0]; exact hw
    simp only [List.length_nil, Nat.zero_add, Nat.mul_one]
    have hz : (BitVec.ofNat 64 4 - 4 == 0) = true := by decide
    run_code [read_word hw0, write_word hw, turn64, low32, hz]
    exact ⟨_, rfl, rfl, rfl, rfl, ⟨word_put32 _ _ _, trivial⟩, fun x hx => put32_other _ _ _ x hx, rfl⟩
  | cons w2 rest ih =>
    intro w x0 x1 x2 x8 x9 x30 z m leak ⟨hw, ht⟩ h8 hn
    simp only [List.length_cons] at h8 hn ⊢
    have hw0 : Word m (x0 + 0) w := by rw [add0]; exact hw
    have hne : x8 - 4 ≠ 0 := by rw [h8]; exact more_words _ hn
    have hz : (x8 - 4 == 0) = false := by simpa using hne
    rw [show 5 * (rest.length + 1 + 1) = 5 + 5 * (rest.length + 1) by omega, steps_add]
    run_code [read_word hw0, write_word hw, turn64, low32, hz]
    have ht' : Holds (m.put32 x0 (Spec.step (BitVec.setWidth 32 x2) w)) (x0 + 4) (w2 :: rest) :=
      holds_congr _ _ (by simp only [List.length_cons]; omega)
        (fun x hx => put32_other _ _ _ x (by simp only [List.length_cons] at hx; bv_omega)) ht
    obtain ⟨s', hs, hpc, hx2, h30, hh, hf, hl⟩ :=
      ih w2 (x0 + 4) x1 (BitVec.setWidth 64 (Spec.step (BitVec.setWidth 32 x2) w)) (x8 - 4) (BitVec.setWidth 64 w) x30 _ _ _ ht'
        (by subst h8; bv_omega) (by omega)
    rw [low32] at hx2 hh
    refine ⟨s', hs, hpc, hx2, h30, ⟨?_, hh⟩, ?_, hl⟩
    · obtain ⟨p0, p1, p2, p3⟩ := word_put32 m x0 (Spec.step (BitVec.setWidth 32 x2) w)
      exact ⟨by rw [hf _ (by bv_omega)]; exact p0, by rw [hf _ (by bv_omega)]; exact p1,
        by rw [hf _ (by bv_omega)]; exact p2, by rw [hf _ (by bv_omega)]; exact p3⟩
    · intro x hx
      rw [hf x (by bv_omega), put32_other _ _ _ x (by bv_omega)]

/-- What a whole call lets an observer see: a function of the slice's address and length and of
the return address. The words and the seed are not among its arguments. -/
def scanLeak (p ra : BitVec 64) : Nat → List Obs → List Obs
  | 0, seen => .pc ra.toNat :: .pc 0x101C :: seen
  | n + 1, seen => .pc ra.toNat :: loopLeak p n (.pc 0x1004 :: seen)

theorem shl2 (x : BitVec 64) : x <<< 2 = x * 4 := by bv_decide

/-- **The compiled AArch64 `scan` computes `Spec.scan` and `Spec.fold`, for a slice of any length.**
Called with a slice of `ws.length` words at X0 (its bytes fewer than 2^63), the seed in W2 and a
return address in X30, it returns there with the fold in W0 and the scan where the slice was; no
byte outside the slice is changed, and what it lets an observer see is `scanLeak` of the slice's
address and length and the return address: the same for every seed and all words. -/
theorem scan_is_the_scan (ws : List (BitVec 32)) (x0 x1 x2 x8 x9 x30 : BitVec 64) (z : Option Bool) (m : Mem)
    (leak : List Obs)
    (hlen : x1 = BitVec.ofNat 64 ws.length) (hn : 4 * ws.length < 2 ^ 63) (hws : Holds m x0 ws) :
    ∃ k s', steps Code.prog k ⟨x0, x1, x2, x8, x9, x30, z, m, 0x1000, leak⟩ = some s' ∧ s'.pc = x30.toNat ∧
      s'.x0.setWidth 32 = Spec.fold (x2.setWidth 32) ws ∧
      Holds s'.mem x0 (Spec.scan (x2.setWidth 32) ws) ∧
      (∀ x, 4 * ws.length ≤ (x - x0).toNat → s'.mem x = m x) ∧
      s'.leak = scanLeak x0 x30 ws.length leak := by
  cases ws with
  | nil =>
    simp only [List.length_nil] at hlen
    subst hlen
    refine ⟨3, ?_⟩
    have hz : (BitVec.ofNat 64 0 = 0) = True := by simp
    run_code [hz]
    exact ⟨_, rfl, rfl, rfl, trivial, fun x _ => rfl, rfl⟩
  | cons w rest =>
    simp only [List.length_cons] at hlen hn ⊢
    have hnz : (x1 = 0) = False := by subst hlen; simp; bv_omega
    have hpre : steps Code.prog 2 ⟨x0, x1, x2, x8, x9, x30, z, m, 0x1000, leak⟩ =
        some ⟨x0, x1, x2, x1 <<< 2, x9, x30, z, m, 0x1008, .pc 0x1004 :: leak⟩ := by
      run_code [hnz]
    obtain ⟨⟨a0, a1, a2, a8, a9, a30, az, am, apc, aleak⟩, hs1, hpc1, hx2, h30, hh, hf, hl⟩ :=
      loop rest w x0 x1 x2 (x1 <<< 2) x9 x30 z m (.pc 0x1004 :: leak) hws (by subst hlen; rw [shl2]; bv_omega) hn
    simp only at hpc1 hx2 h30 hh hf hl
    subst hpc1 hx2 hl
    subst a30
    have hpost : ∃ s', steps Code.prog 2 ⟨a0, a1, (Spec.fold (x2.setWidth 32) (w :: rest)).setWidth 64, a8, a9, x30, az, am, 0x101C,
          loopLeak x0 rest.length (.pc 0x1004 :: leak)⟩ = some s' ∧ s'.pc = x30.toNat ∧
        s'.x0 = (Spec.fold (x2.setWidth 32) (w :: rest)).setWidth 64 ∧ s'.mem = am ∧
        s'.leak = .pc x30.toNat :: loopLeak x0 rest.length (.pc 0x1004 :: leak) := by
      run_code []
      exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨s', hs', hpc', hx0', hm', hl'⟩ := hpost
    refine ⟨2 + (5 * (rest.length + 1) + 2), s', ?_, hpc', ?_, ?_, ?_, hl'⟩
    · rw [steps_add, hpre, Option.bind_some, steps_add, hs1, Option.bind_some, hs']
    · rw [hx0']; bv_decide
    · rw [hm']; exact hh
    · intro x hx; rw [hm', hf x hx]

#print axioms scan_is_the_scan
