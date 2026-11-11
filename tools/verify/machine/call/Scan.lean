import X86
import Code
import Mem
open X86

/-! # `scan`: a loop over memory the caller owns

The Lean function, and the compiled Rust (`fold.rs`, rustc 1.99.1, opt-level s) proved to
compute it for a slice of any length. -/

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

theorem steps_mk (prog : Nat → Option (Instr × Nat)) (k : Nat) (rax rcx rdx rbx rsp rbp rsi rdi r8 r14 : BitVec 64)
    (zf cf : Option Bool) (mem : Mem) (pc : Nat) (leak : List Obs) :
    steps prog (k + 1) ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r14, zf, cf, mem, pc, leak⟩ =
      match prog pc with
      | none => none
      | some (i, next) => (step i next ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r14, zf, cf, mem, pc, leak⟩).bind (steps prog k) := rfl

theorem steps_zero (prog : Nat → Option (Instr × Nat)) (s : State) : steps prog 0 s = some s := rfl

theorem steps_add (prog : Nat → Option (Instr × Nat)) (a b : Nat) (s : State) :
    steps prog (a + b) s = (steps prog a s).bind (steps prog b) := by
  induction a generalizing s with
  | zero => simp [steps]
  | succ a ih =>
    rw [Nat.add_right_comm]
    simp only [steps]
    cases prog s.pc with
    | none => rfl
    | some x =>
      obtain ⟨i, next⟩ := x
      simp only []
      cases step i next s with
      | none => rfl
      | some s1 => simp only [Option.bind_some, ih]

/-- Run the instructions of a state that is written out. -/
macro "run_code" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := {maxSteps := 10000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step,
    X86.read, write, addr, State.get, State.set, trunc, logic, holds, touched, seen,
    List.nil_append, List.cons_append, List.append_nil,
    Code.at_1000, Code.at_1002, Code.at_1005, Code.at_1007, Code.at_1008, Code.at_100B, Code.at_100F, Code.at_1011, Code.at_1014, Code.at_1017, Code.at_101A, Code.at_101E, Code.at_1021, Code.at_1023, Code.at_1024, Code.at_1025, Code.at_1026, Code.at_1029, Code.at_102B, Code.at_102C, Code.at_102F, Code.at_1032, Code.at_1035, Code.at_103A, Code.at_103D, Code.at_1040, Code.at_1042, Code.at_1043, Code.at_1045, Code.at_1046,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp,
    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq, $hs,*])

/-- A list in memory is still there in a memory that agrees on its bytes. -/
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

/-- What one turn of the compiled loop leaves in EAX and in the word, as the specification's step. -/
theorem turn64 (a w : BitVec 32) :
    (BitVec.setWidth 64 ((BitVec.setWidth 32 (BitVec.setWidth 64 a)).rotateLeft 5) &&& 4294967295 ^^^ BitVec.setWidth 64 w) &&&
      4294967295 = BitVec.setWidth 64 (Spec.step a w) := by
  simp only [Spec.step]; bv_decide

theorem turn32 (a w : BitVec 32) :
    BitVec.setWidth 32 ((BitVec.setWidth 64 ((BitVec.setWidth 32 (BitVec.setWidth 64 a)).rotateLeft 5) &&& 4294967295 ^^^
      BitVec.setWidth 64 w) &&& 4294967295 &&& 4294967295) = Spec.step a w := by
  simp only [Spec.step]; bv_decide

theorem low32 (v : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 v &&& 4294967295) = v := by bv_decide

/-- What the loop lets an observer see, from its head with `n + 1` words ahead of offset `c`: each
word's address twice (its read, its write) and where the jump after it goes. No word, and nothing
computed from one, is in it. -/
def loopLeak (p : BitVec 64) : BitVec 64 → Nat → List Obs → List Obs
  | c, 0, seen => .pc 0x1023 :: .addr (p + c) :: .addr (p + c) :: seen
  | c, n + 1, seen => loopLeak p (c + 4) n (.pc 0x1011 :: .addr (p + c) :: .addr (p + c) :: seen)

/-- **The loop.** From its head with `a` in EAX and the words `w :: rest` ahead of RCX, six instructions a
word bring it to the instruction after the loop with the fold in EAX and the scan in their place; no
other byte is changed. -/
theorem loop (rest : List (BitVec 32)) : ∀ (w a : BitVec 32) (rcx rdx rbx rsp rbp rsi rdi r8 r14 : BitVec 64)
    (zf cf : Option Bool) (m : Mem) (leak : List Obs),
    Holds m (rdi + rcx) (w :: rest) →
    rsi = rcx + BitVec.ofNat 64 (4 * (rest.length + 1)) →
    4 * (rest.length + 1) < 2 ^ 63 →
    ∃ s', steps Code.prog (6 * (rest.length + 1)) ⟨a.setWidth 64, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r14, zf, cf, m, 0x1011, leak⟩ = some s' ∧
      s'.pc = 0x1023 ∧ s'.rax = (Spec.fold a (w :: rest)).setWidth 64 ∧ s'.rbx = rbx ∧ s'.rsp = rsp ∧ s'.rbp = rbp ∧ s'.r14 = r14 ∧
      Holds s'.mem (rdi + rcx) (Spec.scan a (w :: rest)) ∧
      (∀ x, 4 * (rest.length + 1) ≤ (x - (rdi + rcx)).toNat → s'.mem x = m x) ∧
      s'.leak = loopLeak rdi rcx rest.length leak := by
  induction rest with
  | nil =>
    intro w a rcx rdx rbx rsp rbp rsi rdi r8 r14 zf cf m leak ⟨hw, _⟩ hsi _
    subst hsi
    simp only [List.length_nil, Nat.zero_add, Nat.mul_one]
    run_code [read_word hw, write_word hw]
    simp only [turn64, low32]
    have hc : (!(rcx + 4#64 - (rcx + 4) == 0)) = false := by bv_decide
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨word_put32 _ _ _, trivial⟩, fun x hx => put32_other _ _ _ x hx, rfl⟩
  | cons w2 rest ih =>
    intro w a rcx rdx rbx rsp rbp rsi rdi r8 r14 zf cf m leak ⟨hw, ht⟩ hsi hn
    simp only [List.length_cons] at hsi hn ⊢
    rw [show 6 * (rest.length + 1 + 1) = 6 + 6 * (rest.length + 1) by omega, steps_add]
    run_code [read_word hw, write_word hw]
    simp only [turn64, low32]
    have hne : rsi - (rcx + 4) ≠ 0 := by subst hsi; bv_omega
    have hc : (!(rsi - (rcx + 4) == 0)) = true := by simpa using hne
    simp only [hc, ↓reduceIte]
    have ht' : Holds (m.put32 (rdi + rcx) (Spec.step a w)) (rdi + (rcx + 4)) (w2 :: rest) := by
      rw [← BitVec.add_assoc]
      exact holds_congr _ _ (by simp only [List.length_cons]; omega)
        (fun x hx => put32_other _ _ _ x (by simp only [List.length_cons] at hx; bv_omega)) ht
    obtain ⟨s', hs, hpc, hax, hbx, hsp, hbp, h14, hh, hf, hl⟩ :=
      ih w2 (Spec.step a w) (rcx + 4) rdx rbx rsp rbp rsi rdi r8 r14 _ _ _ _ ht' (by subst hsi; bv_omega) (by omega)
    refine ⟨s', hs, hpc, hax, hbx, hsp, hbp, h14, ⟨?_, ?_⟩, ?_, hl⟩
    · obtain ⟨p0, p1, p2, p3⟩ := word_put32 m (rdi + rcx) (Spec.step a w)
      exact ⟨by rw [hf _ (by bv_omega)]; exact p0, by rw [hf _ (by bv_omega)]; exact p1,
        by rw [hf _ (by bv_omega)]; exact p2, by rw [hf _ (by bv_omega)]; exact p3⟩
    · rw [BitVec.add_assoc]; exact hh
    · intro x hx
      rw [hf x (by bv_omega), put32_other _ _ _ x (by bv_omega)]

theorem low_is (x : BitVec 64) : x &&& 4294967295 = BitVec.setWidth 64 (BitVec.setWidth 32 x) := by bv_decide
theorem xor_same (x : BitVec 64) : (x &&& 4294967295 ^^^ x &&& 4294967295) &&& 4294967295 = 0 := by bv_decide
theorem shl2 (x : BitVec 64) : x <<< 2 = x * 4 := by bv_decide

/-- What a whole call lets an observer see: a function of the slice's address and length and of the
stack pointer. The words and the seed are not among its arguments. -/
def scanLeak (p sp ra : BitVec 64) : Nat → List Obs → List Obs
  | 0, seen => .pc ra.toNat :: .addr sp :: .pc 0x1024 :: seen
  | n + 1, seen => .pc ra.toNat :: .addr sp :: .addr (sp - 8) :: loopLeak p 0 n (.addr (sp - 8) :: .pc 0x1007 :: seen)

/-- **The compiled `scan` computes `Spec.scan` and `Spec.fold`, for a slice of any length.**
Called with a slice of `ws.length` words at RDI (as Rust passes one: its bytes fewer than 2^63), the
seed in EDX, a return address on the stack, the eight bytes below it owned and the slice apart from
both: it returns, with the fold in EAX, the scan where the slice was, the stack pointer popped, RBX and
RBP as they were, and no byte changed outside the slice and those eight. What it lets an observer see
(the addresses it touches, the way each jump goes) is `scanLeak` of the slice's address and length and
the stack pointer: the same for every seed and all words. -/
theorem scan_is_the_scan (ws : List (BitVec 32)) (seed : BitVec 32)
    (rax rcx rdx rbx rsp rbp rsi rdi r8 r14 ra : BitVec 64) (zf cf : Option Bool) (m : Mem) (leak : List Obs)
    (hlen : rsi = BitVec.ofNat 64 ws.length) (hn : 4 * ws.length < 2 ^ 63)
    (hseed : rdx.setWidth 32 = seed)
    (hws : Holds m rdi ws)
    (hret : m.read rsp 64 = some ra)
    (hstack : Owned8 m (rsp - 8))
    (hapart : ∀ x, (x - rdi).toNat < 4 * ws.length → 16 ≤ (x - (rsp - 8)).toNat) :
    ∃ k s', steps Code.prog k ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r14, zf, cf, m, 0x1000, leak⟩ = some s' ∧ s'.pc = ra.toNat ∧
      s'.rax.setWidth 32 = Spec.fold seed ws ∧ s'.rsp = rsp + 8 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧ s'.r14 = r14 ∧
      Holds s'.mem rdi (Spec.scan seed ws) ∧
      (∀ x, 4 * ws.length ≤ (x - rdi).toNat → 8 ≤ (x - (rsp - 8)).toNat → s'.mem x = m x) ∧
      s'.leak = scanLeak rdi rsp ra ws.length leak := by
  subst hseed
  cases ws with
  | nil =>
    -- An empty slice: four instructions, straight to the return.
    simp only [List.length_nil] at hlen
    subst hlen
    have h : ∃ s', steps Code.prog 4 ⟨rax, rcx, rdx, rbx, rsp, rbp, BitVec.ofNat 64 0, rdi, r8, r14, zf, cf, m, 0x1000, leak⟩ = some s' ∧
        s'.pc = ra.toNat ∧ s'.rax.setWidth 32 = rdx.setWidth 32 ∧ s'.rsp = rsp + 8 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧ s'.r14 = r14 ∧ s'.mem = m ∧
        s'.leak = .pc ra.toNat :: .addr rsp :: .pc 0x1024 :: leak := by
      have hz : (BitVec.ofNat 64 0 &&& BitVec.ofNat 64 0 == 0) = true := by decide
      run_code [hret, hz]
      refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      simp only []; bv_decide
    obtain ⟨s', hs, hpc, hax, hsp, hbx, hbp, h14, hm, hl⟩ := h
    exact ⟨4, s', hs, hpc, hax, hsp, hbx, hbp, h14, trivial, fun x _ _ => by rw [hm], hl⟩
  | cons w rest =>
    simp only [List.length_cons] at hlen hn hapart ⊢
    -- Seven instructions to the loop's head: the frame is made, RCX is 0, RSI the slice's bytes.
    have hnz : (rsi &&& rsi == 0) = false := by subst hlen; simp; bv_omega
    have hpre : steps Code.prog 7 ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r14, zf, cf, m, 0x1000, leak⟩ =
        some ⟨(rdx.setWidth 32).setWidth 64, 0, rdx, rbx, rsp - 8, rsp - 8, rsi * 4, rdi, r8, r14, some true, some false,
          m.put64 (rsp - 8) rbp, 0x1011, .addr (rsp - 8) :: .pc 0x1007 :: leak⟩ := by
      run_code [write_quad hstack, hnz]
      simp [xor_same, shl2] <;> bv_decide
    -- The loop, on the memory with the frame in it.
    have e0 : rdi + 0 = rdi := by bv_decide
    have hws1 : Holds (m.put64 (rsp - 8) rbp) (rdi + 0) (w :: rest) := by
      rw [e0]
      exact holds_congr _ _ (by simp only [List.length_cons]; omega)
        (fun x hx => put64_other _ _ _ x (by simp only [List.length_cons] at hx; have := hapart x hx; omega)) hws
    obtain ⟨s1, hs1, hpc1, hax1, hbx1, hsp1, hbp1, h141, hh1, hf1, hl1⟩ :=
      loop rest w (rdx.setWidth 32) 0 rdx rbx (rsp - 8) (rsp - 8) (rsi * 4) rdi r8 r14 (some true) (some false) _ _ hws1
        (by subst hlen; bv_omega) hn
    simp only [e0] at hh1 hf1
    -- Outside the slice the loop changed nothing: the saved RBP and the return address are there.
    have hout : ∀ x, (x - (rsp - 8)).toNat < 16 → 4 * (rest.length + 1) ≤ (x - rdi).toNat := fun x hx =>
      Nat.le_of_not_lt (fun h => by have := hapart x h; omega)
    have hpop : s1.mem.read (rsp - 8) 64 = some rbp := by
      rw [read_congr (m := m.put64 (rsp - 8) rbp) _ (fun x hx => hf1 x (hout x (by omega))), read_put64]
    have hret1 : s1.mem.read (rsp - 8 + 8) 64 = some ra := by
      rw [read_congr (m := m) _ (fun x hx => by
        rw [hf1 x (hout x (by bv_omega)), put64_other _ _ _ x (by bv_omega)])]
      rw [show rsp - 8 + 8 = rsp by bv_decide]; exact hret
    -- Two more instructions: pop, return.
    obtain ⟨rax1, rcx1, rdx1, rbx1, rsp1, rbp1, rsi1, rdi1, r81, r141, zf1, cf1, m1, pc1, leak1⟩ := s1
    simp only at hpc1 hax1 hbx1 hsp1 hbp1 h141 hh1 hf1 hpop hret1 hl1
    subst hpc1 hax1 hsp1 hbp1 hl1
    subst rbx1 r141
    have hpost : ∃ s', steps Code.prog 2 ⟨(Spec.fold (rdx.setWidth 32) (w :: rest)).setWidth 64, rcx1, rdx1, rbx, rsp - 8, rsp - 8, rsi1, rdi1, r81, r14, zf1, cf1, m1, 0x1023,
          loopLeak rdi 0 rest.length (.addr (rsp - 8) :: .pc 0x1007 :: leak)⟩ = some s' ∧
        s'.pc = ra.toNat ∧ s'.rax = (Spec.fold (rdx.setWidth 32) (w :: rest)).setWidth 64 ∧ s'.rsp = rsp + 8 ∧
        s'.rbx = rbx ∧ s'.rbp = rbp ∧ s'.r14 = r14 ∧ s'.mem = m1 ∧
        s'.leak = .pc ra.toNat :: .addr (rsp - 8 + 8) :: .addr (rsp - 8) :: loopLeak rdi 0 rest.length (.addr (rsp - 8) :: .pc 0x1007 :: leak) := by
      run_code [hpop, hret1]
      simp
      bv_decide
    obtain ⟨s', hs', hpc', hax', hsp', hbx', hbp', h14', hm', hl'⟩ := hpost
    refine ⟨7 + (6 * (rest.length + 1) + 2), s', ?_, hpc', ?_, hsp', hbx', hbp', h14', ?_, ?_, ?_⟩
    · rw [steps_add, hpre, Option.bind_some, steps_add, hs1, Option.bind_some, hs']
    · rw [hax']; bv_decide
    · rw [hm']; exact hh1
    · intro x hx hx8
      rw [hm', hf1 x hx, put64_other _ _ _ x hx8]
    · rw [hl', show rsp - 8 + 8 = rsp by bv_decide]; rfl

#print axioms scan_is_the_scan
