import Rule
import Run
import Lang
import Code_Mix
open X86

/-! `mix`: the machine code computes the Lean function. Written by make.py from the listing; not edited by hand. -/

namespace Mix

abbrev prog := Code_Mix.prog

/-- Where the compiled loop keeps its things. -/
def view : View State Obs (BitVec 64 × BitVec 64 × BitVec 64) where
  steps := steps prog
  steps_add := steps_add prog
  mem := State.mem
  pc := State.pc
  leak := State.leak
  head := 0x1015
  exit := 0x103E
  turn := 13
  acc s := s.rdx.setWidth 32
  out s := s.rax.setWidth 32
  ptr s := s.rdi + s.rcx
  left s := s.rsi - s.rcx
  kept s := (s.rbx, s.rsp, s.rbp)
  good s := s.r8 = 0xF0F0F0F0
  obs p last := [.pc (if last then 0x103E else 0x1015), .addr p, .addr p]

macro "close" : tactic => `(tactic| first
  | rfl | trivial | bv_decide
  | (simp only [view, mix, Scan.step, Exp.eval]; bv_decide)
  | (apply put32_congr; simp only [view, mix, Scan.step, Exp.eval]; bv_decide))

/-- **One turn of the compiled loop is one step of the Lean function.** -/
theorem turn : Turn view mix.step := by
  intro ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, zf, cf, m, pc, leak⟩ w hpc hg hw
  simp only [view] at hpc hg hw ⊢
  subst hpc
  subst hg
  run_code [read_word hw, write_word hw]
  split
  · rename_i h
    have h4 : ¬ (rsi - rcx = 4) := by bv_decide
    simp only [h4, ↓reduceIte, decide_false]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> close
  · rename_i h
    have h4 : rsi - rcx = 4 := by bv_decide
    simp only [h4, ↓reduceIte, decide_true]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> close

/-- What a whole call shows an observer: a function of the slice's address and length and of the stack
pointer. The words and the seed are not among its arguments. -/
def leakOf (p sp : BitVec 64) : Nat → List Obs → List Obs
  | 0, seen => .pc 0 :: .addr (sp - 8 + 8) :: .addr (sp - 8) :: .pc 0x1040 :: .addr (sp - 8) :: seen
  | n + 1, seen => .pc 0 :: .addr (sp - 8 + 8) :: .addr (sp - 8) :: loopLeak view.obs p n (.pc 0x1009 :: .addr (sp - 8) :: seen)

/-- **The compiled `mix` computes the Lean function `mix`, for a slice of any length.**
Called with a slice of `ws.length` words at RDI (its bytes fewer than 2^63), the seed in EDX, a return
address on the stack, the eight bytes below it owned and the slice apart from both: it returns, with
`mix.fold seed ws` in EAX, `mix.scan seed ws` where the slice was, the stack pointer popped, RBX and
RBP as they were, no byte changed outside the slice and those eight, and a trace that is `leakOf` of the
slice's address and length and the stack pointer. -/
theorem mix_is_its_lean_function (ws : List (BitVec 32)) (seed : BitVec 32)
    (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 : BitVec 64) (zf cf : Option Bool) (m : Mem) (leak : List Obs)
    (hlen : rsi = BitVec.ofNat 64 ws.length) (hn : 4 * ws.length < 2 ^ 63)
    (hseed : rdx.setWidth 32 = seed)
    (hws : Holds m rdi ws)
    (hret : m.read rsp 64 = some 0)
    (hstack : Owned8 m (rsp - 8))
    (hapart : ∀ x, (x - rdi).toNat < 4 * ws.length → 16 ≤ (x - (rsp - 8)).toNat) :
    ∃ s', Returns prog ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, zf, cf, m, 0x1000, leak⟩ s' ∧
      s'.rax.setWidth 32 = mix.fold seed ws ∧ s'.rsp = rsp + 8 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧
      Holds s'.mem rdi (mix.scan seed ws) ∧
      (∀ x, 4 * ws.length ≤ (x - rdi).toNat → 8 ≤ (x - (rsp - 8)).toNat → s'.mem x = m x) ∧
      s'.leak = leakOf rdi rsp ws.length leak := by
  subst hseed
  have hpopm : (m.put64 (rsp - 8) rbp).read (rsp - 8) 64 = some rbp := read_put64 _ _ _
  have hretm : (m.put64 (rsp - 8) rbp).read (rsp - 8 + 8) 64 = some 0 := by
    rw [read_congr (m := m) _ (fun x hx => put64_other _ _ _ x (by bv_omega)), show rsp - 8 + 8 = rsp by bv_decide]
    exact hret
  cases ws with
  | nil =>
    -- An empty slice: 7 instructions.
    simp only [List.length_nil] at hlen
    subst hlen
    have hz : (BitVec.ofNat 64 0 &&& BitVec.ofNat 64 0 == 0) = true := by decide
    have h : ∃ s', steps prog 7 ⟨rax, rcx, rdx, rbx, rsp, rbp, BitVec.ofNat 64 0, rdi, r8, r9, zf, cf, m, 0x1000, leak⟩ = some s' ∧
        s'.pc = done ∧ s'.rax.setWidth 32 = rdx.setWidth 32 ∧ s'.rsp = rsp + 8 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧
        s'.mem = m.put64 (rsp - 8) rbp ∧ s'.leak = leakOf rdi rsp 0 leak := by
      run_code [write_quad hstack, hz, hpopm, hretm]
      refine ⟨_, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;> (simp only []; bv_decide)
    obtain ⟨s', hs, hpc, hax, hsp, hbx, hbp, hm, hl⟩ := h
    exact ⟨s', ⟨7, hs, hpc⟩, hax, hsp, hbx, hbp, trivial, fun x _ h8 => by rw [hm, put64_other _ _ _ x h8], hl⟩
  | cons w rest =>
    simp only [List.length_cons] at hlen hn hapart ⊢
    -- 7 instructions to the loop's head.
    have hnz : (rsi &&& rsi == 0) = false := by subst hlen; simp; bv_omega
    have hpre : ∃ s1, steps prog 7 ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, zf, cf, m, 0x1000, leak⟩ = some s1 ∧
        view.pc s1 = view.head ∧ view.good s1 ∧ view.acc s1 = rdx.setWidth 32 ∧ view.ptr s1 = rdi ∧
        view.left s1 = rsi * 4 ∧ view.mem s1 = m.put64 (rsp - 8) rbp ∧ view.kept s1 = (rbx, rsp - 8, rsp - 8) ∧
        view.leak s1 = .pc 0x1009 :: .addr (rsp - 8) :: leak := by
      run_code [write_quad hstack, hnz]
      refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> close
    obtain ⟨s1, hs1, hpc1, hg1, hacc1, hptr1, hleft1, hmem1, hk1, hl1⟩ := hpre
    -- The loop, by the rule.
    have hws1 : Holds (view.mem s1) (view.ptr s1) (w :: rest) := by
      rw [hptr1, hmem1]
      exact holds_congr _ _ (by simp only [List.length_cons]; omega)
        (fun x hx => put64_other _ _ _ x (by simp only [List.length_cons] at hx; have := hapart x hx; omega)) hws
    obtain ⟨s2, hs2, hpc2, hout2, hh2, hf2, hk2, hl2⟩ :=
      loop_rule view mix.step turn rest w s1 hpc1 hg1 hws1 (by rw [hleft1]; subst hlen; bv_omega) hn
    rw [hptr1, hacc1] at hh2
    rw [hptr1, hmem1] at hf2
    rw [hptr1, hl1] at hl2
    rw [hacc1] at hout2
    rw [hk1] at hk2
    obtain ⟨rax2, rcx2, rdx2, rbx2, rsp2, rbp2, rsi2, rdi2, r82, r92, zf2, cf2, m2, pc2, leak2⟩ := s2
    have hpc2' : pc2 = 0x103E := hpc2
    have hk2' : (rbx2, rsp2, rbp2) = (rbx, rsp - 8, rsp - 8) := hk2
    simp only [Prod.mk.injEq] at hk2'
    obtain ⟨hb, hsp, hbp⟩ := hk2'
    subst hpc2' hsp hbp
    subst rbx2
    have hf2' : ∀ x, 4 * (rest.length + 1) ≤ (x - rdi).toNat → m2 x = (m.put64 (rsp - 8) rbp) x := hf2
    -- Outside the slice the loop changed nothing: the saved RBP and the return address are there.
    have hout : ∀ x, (x - (rsp - 8)).toNat < 16 → 4 * (rest.length + 1) ≤ (x - rdi).toNat := fun x hx =>
      Nat.le_of_not_lt (fun h => by have := hapart x h; omega)
    have hpop : m2.read (rsp - 8) 64 = some rbp := by
      rw [read_congr (m := m.put64 (rsp - 8) rbp) _ (fun x hx => hf2' x (hout x (by omega)))]; exact hpopm
    have hret2 : m2.read (rsp - 8 + 8) 64 = some 0 := by
      rw [read_congr (m := m.put64 (rsp - 8) rbp) _ (fun x hx => hf2' x (hout x (by bv_omega)))]; exact hretm
    -- 3 more instructions: out of the frame, return.
    have hpost : ∃ s', steps prog 3 ⟨rax2, rcx2, rdx2, rbx, rsp - 8, rsp - 8, rsi2, rdi2, r82, r92, zf2, cf2, m2, 0x103E, leak2⟩ = some s' ∧
        s'.pc = done ∧ s'.rax = rax2 ∧ s'.rsp = rsp + 8 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧ s'.mem = m2 ∧
        s'.leak = .pc 0 :: .addr (rsp - 8 + 8) :: .addr (rsp - 8) :: leak2 := by
      run_code [hpop, hret2]
      refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (first | rfl | (simp only []; bv_decide))
    obtain ⟨s', hs', hpc', hax', hsp', hbx', hbp', hm', hl'⟩ := hpost
    refine ⟨s', ⟨7 + (13 * (rest.length + 1) + 3), ?_, hpc'⟩, ?_, hsp', hbx', hbp', ?_, ?_, ?_⟩
    · rw [steps_add, hs1, Option.bind_some, steps_add,
        show steps prog (13 * (rest.length + 1)) s1 = _ from hs2, Option.bind_some, hs']
    · rw [hax']; exact hout2
    · rw [hm']; exact hh2
    · intro x hx hx8
      rw [hm', hf2' x hx, put64_other _ _ _ x hx8]
    · rw [hl']
      have e : leak2 = _ := hl2
      rw [e]; rfl

#print axioms mix_is_its_lean_function

end Mix
