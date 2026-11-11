import X86
import Code
import Regions
open X86

/-! # `Hash == Hash`, as compiled, is equality and shows nothing of either hash

`impl PartialEq for Hash` is `constant_time_eq::constant_time_eq_32(&self.0, &other.0)`. Its machine
code (rustc 1.99.1, x86-64, `probe.rs`) is fourteen instructions; LLVM made the crate's xor-and-or
loop into two byte comparisons, an AND and a mask. The theorem is about those instructions. -/

/-- The thirty-two bytes of a hash, given as a function of the offset. -/
def bytesOf (h : BitVec 64 → BitVec 8) : List (BitVec 8) := [h 0#64, h 1#64, h 2#64, h 3#64, h 4#64, h 5#64, h 6#64, h 7#64, h 8#64, h 9#64, h 10#64, h 11#64, h 12#64, h 13#64, h 14#64, h 15#64, h 16#64, h 17#64, h 18#64, h 19#64, h 20#64, h 21#64, h 22#64, h 23#64, h 24#64, h 25#64, h 26#64, h 27#64, h 28#64, h 29#64, h 30#64, h 31#64]

/-- The sixteen bytes around the stack pointer the function uses: eight below it (the saved RBP)
and the return address. -/
def inS (d : BitVec 64) : Bool := (d + 8#64).ult 16#64

/-- What a call shows an observer, newest first: where the two hashes and the stack are. Neither
hash's bytes occur in it. -/
def eqLeak (pa pb sp : BitVec 64) : List Obs :=
  [.pc 0, .addr (sp + 0#64), .addr (sp + 18446744073709551608#64), .addr (pb + 16#64), .addr (pb + 0#64),
   .addr (pa + 16#64), .addr (pa + 0#64), .addr (sp + 18446744073709551608#64)]

theorem steps_mk (prog : Nat → Option (Instr × Nat)) (k : Nat) (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 : BitVec 64)
    (x0 x1 x2 x3 : BitVec 128) (zf cf : Option Bool) (mem : Mem) (pc : Nat) (leak : List Obs) :
    steps prog (k + 1) ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, x0, x1, x2, x3, zf, cf, mem, pc, leak⟩ =
      match prog pc with
      | none => none
      | some (i, next) => (step i next ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, x0, x1, x2, x3, zf, cf, mem, pc, leak⟩).bind (steps prog k) := rfl

theorem steps_zero (prog : Nat → Option (Instr × Nat)) (s : State) : steps prog 0 s = some s := rfl

theorem add_add (a c d : BitVec 64) : a + c + d = a + (c + d) := by bv_decide
theorem sub_lit (a c : BitVec 64) : a - c = a + (-c) := by bv_decide

/-- Eight bytes written and read back are the value. -/
theorem unbyte64 (v : BitVec 64) : BitVec.setWidth 64 (byte v 0) ||| BitVec.setWidth 64 (byte v 1) <<< 8 ||| BitVec.setWidth 64 (byte v 2) <<< 16 ||| BitVec.setWidth 64 (byte v 3) <<< 24 ||| BitVec.setWidth 64 (byte v 4) <<< 32 ||| BitVec.setWidth 64 (byte v 5) <<< 40 ||| BitVec.setWidth 64 (byte v 6) <<< 48 ||| BitVec.setWidth 64 (byte v 7) <<< 56 = v := by
  simp only [byte]; bv_decide

macro "run_eq" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) (disch := decide) only [steps_mk, steps_zero, step,
    X86.read, write, addr, State.get, State.set, State.xmm, State.setx, trunc, logic, holds, done, touched, seen,
    List.nil_append, List.cons_append, List.append_nil, code_at,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp,
    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq,
    Mem.read, Mem.read8, Mem.read128, Mem.write, Mem.write8, Mem.write128, Option.isSome_some,
    upd_apply, none_apply, Option.some_or, Option.none_or,
    BitVec.ofNat_eq_ofNat, add_add, sub_lit, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.reduceMul, BitVec.reduceAnd, BitVec.reduceEq,
    BitVec.reduceBEq, BitVec.reduceULT, Nat.reduceAdd, Nat.reduceMul, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    unbyte64, $hs,*])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The compiled comparison is equality, and constant-time.** Called with the addresses of two
hashes in RDI and RSI, the sixteen bytes around the stack pointer owned and neither hash in them:
it returns with 1 in AL if the 32 bytes are equal and 0 if not, the stack pointer popped, RBX and RBP
as they were, no byte changed but the eight below the stack pointer, and an observer's trace
`eqLeak` of the three addresses: the same whatever the hashes are. -/
theorem hash_eq_is_equality (pa pb rsp : BitVec 64) (A B : BitVec 64 → BitVec 8) (m : Mem)
    (rax rcx rdx rbx rbp r8 r9 : BitVec 64) (x0 x1 x2 x3 : BitVec 128) (zf cf : Option Bool) (leak : List Obs)
    (hA : ∀ c : BitVec 64, c.ult 32#64 = true → m (pa + c) = some (A c))
    (hB : ∀ c : BitVec 64, c.ult 32#64 = true → m (pb + c) = some (B c))
    (hS : ∀ d : BitVec 64, inS d = true → (m (rsp + d)).isSome = true)
    (hra : ∀ k : BitVec 64, k.ult 8#64 = true → m (rsp + k) = some 0#8)
    (aA : ∀ c : BitVec 64, c.ult 32#64 = true → inS (pa + c - rsp) = false)
    (aB : ∀ c : BitVec 64, c.ult 32#64 = true → inS (pb + c - rsp) = false) :
    ∃ s', Returns Code.prog ⟨rax, rcx, rdx, rbx, rsp, rbp, pb, pa, r8, r9, x0, x1, x2, x3, zf, cf, m, 0x1000, leak⟩ s' ∧
      s'.rax.setWidth 8 = (if bytesOf A = bytesOf B then 1#8 else 0#8) ∧
      s'.rsp = rsp + 8#64 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧
      (∀ x, inS (x - rsp) = false → s'.mem x = m x) ∧
      s'.leak = eqLeak pa pb rsp ++ leak := by
  let mm (fS : Written) : Mem := over m rsp inS fS
  have hm : m = mm none' := by simp only [mm, over_none]
  have wS : ∀ (fS : Written) (d : BitVec 64) (v : BitVec 8), inS d = true → (mm fS).put8 (rsp + d) v = mm (upd fS d v) := by
    intro fS d v hd; simp only [mm]; rw [put8_over_in _ _ _ _ _ _ hd]
  have rS : ∀ (fS : Written) (d : BitVec 64), inS d = true → mm fS (rsp + d) = (fS d).or (m (rsp + d)) := by
    intro fS d hd; simp only [mm]; rw [over_in _ _ _ _ _ hd]
  have rA : ∀ (fS : Written) (c : BitVec 64), c.ult 32#64 = true → mm fS (pa + c) = some (A c) := by
    intro fS c hc; simp only [mm]; rw [over_out _ _ _ _ _ (aA c hc), hA c hc]
  have rB : ∀ (fS : Written) (c : BitVec 64), c.ult 32#64 = true → mm fS (pb + c) = some (B c) := by
    intro fS c hc; simp only [mm]; rw [over_out _ _ _ _ _ (aB c hc), hB c hc]
  have hrun : ∃ s', steps Code.prog 14 ⟨rax, rcx, rdx, rbx, rsp, rbp, pb, pa, r8, r9, x0, x1, x2, x3, zf, cf, mm none', 0x1000, leak⟩ = some s' ∧
      s'.pc = done ∧ s'.rax.setWidth 8 = (if bytesOf A = bytesOf B then 1#8 else 0#8) ∧
      s'.rsp = rsp + 8#64 ∧ s'.rbx = rbx ∧ s'.rbp = rbp ∧ (∃ fS, s'.mem = mm fS) ∧
      s'.leak = eqLeak pa pb rsp ++ leak := by
    run_eq [wS, rS, rA, rB, hS, hra]
    refine ⟨_, rfl, rfl, ?_, rfl, rfl, rfl, ⟨_, rfl⟩, ?_⟩
    · by_cases hEq : bytesOf A = bytesOf B
      · rw [if_pos hEq]
        simp only [bytesOf, List.cons.injEq, and_true] at hEq
        obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hEq
        simp only [pcmpeqb, pmovmskb, eqByte]
        bv_decide
      · rw [if_neg hEq]
        simp only [bytesOf, List.cons.injEq, and_true] at hEq
        simp only [pcmpeqb, pmovmskb, eqByte]
        bv_decide
    · simp only [eqLeak, List.cons_append, List.nil_append]
      rfl
  obtain ⟨s', hs, hpc, hal, hsp, hbx, hbp, ⟨fS, hmem⟩, hleak⟩ := hrun
  rw [← hm] at hs
  refine ⟨s', ⟨14, hs, hpc⟩, hal, hsp, hbx, hbp, ?_, hleak⟩
  intro x hx
  rw [hmem]
  simp only [mm]
  rw [over_out _ _ _ _ _ hx]

#print axioms hash_eq_is_equality
