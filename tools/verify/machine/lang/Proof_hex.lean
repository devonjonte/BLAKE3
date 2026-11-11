import Machine
import MemLemmas
import Observer
import HexSpec
import Code_hex
open X86

/-! # The kernel `hex` meets its contract

Written by prove.py from the contract in the source. The statement is the contract; the proof is the
recipe for a straight-line kernel. Lean checks both. -/

theorem vec_as {m : Mem} {a : BitVec 64} {v w : V} (h : Vec m a v) (e : v = w) : Vec m a w := e ▸ h

theorem put_0 (mem : Mem) (out : BitVec 64) (v0 v1 v2 v3 : V) : Vec ((((mem.put128 (out + 0) v0).put128 (out + 16) v1).put128 (out + 32) v2).put128 (out + 48) v3) (out + 0) v0 := by
  exact vec_congr (fun x hx => put128_other _ _ _ x (by bv_omega)) (vec_congr (fun x hx => put128_other _ _ _ x (by bv_omega)) (vec_congr (fun x hx => put128_other _ _ _ x (by bv_omega)) (vec_put128 mem (out + 0) v0)))

theorem put_1 (mem : Mem) (out : BitVec 64) (v0 v1 v2 v3 : V) : Vec ((((mem.put128 (out + 0) v0).put128 (out + 16) v1).put128 (out + 32) v2).put128 (out + 48) v3) (out + 16) v1 := by
  exact vec_congr (fun x hx => put128_other _ _ _ x (by bv_omega)) (vec_congr (fun x hx => put128_other _ _ _ x (by bv_omega)) (vec_put128 (mem.put128 (out + 0) v0) (out + 16) v1))

theorem put_2 (mem : Mem) (out : BitVec 64) (v0 v1 v2 v3 : V) : Vec ((((mem.put128 (out + 0) v0).put128 (out + 16) v1).put128 (out + 32) v2).put128 (out + 48) v3) (out + 32) v2 := by
  exact vec_congr (fun x hx => put128_other _ _ _ x (by bv_omega)) (vec_put128 ((mem.put128 (out + 0) v0).put128 (out + 16) v1) (out + 32) v2)

theorem put_3 (mem : Mem) (out : BitVec 64) (v0 v1 v2 v3 : V) : Vec ((((mem.put128 (out + 0) v0).put128 (out + 16) v1).put128 (out + 32) v2).put128 (out + 48) v3) (out + 48) v3 := by
  exact vec_put128 (((mem.put128 (out + 0) v0).put128 (out + 16) v1).put128 (out + 32) v2) (out + 48) v3

theorem put_frame (mem : Mem) (out : BitVec 64) (v0 v1 v2 v3 : V) (x : BitVec 64) (hx : 64 ≤ (x - out).toNat) :
    ((((mem.put128 (out + 0) v0).put128 (out + 16) v1).put128 (out + 32) v2).put128 (out + 48) v3) x = mem x := by
  rw [put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)]

set_option maxRecDepth 100000 in
macro "run_hex" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [stepsL_mk, stepsL_zero, stepL, touched, srcObs, opObs, branches,
    step, src, X86.read, write, State.get, State.set, State.xmm, State.setx, trunc, hex_at,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp, Option.isSome_some,
    List.nil_append, List.cons_append, List.append_nil,
    Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte, reduceCtorEq, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceEq, BitVec.reduceBEq,
    BitVec.reduceAnd, BitVec.reduceSetWidth, Bool.false_eq_true, Bool.true_eq_false, Bool.false_and, Bool.true_and,
    Bool.not_true, Bool.not_false, $hs,*])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The 45 instructions of `hex` meet its contract.** Called with the address of 32 bytes in RSI (the vectors
h0, h1) and of 64 owned bytes in RDI, the return address on the stack and apart from those 64 bytes: it returns
there with the stack pointer popped and the registers a callee keeps as they were; the 64 bytes are
Hex.hex8 h0 0, Hex.hex8 h0 8, Hex.hex8 h1 0, Hex.hex8 h1 8; no other byte of memory changes;
and what an observer sees is `L`, a list fixed by the two addresses, the stack pointer and the return address,
whatever h0, h1 are. -/
theorem hex_meets_its_contract (out inp rsp ra : BitVec 64) : ∃ L : List Obs, ∀ (s : State) (h0 h1 : V),
    s.pc = 0x50000 → s.rdi = out → s.rsi = inp → s.rsp = rsp →
    Vec s.mem (inp + 0) h0 → Vec s.mem (inp + 16) h1 →
    Owned16 s.mem (out + 0) → Owned16 s.mem (out + 16) → Owned16 s.mem (out + 32) → Owned16 s.mem (out + 48) →
    s.mem.read rsp 64 = some ra → (∀ x, (x - rsp).toNat < 8 → 64 ≤ (x - out).toNat) →
    ∃ S, stepsL Code_hex.prog 45 ⟨s, []⟩ = some S ∧ S.leak = L ∧
      S.core.pc = ra.toNat ∧ S.core.rsp = rsp + 8 ∧
      S.core.rbx = s.rbx ∧ S.core.rbp = s.rbp ∧ S.core.r12 = s.r12 ∧ S.core.r13 = s.r13 ∧ S.core.r14 = s.r14 ∧ S.core.r15 = s.r15 ∧
      Vec S.core.mem (out + 0) (Hex.hex8 h0 0) ∧
      Vec S.core.mem (out + 16) (Hex.hex8 h0 8) ∧
      Vec S.core.mem (out + 32) (Hex.hex8 h1 0) ∧
      Vec S.core.mem (out + 48) (Hex.hex8 h1 8) ∧
      (∀ x, 64 ≤ (x - out).toNat → S.core.mem x = s.mem x) := by
  refine ⟨?L, ?_⟩
  rotate_left
  intro s h0 h1 hpc hout hinp hsp hr0 hr1 ho0 ho1 ho2 ho3 hret hapart
  obtain ⟨rax, rcx, rdx, rbx, rsp_, rbp, rsi_, rdi_, r8, r9, r12, r13, r14, r15, zf, cf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, mem, pc⟩ := s
  simp only at hpc hout hinp hsp hr0 hr1 ho0 ho1 ho2 ho3 hret hapart
  subst pc rdi_ rsi_ rsp_
  have r0 := read_vec hr0
  have r1 := read_vec hr1
  have w0 : ∀ v : V, mem.write128 (out + 0) v = some (mem.put128 (out + 0) v) :=
    fun v => write_vec ho0 v
  have w1 : ∀ v0 v : V, (mem.put128 (out + 0) v0).write128 (out + 16) v = some ((mem.put128 (out + 0) v0).put128 (out + 16) v) :=
    fun v0 v => write_vec (owned16_put128 _ _ _ _ ho1) v
  have w2 : ∀ v0 v1 v : V, ((mem.put128 (out + 0) v0).put128 (out + 16) v1).write128 (out + 32) v = some (((mem.put128 (out + 0) v0).put128 (out + 16) v1).put128 (out + 32) v) :=
    fun v0 v1 v => write_vec (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ ho2)) v
  have w3 : ∀ v0 v1 v2 v : V, (((mem.put128 (out + 0) v0).put128 (out + 16) v1).put128 (out + 32) v2).write128 (out + 48) v = some ((((mem.put128 (out + 0) v0).put128 (out + 16) v1).put128 (out + 32) v2).put128 (out + 48) v) :=
    fun v0 v1 v2 v => write_vec (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ (owned16_put128 _ _ _ _ ho3))) v
  have rr : ∀ v0 v1 v2 v3 : V, ((((mem.put128 (out + 0) v0).put128 (out + 16) v1).put128 (out + 32) v2).put128 (out + 48) v3).read rsp 64 = some ra := by
    intro v0 v1 v2 v3
    rw [read_congr (m := mem) _ (fun x hx => by
      have := hapart x hx
      rw [put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega), put128_other _ _ _ _ (by bv_omega)])]
    exact hret
  run_hex [r0, r1, w0, w1, w2, w3, rr]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    rfl
  · refine vec_as (put_0 _ _ _ _ _ _) ?_
    simp only [Hex.hex8, Hex.hi, Hex.lo, Hex.hexc, paddb, pcmpgtb, gtb, punpcklbw, punpckhbw, psrlw, by8, w16]
    bv_decide (config := { timeout := 900 })
  · refine vec_as (put_1 _ _ _ _ _ _) ?_
    simp only [Hex.hex8, Hex.hi, Hex.lo, Hex.hexc, paddb, pcmpgtb, gtb, punpcklbw, punpckhbw, psrlw, by8, w16]
    bv_decide (config := { timeout := 900 })
  · refine vec_as (put_2 _ _ _ _ _ _) ?_
    simp only [Hex.hex8, Hex.hi, Hex.lo, Hex.hexc, paddb, pcmpgtb, gtb, punpcklbw, punpckhbw, psrlw, by8, w16]
    bv_decide (config := { timeout := 900 })
  · refine vec_as (put_3 _ _ _ _ _ _) ?_
    simp only [Hex.hex8, Hex.hi, Hex.lo, Hex.hexc, paddb, pcmpgtb, gtb, punpcklbw, punpckhbw, psrlw, by8, w16]
    bv_decide (config := { timeout := 900 })
  · intro x hx
    exact put_frame _ _ _ _ _ _ x hx

#print axioms hex_meets_its_contract
