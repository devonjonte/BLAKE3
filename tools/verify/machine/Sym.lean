import X86
open X86

/-! Lemmas for running a program on unknown inputs: addresses are a base plus a constant. -/

namespace Sym

theorem sub_lit (a c : BitVec 64) : a - c = a + (-c) := by bv_decide
theorem add_add (a c d : BitVec 64) : a + c + d = a + (c + d) := by bv_decide
theorem eq_add_add (a c d : BitVec 64) : (a + c == a + d) = (c == d) := by bv_decide
theorem eq_self_add (a d : BitVec 64) : (a == a + d) = (0 == d) := by bv_decide
theorem eq_add_self (a c : BitVec 64) : (a + c == a) = (c == 0) := by bv_decide

/-- A 64-bit value stored and loaded again is itself, as a term: so a pointer the code saves on the
stack and restores (a frame register) is still `base + constant` when it is next used as an address. -/
theorem join64 (v : BitVec 64) :
    (BitVec.setWidth 64 (BitVec.setWidth 8 (v >>> 0)) ||| BitVec.setWidth 64 (BitVec.setWidth 8 (v >>> 8)) <<< 8 |||
      BitVec.setWidth 64 (BitVec.setWidth 8 (v >>> 16)) <<< 16 ||| BitVec.setWidth 64 (BitVec.setWidth 8 (v >>> 24)) <<< 24 |||
      BitVec.setWidth 64 (BitVec.setWidth 8 (v >>> 32)) <<< 32 ||| BitVec.setWidth 64 (BitVec.setWidth 8 (v >>> 40)) <<< 40 |||
      BitVec.setWidth 64 (BitVec.setWidth 8 (v >>> 48)) <<< 48 ||| BitVec.setWidth 64 (BitVec.setWidth 8 (v >>> 56)) <<< 56) = v := by
  bv_decide

theorem run_ite (prog : Nat → Option (Instr × Nat)) (cpu : Cpu) (n : Nat) (c : Prop) [Decidable c] (a b : State) :
    run prog cpu n (if c then a else b) = if c then run prog cpu n a else run prog cpu n b := by
  split <;> rfl

theorem run_bite (prog : Nat → Option (Instr × Nat)) (cpu : Cpu) (n : Nat) (c : Bool) (a b : State) :
    run prog cpu n (bif c then a else b) = bif c then run prog cpu n a else run prog cpu n b := by
  cases c <;> rfl

/-- One instruction, where the state is written out (so never under a binder, on a state not yet known). -/
theorem run_mk (prog : Nat → Option (Instr × Nat)) (cpu : Cpu) (n : Nat) (rax rcx rdx rbx rsp rbp rsi rdi : BitVec 64)
    (zf cf : Option Bool) (mem : List (BitVec 64 × BitVec 8)) (pc : Nat) :
    run prog cpu (n + 1) ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, zf, cf, mem, pc⟩ =
      if pc = done then some ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, zf, cf, mem, pc⟩
      else match prog pc with
        | none => none
        | some (i, next) => (step cpu i next ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, zf, cf, mem, pc⟩).bind (run prog cpu n) := rfl

theorem run_zero (prog : Nat → Option (Instr × Nat)) (cpu : Cpu) (s : State) : run prog cpu 0 s = none := rfl

theorem map_ite {α β : Type} (f : α → β) (c : Prop) [Decidable c] (a b : Option α) :
    (if c then a else b).map f = if c then a.map f else b.map f := by
  split <;> rfl

end Sym
