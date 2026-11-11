import X86
import Code
import Sym
import Theirs

open X86

/-! # The compiled `Params::new` of `zakura-equihash 4.0.0` is equihash-lean's `Params.new?`

The thirty instructions rustc 1.99.1 makes of `Params::new` (release build, x86-64), run on the
model of `X86.lean`, against the Lean function craftsoldier/equihash-lean transcribed from the
Rust by hand. -/

/-- A call of `Params::new(n, k)`: `out` (RDI) is where the `Option<Params>` goes, `n` is ESI, `k`
is EDX; the upper halves of RSI and RDX are whatever the caller left. Any other registers; the
return address on the stack. -/
def entry (rax rcx rdx rbx rsp rbp rsi rdi r8 : BitVec 64) : State :=
  { rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, zf := none, cf := none, mem := store [] (rsp + 0) 0 64, pc := 0x1D50 }

/-- What a caller sees on return: RAX, the stack pointer, the registers the convention keeps, and
the three words at `out`: the tag, `n`, `k` (`none` for a word the function did not write). -/
def seen (out : BitVec 64) (s : State) :=
  (s.rax, s.rsp, s.rbx, s.rbp, load s.mem (out + 0) 32, load s.mem (out + 4) 32, load s.mem (out + 8) 32)

/-- The Rust's condition on two `u32`s, as the machine computes with them. -/
def accepts (n k : BitVec 32) : Bool :=
  n % 8 == 0 && (3 : BitVec 32).ule k && k.ult n && n % (k + 1) == 0 && n.ule 512 &&
    (8 : BitVec 32).ule (n / (k + 1)) && (n / (k + 1)).ule 24

theorem bind_ite {α β : Type} (c : Prop) [Decidable c] (a b : Option α) (f : α → Option β) :
    (if c then a else b).bind f = if c then a.bind f else b.bind f := by
  split <;> rfl

macro "run_code" : tactic => `(tactic|
  simp (config := {maxSteps := 10000000, implicitDefEqProofs := false}) (disch := decide) only [entry, Sym.run_mk, Sym.run_zero, step,
    X86.read, write, State.get, State.set, trunc, store, load, byteAt, byte, done, logic, holds,
    code_at, bind_ite, seen, *,
    Sym.join64, Sym.sub_lit, Sym.add_add, Sym.eq_add_add, Sym.eq_self_add, Sym.eq_add_self, Sym.run_ite, Sym.run_bite,
    Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.pure_def, Option.map_some, Option.map_none, bind_pure_comp,
    List.lookup_cons, List.lookup_nil,
    Nat.reduceEqDiff, Nat.reduceMul, ↓reduceIte, BitVec.reduceAdd, BitVec.reduceNeg, BitVec.reduceEq, BitVec.reduceBEq,
    BitVec.reduceAnd, BitVec.reduceHShiftRight, BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat, BitVec.reduceHShiftLeft,
    BitVec.reduceOr, BitVec.reduceToNat, reduceCtorEq, beq_self_eq_true, Bool.not_false, Bool.not_true, Sym.map_ite,
    BitVec.xor_self, true_and, and_true, and_self])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The machine's side.** From any registers, with the twelve bytes at `out` apart from the
sixteen bytes of stack the function uses (its return address and the saved RBP), the thirty instructions return without a fault (no
division by zero among them), RAX is `out`, the stack pointer is popped, RBX and RBP are as they
were, and at `out` the tag is 1 with `n` and `k` after it exactly when `accepts n k`, and
otherwise the tag is 0 and the other two words are not written. -/
theorem params_new_code (cpu : Cpu) (rax rcx rdx rbx rsp rbp rsi out r8 : BitVec 64)
    (hsep : ∀ c d : BitVec 64, (c + 8).ult 16 = true → d.ult 12 = true → (rsp + c == out + d) = false) :
    (run Code.prog cpu 40 (entry rax rcx rdx rbx rsp rbp rsi out r8)).map (seen out) =
      some (out, rsp + 8, rbx, rbp,
        some (if accepts (rsi.setWidth 32) (rdx.setWidth 32) then 1 else 0),
        if accepts (rsi.setWidth 32) (rdx.setWidth 32) then some (rsi &&& 0xFFFFFFFF) else none,
        if accepts (rsi.setWidth 32) (rdx.setWidth 32) then some (rdx &&& 0xFFFFFFFF) else none) := by
  have hsep' : ∀ c d : BitVec 64, (c + 8).ult 16 = true → d.ult 12 = true → (out + d == rsp + c) = false :=
    fun c d hc hd => by rw [BEq.comm]; exact hsep c d hc hd
  run_code
  clear hsep hsep'
  repeat' split
  all_goals (simp only [accepts, Option.some.injEq, Prod.mk.injEq] at *)
  all_goals bv_decide (config := { timeout := 900 })

#print axioms params_new_code
