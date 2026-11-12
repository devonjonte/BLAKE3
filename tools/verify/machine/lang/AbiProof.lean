import Abi
import Hoare
open X86

/-! # From the compiler's pieces to `Abi.Meets`

`Abi.Meets` (what a reader reads) says nothing of frames, and gives the function a budget of stack.
The compiler's proof works with the frame it really made: its size `F`, its lowest address `fb`, the
values of the registers a callee keeps, and the memory at entry, as names. `Pre` and `Post` are the
contract in those terms, and `meets_of_triple` (proved here, once, for any function) says that is
enough, as long as the frame is within the budget. Not to be read: Lean checks it. -/

namespace Abi

/-- The registers a callee keeps, as they were at the call. -/
structure Saved where
  rbx : BitVec 64
  rbp : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64

/-- The contract with the stack the compiled function really uses. -/
def Contract.framed (c : Contract) (F : BitVec 64) : Contract := { c with stack := F }

def Pre (entry : Nat) (c : Contract) (fb ra : BitVec 64) (sv : Saved) (m0 : Mem) (s : State) : Prop :=
  s.pc = entry ∧ s.rsp = fb + c.stack ∧
  c.args = [s.rdi, s.rsi, s.rdx, s.rcx, s.r8, s.r9].take c.args.length ∧
  s.rbx = sv.rbx ∧ s.rbp = sv.rbp ∧ s.r12 = sv.r12 ∧ s.r13 = sv.r13 ∧ s.r14 = sv.r14 ∧ s.r15 = sv.r15 ∧
  s.mem = m0 ∧ Cells.Region m0 fb c.stack ∧ Quad m0 (fb + c.stack) ra ∧
  AllApart ((fb, c.stack + 8#64) :: c.regions) ∧ c.requires m0

def Post (c : Contract) (fb ra : BitVec 64) (sv : Saved) (m0 : Mem) (s : State) : Prop :=
  s.pc = ra.toNat ∧ s.rsp = fb + c.stack + 8#64 ∧
  s.rbx = sv.rbx ∧ s.rbp = sv.rbp ∧ s.r12 = sv.r12 ∧ s.r13 = sv.r13 ∧ s.r14 = sv.r14 ∧ s.r15 = sv.r15 ∧
  (∀ x : BitVec 64, c.stack + 8#64 ≤ x - fb → (∀ r ∈ c.modifies, r.2 ≤ x - r.1) → s.mem x = m0 x) ∧
  c.ensures s.rax s.mem

theorem apart_shrink {a S F : BitVec 64} (hF : F ≤ S) (hS : S ≤ 0x100000#64) {q : BitVec 64 × BitVec 64}
    (h : Apart a (S + 8#64) q.1 q.2) : Apart (a + (S - F)) (F + 8#64) q.1 q.2 := by
  obtain ⟨h1, h2⟩ := h
  constructor <;> bv_omega

/-- A function proved with a frame of `F` bytes meets its contract when `F` is within the contract's budget. -/
theorem meets_of_triple {prog : Nat → Option (Instr × Nat)} {entry : Nat} {c : Contract} (F : BitVec 64)
    (hF : F ≤ c.stack) (hS : c.stack ≤ 0x100000#64)
    (h : ∀ fb ra sv m0, Hoare.Triple prog (Pre entry (c.framed F) fb ra sv m0) (Post (c.framed F) fb ra sv m0)) :
    Meets prog entry c := by
  intro s ra hpc hargs hra hstack hap hreq
  have e : s.rsp - F + F = s.rsp := BitVec.sub_add_cancel ..
  have ea : s.rsp - F = s.rsp - c.stack + (c.stack - F) := by bv_omega
  have hstack' : Cells.Region s.mem (s.rsp - F) F := by
    intro d hd
    have := hstack (c.stack - F + d) (by bv_omega)
    rw [show s.rsp - F + d = s.rsp - c.stack + (c.stack - F + d) by bv_omega]; exact this
  have hap' : AllApart ((s.rsp - F, F + 8#64) :: c.regions) := by
    obtain ⟨h1, h2⟩ := hap
    exact ⟨fun q hq => by rw [ea]; exact apart_shrink hF hS (h1 q hq), h2⟩
  obtain ⟨k, s', hrun, hpc', hsp', hbx, hbp, h12, h13, h14, h15, hout, hens⟩ :=
    h (s.rsp - F) ra ⟨s.rbx, s.rbp, s.r12, s.r13, s.r14, s.r15⟩ s.mem s
      ⟨hpc, e.symm, hargs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hstack', by show Quad s.mem (s.rsp - F + F) ra; rw [e]; exact hra, hap', hreq⟩
  refine ⟨k, s', hrun, hpc', ?_, hbx, hbp, h12, h13, h14, h15, hens, ?_⟩
  · rw [hsp']; show s.rsp - F + F + 8#64 = s.rsp + 8#64; rw [e]
  · intro x hx hmod
    exact hout x (by show F + 8#64 ≤ x - (s.rsp - F); bv_omega) hmod

end Abi
