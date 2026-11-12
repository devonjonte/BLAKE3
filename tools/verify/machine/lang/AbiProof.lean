import Abi
import Hoare
open X86

/-! # From the compiler's pieces to `Abi.Meets`

`Abi.Meets` (what a reader reads) says nothing of frames. The compiler's proof works with the frame's
lowest address `fb`, the values of the registers a callee keeps, and the memory at entry, as names.
`Pre` and `Post` are a contract in those terms, and `meets_of_triple` (proved here, once, for any
function) says that is enough. Not to be read: Lean checks it. -/

namespace Abi

/-- The registers a callee keeps, as they were at the call. -/
structure Saved where
  rbx : BitVec 64
  rbp : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64

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

theorem meets_of_triple {prog : Nat → Option (Instr × Nat)} {entry : Nat} {c : Contract}
    (h : ∀ fb ra sv m0, Hoare.Triple prog (Pre entry c fb ra sv m0) (Post c fb ra sv m0)) : Meets prog entry c := by
  intro s ra hpc hargs hra hstack hap hreq
  have e : s.rsp - c.stack + c.stack = s.rsp := BitVec.sub_add_cancel ..
  obtain ⟨k, s', hrun, hpc', hsp', hbx, hbp, h12, h13, h14, h15, hout, hens⟩ :=
    h (s.rsp - c.stack) ra ⟨s.rbx, s.rbp, s.r12, s.r13, s.r14, s.r15⟩ s.mem s
      ⟨hpc, e.symm, hargs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hstack, by rw [e]; exact hra, hap, hreq⟩
  exact ⟨k, s', hrun, hpc', by rw [hsp', e], hbx, hbp, h12, h13, h14, h15, hens, hout⟩

end Abi
