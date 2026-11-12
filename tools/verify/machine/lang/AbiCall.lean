import AbiProof
import Dom
open X86 Cells

/-! # Calling a function by its contract (not to be read)

A function of ours that calls another uses nothing of the callee but `Abi.Meets … contract`: whatever code
meets the contract may stand there. `Abi.Meets.mono` carries a callee's theorem into the caller's program
(which holds the callee's instructions and more); `Abi.call_meets` is the step a caller's proof takes at
the call: what the contract asks is shown of the state at the callee's first instruction, and the run
goes on from the state at the return, of which the contract's promises are known. -/

namespace Abi

/-- A function that meets its contract in a program meets it in any program that has those instructions. -/
theorem Meets.mono {p q : Nat → Option (Instr × Nat)} {entry : Nat} {c : Contract}
    (h : ∀ pc x, p pc = some x → q pc = some x) (hm : Meets p entry c) : Meets q entry c := by
  intro s ra hpc hargs hra hstack hap hacc hreq
  obtain ⟨k, s', hrun, rest⟩ := hm s ra hpc hargs hra hstack hap hacc hreq
  exact ⟨k, s', steps_mono h k s s' hrun, rest⟩

/-- **At a call:** the state is at the callee's first instruction (the return address just pushed). If it
gives the callee what its contract asks, the run goes on from a state at the return address of which the
contract's promises hold; and what was the program's memory still is (`steps_dom`: no instruction maps or
unmaps), the stack it lent included. -/
theorem call_meets {prog : Nat → Option (Instr × Nat)} {entry : Nat} {c : Contract} (hm : Meets prog entry c)
    {s : State} {ra : BitVec 64} {Q : State → Prop}
    (hpc : s.pc = entry)
    (hargs : c.args = [s.rdi, s.rsi, s.rdx, s.rcx, s.r8, s.r9].take c.args.length)
    (hra : Quad s.mem s.rsp ra)
    (hstack : Cells.Region s.mem (s.rsp - c.stack) c.stack)
    (hap : AllApart ((s.rsp - c.stack, c.stack + 8#64) :: c.regions))
    (hacc : c.accepts) (hreq : c.requires s.mem)
    (next : ∀ s' : State, s'.pc = ra.toNat → s'.rsp = s.rsp + 8#64 →
      s'.rbx = s.rbx → s'.rbp = s.rbp → s'.r12 = s.r12 → s'.r13 = s.r13 → s'.r14 = s.r14 → s'.r15 = s.r15 →
      c.ensures s'.rax s'.mem →
      (∀ x : BitVec 64, c.stack + 8#64 ≤ x - (s.rsp - c.stack) → (∀ r ∈ c.modifies, r.2 ≤ x - r.1) → s'.mem x = s.mem x) →
      (∀ b n : BitVec 64, Cells.Region s.mem b n → Cells.Region s'.mem b n) →
      Runs prog s' Q) :
    Runs prog s Q := by
  obtain ⟨k, s', hrun, hpc', hsp', hbx, hbp, h12, h13, h14, h15, hens, hout⟩ := hm s ra hpc hargs hra hstack hap hacc hreq
  have hdom := steps_dom prog k s s' hrun
  exact runs_then hrun (next s' hpc' hsp' hbx hbp h12 h13 h14 h15 hens hout
    (fun b n hr d hd => by rw [hdom (b + d)]; exact hr d hd))

end Abi
