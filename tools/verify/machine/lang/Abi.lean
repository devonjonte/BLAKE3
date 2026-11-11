import Machine
import MemLemmas
import Cells
open X86

/-! # What it means for a function to meet a contract

Read once; every function's statement is written with it. Definitions only. -/

namespace Abi

/-- The `n` bytes at `a` and the `k` bytes at `b` do not overlap: `b` is at least `n` past `a`, and
`a` at least `k` past `b` (addresses wrap around at 2^64). -/
def Apart (a n b k : BitVec 64) : Prop := n ≤ b - a ∧ k ≤ a - b

/-- Regions (address, size), each apart from every other. -/
def AllApart : List (BitVec 64 × BitVec 64) → Prop
  | [] => True
  | r :: rest => (∀ q ∈ rest, Apart r.1 r.2 q.1 q.2) ∧ AllApart rest

/-- What a caller owes a function and what it gets. -/
structure Contract where
  /-- The arguments, in order (at most six). -/
  args : List (BitVec 64)
  /-- Bytes of stack below the stack pointer the function may use. -/
  stack : BitVec 64
  /-- The memory the contract speaks of, as (address, size): apart from one another and from the stack. -/
  regions : List (BitVec 64 × BitVec 64)
  /-- What must hold of memory at the call. -/
  requires : Mem → Prop
  /-- What holds of the result and of memory at the return. -/
  ensures : BitVec 64 → Mem → Prop
  /-- The only memory, as (address, size), that may differ at the return (besides the stack below the stack pointer). -/
  modifies : List (BitVec 64 × BitVec 64)

/-- **The function at `entry` of `prog` meets the contract `c`.** From any state at its first instruction
with the arguments in the registers the System V calling convention names, the return address on the
stack, `c.stack` bytes below it free, the stack and the contract's regions apart, and `c.requires` of
memory: the instructions run, without a fault, to that return address, with the stack pointer popped,
the registers a callee must keep as they were, `c.ensures` of RAX and memory, and every byte outside the
stack below the stack pointer and `c.modifies` as it was. -/
def Meets (prog : Nat → Option (Instr × Nat)) (entry : Nat) (c : Contract) : Prop :=
  ∀ (s : State) (ra : BitVec 64),
    s.pc = entry →
    c.args = [s.rdi, s.rsi, s.rdx, s.rcx, s.r8, s.r9].take c.args.length →
    Quad s.mem s.rsp ra →
    Cells.Region s.mem (s.rsp - c.stack) c.stack →
    AllApart ((s.rsp - c.stack, c.stack + 8#64) :: c.regions) →
    c.requires s.mem →
    ∃ k s', steps prog k s = some s' ∧
      s'.pc = ra.toNat ∧ s'.rsp = s.rsp + 8#64 ∧
      s'.rbx = s.rbx ∧ s'.rbp = s.rbp ∧ s'.r12 = s.r12 ∧ s'.r13 = s.r13 ∧ s'.r14 = s.r14 ∧ s'.r15 = s.r15 ∧
      c.ensures s'.rax s'.mem ∧
      ∀ x : BitVec 64, c.stack + 8#64 ≤ x - (s.rsp - c.stack) → (∀ r ∈ c.modifies, r.2 ≤ x - r.1) → s'.mem x = s.mem x

end Abi
