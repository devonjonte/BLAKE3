import Machine
import MemLemmas
import Cells
open X86

/-! # What it means for a function to meet a contract

Read once; every function's contract is written with it. Definitions only. (`@[abi]` marks what a proof
opens to see what a contract says; it changes no meaning.) -/

namespace Abi

/-- The `n` bytes at `a` and the `k` bytes at `b` do not overlap: `b` is at least `n` past `a`, and
`a` at least `k` past `b` (addresses wrap around at 2^64). -/
def Apart (a n b k : BitVec 64) : Prop := n ≤ b - a ∧ k ≤ a - b

/-- Regions (address, size), each apart from every other. -/
def AllApart : List (BitVec 64 × BitVec 64) → Prop
  | [] => True
  | r :: rest => (∀ q ∈ rest, Apart r.1 r.2 q.1 q.2) ∧ AllApart rest

/-- A kind of thing in memory: how many bytes it takes, and what it means for memory to hold the value `v`
of it at the address `a`. -/
structure Layout (α : Type) where
  size : BitVec 64
  holds : Mem → BitVec 64 → α → Prop

/-- A piece of memory a contract speaks of: where it is, how big, and what it holds at the call and at the
return. -/
structure Piece where
  addr : BitVec 64
  size : BitVec 64
  before : Mem → Prop
  after : Mem → Prop

/-- The thing at `a` holds `v`, and the function leaves it so. -/
@[abi] def Layout.keeps {α : Type} (l : Layout α) (a : BitVec 64) (v : α) : Piece :=
  ⟨a, l.size, fun m => l.holds m a v, fun m => l.holds m a v⟩

/-- The thing at `a` holds `v` at the call and `w` at the return. -/
@[abi] def Layout.turns {α : Type} (l : Layout α) (a : BitVec 64) (v w : α) : Piece :=
  ⟨a, l.size, fun m => l.holds m a v, fun m => l.holds m a w⟩

/-- What a caller owes a function and what it gets. -/
structure Contract where
  /-- The arguments, in order (at most six). -/
  args : List (BitVec 64)
  /-- Bytes of stack below the stack pointer the function may use. -/
  stack : BitVec 64
  /-- What must hold of the arguments themselves. A caller shows it, or calls the function's checked entry
  (`Contract.checked`), which tests it. -/
  accepts : Prop
  /-- Memory the function is given and does not change. -/
  reads : List Piece
  /-- Memory the function is given and may change: nothing else, but its own stack. -/
  updates : List Piece
  /-- What holds of the result. -/
  returns : BitVec 64 → Prop

/-- The memory the contract speaks of, as (address, size): apart from one another and from the stack. -/
@[abi] def Contract.regions (c : Contract) : List (BitVec 64 × BitVec 64) := (c.updates ++ c.reads).map fun p => (p.addr, p.size)
/-- What must hold of memory at the call. No code can test this: a caller shows it. -/
@[abi] def Contract.requires (c : Contract) (m : Mem) : Prop := ∀ p ∈ c.updates ++ c.reads, p.before m
/-- What holds of the result and of memory at the return. -/
@[abi] def Contract.ensures (c : Contract) (result : BitVec 64) (m : Mem) : Prop := c.returns result ∧ ∀ p ∈ c.updates, p.after m
/-- The only memory, as (address, size), that may differ at the return (besides the stack below the stack pointer). -/
@[abi] def Contract.modifies (c : Contract) : List (BitVec 64 × BitVec 64) := c.updates.map fun p => (p.addr, p.size)

/-- **The function at `entry` of `prog` meets the contract `c`.** From any state at its first instruction
with the arguments in the registers the System V calling convention names, the return address on the
stack, `c.stack` bytes below it free, the stack and the contract's pieces of memory apart, `c.accepts` of
the arguments and every piece holding what the contract says: the instructions run, without a fault, to
that return address, with the stack pointer popped, the registers a callee must keep as they were,
`c.returns` of RAX, every piece the function may change holding what the contract says, and every byte
outside those pieces and the stack below the stack pointer as it was. -/
def Meets (prog : Nat → Option (Instr × Nat)) (entry : Nat) (c : Contract) : Prop :=
  ∀ (s : State) (ra : BitVec 64),
    s.pc = entry →
    c.args = [s.rdi, s.rsi, s.rdx, s.rcx, s.r8, s.r9].take c.args.length →
    Quad s.mem s.rsp ra →
    Cells.Region s.mem (s.rsp - c.stack) c.stack →
    AllApart ((s.rsp - c.stack, c.stack + 8#64) :: c.regions) →
    c.accepts → c.requires s.mem →
    ∃ k s', steps prog k s = some s' ∧
      s'.pc = ra.toNat ∧ s'.rsp = s.rsp + 8#64 ∧
      s'.rbx = s.rbx ∧ s'.rbp = s.rbp ∧ s'.r12 = s.r12 ∧ s'.r13 = s.r13 ∧ s'.r14 = s.r14 ∧ s'.r15 = s.r15 ∧
      c.ensures s'.rax s'.mem ∧
      ∀ x : BitVec 64, c.stack + 8#64 ≤ x - (s.rsp - c.stack) → (∀ r ∈ c.modifies, r.2 ≤ x - r.1) → s'.mem x = s.mem x

/-- **The contract of a function's checked entry.** Any arguments are accepted. Where the function's own
contract `c` accepts them, the checked entry does as `c` says; where it does not, the checked entry returns
`refused`, and every piece of memory holds what it held at the call. -/
def Contract.checked (c : Contract) (refused : BitVec 64) : Contract :=
  { c with
    accepts := True
    returns := fun result => (c.accepts → c.returns result) ∧ (¬ c.accepts → result = refused)
    updates := c.updates.map fun p =>
      { p with after := fun m => (c.accepts → p.after m) ∧ (¬ c.accepts → p.before m) } }

end Abi
