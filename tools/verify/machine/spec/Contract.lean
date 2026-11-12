/-! # Contracts that name no machine

What a function is given and what it leaves, said of bytes at addresses. Definitions only. Each machine
model says once what it means for its code to meet such a contract (`../lang/AbiBytes.lean` for x86-64 on
our model, `../arm/ArmAbi.lean` for AArch64 on Google DeepMind's): where the arguments are, what "the bytes
at an address" are in its memory, and how much stack the code may use. -/

namespace Bytes

/-- A kind of thing in memory: how many bytes it takes, and what it means for bytes to hold the value `v`
of it. -/
structure Layout (α : Type) where
  size : Nat
  holds : List (BitVec 8) → α → Prop

/-- A piece of memory a contract speaks of: where it is, how many bytes, and what holds of those bytes at
the call and at the return. -/
structure Piece where
  addr : BitVec 64
  size : Nat
  before : List (BitVec 8) → Prop
  after : List (BitVec 8) → Prop

/-- The thing at `a` holds `v`, and the function leaves it so. -/
def Layout.keeps {α : Type} (l : Layout α) (a : BitVec 64) (v : α) : Piece := ⟨a, l.size, (l.holds · v), (l.holds · v)⟩

/-- The thing at `a` holds `v` at the call and `w` at the return. -/
def Layout.turns {α : Type} (l : Layout α) (a : BitVec 64) (v w : α) : Piece := ⟨a, l.size, (l.holds · v), (l.holds · w)⟩

/-- The thing at `a` holds `w` at the return; at the call the bytes there may be anything. -/
def Layout.fills {α : Type} (l : Layout α) (a : BitVec 64) (w : α) : Piece := ⟨a, l.size, fun _ => True, (l.holds · w)⟩

/-- What a caller owes a function and what it gets. -/
structure Contract where
  /-- The arguments, in order (at most six). -/
  args : List (BitVec 64)
  /-- What must hold of the arguments themselves. -/
  accepts : Prop
  /-- Memory the function is given and does not change. -/
  reads : List Piece
  /-- Memory the function is given and may change: nothing else, but its own stack. -/
  updates : List Piece
  /-- What holds of the result. -/
  returns : BitVec 64 → Prop

end Bytes
