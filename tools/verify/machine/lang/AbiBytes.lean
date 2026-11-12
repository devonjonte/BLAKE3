import Abi
import Spec_bytes
import Contract
open X86

/-! # A contract that names no machine, as a contract of this one

Read once. Definitions only. A `Bytes.Contract` (`../spec/Contract.lean`) says what a function is given and
leaves, of bytes at addresses. Here: what that says of this model's memory, so that `Abi.Meets` (System V,
`Abi.lean`) applies to it. -/

namespace Abi

/-- A piece said of bytes, as a piece of this model's memory: the bytes at its address, as many as its
size, are bytes of which the piece's statement holds. -/
def Piece.ofBytes (p : Bytes.Piece) : Piece :=
  ⟨p.addr, BitVec.ofNat 64 p.size,
    fun m => ∃ b, b.length = p.size ∧ Bytes.At m p.addr b ∧ p.before b,
    fun m => ∃ b, b.length = p.size ∧ Bytes.At m p.addr b ∧ p.after b⟩

/-- The contract `c`, for this machine, with `stack` bytes of stack the code may use. -/
def ofBytes (c : Bytes.Contract) (stack : BitVec 64) : Contract where
  args := c.args
  stack := stack
  accepts := c.accepts
  reads := c.reads.map Piece.ofBytes
  updates := c.updates.map Piece.ofBytes
  returns := c.returns

end Abi
