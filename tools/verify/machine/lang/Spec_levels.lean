import Abi
import Spec_stack
open X86

/-! # The tree's levels in memory: what the statements of `ladd` and `lroot` speak of

Definitions only. The tree of chaining values another way than the stack (`../levels/levels.ode`). Each
level of the tree has two places, 32 bytes each, side by side; level 0 is the chunks' own.

The levels are a counter in binary. A level that has received an odd number of values holds the newest
of them, in its first place; each pair it received went, as the pair's parent, to the level above. And
the newest chunk of all waits at the bottom, in the place that is free: its turn to count comes when the
next chunk arrives (until then it may be the root's child). -/

namespace Levels

/-- **The levels from the address `a` upward, `f` of them, have received `r` values of `size` chunks each**
(whole subtrees of the specification's tree, in order from chunk 0): if `r` is odd this level holds the
newest of them in its first place, and the level above has received `r / 2` values of twice the size. -/
def Lev (k : Blake3.CV) (mode : Blake3.Word) (chunks : Array Blake3.Node) (m : Mem) : Nat → BitVec 64 → Nat → Nat → Prop
  | 0, _, _, r => r = 0
  | f + 1, a, size, r =>
    (r % 2 = 1 → Cv.At m a (Blake3.sub k mode chunks ((r - 1) * size) size)) ∧
    Lev k mode chunks m f (a + 64#64) (2 * size) (r / 2)

/-- Where in a level that has received `r` values the next one goes: the first place, or the second
(32 bytes on) if the first is in use. -/
def place (r : Nat) : BitVec 64 := if r % 2 = 1 then 32#64 else 0#64

/-- **Memory holds, at `lv`, the levels of the tree over `chunks`** (under a key and a mode): 3520 bytes
the program may use; the count of chunks in the first eight; the levels from byte 64, 64 bytes each, 54
of them; at most 2^54 chunks (what a message of 2^64 - 1 bytes has). With a chunk or more: the levels have received all the chunks but the
newest, and the newest chunk's value is in the bottom level's next place. -/
def At (k : Blake3.CV) (mode : Blake3.Word) (m : Mem) (lv : BitVec 64) (chunks : Array Blake3.Node) : Prop :=
  chunks.size ≤ 2 ^ 54 ∧ Cells.Region m lv 3520#64 ∧ Quad m lv (BitVec.ofNat 64 chunks.size) ∧
  (0 < chunks.size →
    Lev k mode chunks m 54 (lv + 64#64) 1 (chunks.size - 1) ∧
    Cv.At m (lv + 64#64 + place (chunks.size - 1)) (Blake3.sub k mode chunks (chunks.size - 1) 1))

/-- The levels in memory: 3520 bytes. -/
@[abi] def layout (k : Blake3.CV) (mode : Blake3.Word) : Abi.Layout (Array Blake3.Node) := ⟨3520#64, At k mode⟩

end Levels
