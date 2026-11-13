import StackBytes

/-! # The tree's levels (`ladd`, `lroot`): what is claimed, of the code for any machine

The tree of chaining values another way than the stack (`../levels/levels.ode`): a parent has memory of
its own, and the newest chunk's value waits at the bottom until the next arrives, so every chunk's value
is added, the last too, and the root is made at the end.

Each level has two places, 32 bytes each, side by side; level 0 is the chunks' own. The levels are a
counter in binary: a level that has received an odd number of values holds the newest of them, in its
first place; each pair it received went, as the pair's parent, to the level above. And the newest chunk of
all waits in the bottom level's free place: its turn to count comes when the next chunk arrives (until
then it may be the root's child).

Definitions only, of bytes. **The theorem so far is about the same words said of the x86-64 model's
memory** (`../lang/Spec_levels.lean`, `Spec_ladd.lean`: `ladd_meets`, `../lang/Proof_ladd.lean`); that these
bytes say the same is not proved yet, and `lroot` has no theorem yet. The whole hash on the levels is tried
against `Hash.byteContract`, the contract of the hash on the stack, unchanged (`../levels/try_hash2.sh`). -/

namespace Levels

/-- **The levels from byte `o` of `b` upward, `f` of them, have received `r` values of `size` chunks each**
(whole subtrees of the specification's tree, in order from chunk 0): if `r` is odd this level holds the
newest of them in its first place, and the level above has received `r / 2` values of twice the size. -/
def Received (key : Blake3.CV) (mode : Blake3.Word) (chunks : Array Blake3.Node) (b : List (BitVec 8)) : Nat → Nat → Nat → Nat → Prop
  | 0, _, _, r => r = 0
  | f + 1, o, size, r =>
    (r % 2 = 1 → (b.drop o).take 32 = Cv.bytes (Blake3.sub key mode chunks ((r - 1) * size) size)) ∧
    Received key mode chunks b f (o + 64) (2 * size) (r / 2)

/-- **The bytes `b` hold the levels of the tree over `chunks`**, under a key and a mode: 3520 bytes; the
count of chunks in the first eight; the levels from byte 64, 64 bytes each, 54 of them; at most `2 ^ 54`
chunks. With a chunk or more: the levels have received all the chunks but the newest, and the newest
chunk's value is in the bottom level's next place (its second, if the first is in use). -/
def Holds (key : Blake3.CV) (mode : Blake3.Word) (b : List (BitVec 8)) (chunks : Array Blake3.Node) : Prop :=
  b.length = 3520 ∧ chunks.size ≤ 2 ^ 54 ∧ b.take 8 = Bytes.le64 chunks.size ∧
  (0 < chunks.size →
    Received key mode chunks b 54 64 1 (chunks.size - 1) ∧
    (b.drop (64 + 32 * ((chunks.size - 1) % 2))).take 32 = Cv.bytes (Blake3.sub key mode chunks (chunks.size - 1) 1))

/-- The levels in memory: 3520 bytes. -/
def byteLayout (key : Blake3.CV) (mode : Blake3.Word) : Bytes.Layout (Array Blake3.Node) := ⟨3520, Holds key mode⟩

/-- The 32 bytes of the specification's output for the tree over `chunks` (sections 4.3 and 4.4). -/
def rootBytes (key : Blake3.CV) (mode : Blake3.Word) (chunks : Array Blake3.Node) : List (BitVec 8) :=
  (Blake3.output (Blake3.tree key mode chunks) 32).toList.map (·.toBitVec)

end Levels

/-- **`ladd(lv, key, flags, plat, cv)`.** A chunk's chaining value arrives: the levels at `lv` over
`chunks` become the levels over `chunks` and the new chunk, whose value is at `cv`; the result is the
count. The key at `key` and the mode's flags (below 256) are those of every call on these levels. `plat`
chooses the kernel and changes nothing else. -/
def Ladd.byteContract (lv key flags plat cv : BitVec 64) (k : Blake3.CV) (chunks : Array Blake3.Node)
    (new : Blake3.Node) : Bytes.Contract where
  args := [lv, key, flags, plat, cv]
  accepts := chunks.size < 2 ^ 54 ∧ flags < 256#64
  reads := [Cv.byteLayout.keeps key k, Cv.byteLayout.keeps cv new.cv]
  updates := [(Levels.byteLayout k ⟨flags.setWidth 32⟩).turns lv chunks (chunks.push new)]
  returns := fun result => result.toNat = chunks.size + 1

/-- **`lroot(out, lv, key, flags, plat)`.** For levels over two chunks or more: the 32 bytes at `out`
become the specification's output for the tree over them; the levels are unchanged. -/
def Lroot.byteContract (out lv key flags plat : BitVec 64) (k : Blake3.CV) (chunks : Array Blake3.Node) : Bytes.Contract where
  args := [out, lv, key, flags, plat]
  accepts := 2 ≤ chunks.size ∧ flags < 256#64
  reads := [Cv.byteLayout.keeps key k, (Levels.byteLayout k ⟨flags.setWidth 32⟩).keeps lv chunks]
  updates := [(Bytes.plain 32).fills out (Levels.rootBytes k ⟨flags.setWidth 32⟩ chunks)]
  returns := fun _ => True
