import StackBytes

/-! # The tree's levels (`ladd`, `lroot`): what is claimed, of the code for any machine

The tree of chaining values another way than the stack (`../levels/levels.ode`): a parent has memory of
its own, and the two newest values wait at the bottom level until a third arrives, so every chunk's value
is added, the last too, and the root is made at the end.

Definitions only. **No theorem yet.** The code is tried against BLAKE3 (`../levels/run_levels.sh`) and
the whole hash on it against `Hash.byteContract`, the contract of the hash on the stack, unchanged
(`../levels/try_hash2.sh`). These contracts are here to be compared with the stack's
(`PushContract.lean`, `MergeContract.lean`): they speak of the chunks added and of the specification's
tree over them, and of nothing a caller must compute. -/

namespace Levels

/-- How many values the bottom level holds once `n` were added: the newest one if `n` is odd, the newest
two if it is even. (Two stay until a third arrives: until then they may be the root's children.) -/
def bottom (n : Nat) : Nat := if n = 0 then 0 else if n % 2 = 1 then 1 else 2

/-- How many pairs the bottom level has given upward once `n` values were added. -/
def given (n : Nat) : Nat := (n - 1) / 2

/-- **The bytes `b` hold the levels of the tree over `chunks`**, under a key and a mode: 3520 bytes; the
count of chunks in the first eight; level `L`'s two places from byte `64 + 64 L`, 32 bytes each. The
bottom level holds the newest chunks' chaining values, the older first. A level `L` above it holds a
value, in its first place, if bit `L - 1` of the count of pairs given upward is set: the chaining value of
the specification's subtree over the newest `2 ^ L` chunks that are whole such a subtree. Fewer than
`2 ^ 54` chunks. -/
def Holds (key : Blake3.CV) (mode : Blake3.Word) (b : List (BitVec 8)) (chunks : Array Blake3.Node) : Prop :=
  b.length = 3520 ∧ chunks.size < 2 ^ 54 ∧ b.take 8 = Bytes.le64 chunks.size ∧
  (∀ j : Nat, j < bottom chunks.size →
    (b.drop (64 + 32 * j)).take 32 = Cv.bytes (Blake3.sub key mode chunks (chunks.size - bottom chunks.size + j) 1)) ∧
  ∀ L : Nat, 1 ≤ L → L < 54 → given chunks.size / 2 ^ (L - 1) % 2 = 1 →
    (b.drop (64 + 64 * L)).take 32 =
      Cv.bytes (Blake3.sub key mode chunks (given chunks.size / 2 ^ L * 2 ^ (L + 1)) (2 ^ L))

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
  accepts := chunks.size + 1 < 2 ^ 54 ∧ flags < 256#64
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
