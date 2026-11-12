import StackBytes

/-! # `merge` and `add`: what is claimed, of the code for any machine

Definitions only. The theorems so far are for x86-64 on our model: `merge_meets_bytes`, `add_meets_bytes`
(`../lang/Meets_merge_bytes.lean`). -/

/-- What merging leaves of a stack `cvs`: the specification's `mergeTo` (while more than `target` values
are held, the two newest become their parent node's chaining value), under the key `k` and the mode's
flags. -/
def Merge.merged (k : Blake3.CV) (flags target : BitVec 64) (cvs : List Blake3.CV) : List Blake3.CV :=
  Blake3.mergeTo k ⟨flags.setWidth 32⟩ target.toNat cvs

/-- **`merge(st, key, flags, plat, target)`.** For a target of at least one and the mode's flags below 256:
the stack at `st` turns into `Merge.merged` of it, under the key at `key`, and the result is its count.
`plat` chooses the kernel and changes nothing else. -/
def Merge.byteContract (st key flags plat target : BitVec 64) (k : Blake3.CV) (cvs : List Blake3.CV) : Bytes.Contract where
  args := [st, key, flags, plat, target]
  accepts := 1#64 ≤ target ∧ flags < 256#64
  reads := [Cv.byteLayout.keeps key k]
  updates := [Stack.byteLayout.turns st cvs (Merge.merged k flags target cvs)]
  returns := fun result => result.toNat = (Merge.merged k flags target cvs).length

/-- **`add(st, key, flags, plat, cv, target)`.** A chunk's chaining value arrives: for a stack of fewer
than 55 values at `st`, a target of at least one and the mode's flags below 256, the stack turns into
`Merge.merged` of the stack with the value at `cv` on it, under the key at `key`, and the result is its
count. -/
def Add.byteContract (st key flags plat cv target : BitVec 64) (k new : Blake3.CV) (cvs : List Blake3.CV) : Bytes.Contract where
  args := [st, key, flags, plat, cv, target]
  accepts := cvs.length < 55 ∧ 1#64 ≤ target ∧ flags < 256#64
  reads := [Cv.byteLayout.keeps key k, Cv.byteLayout.keeps cv new]
  updates := [Stack.byteLayout.turns st cvs (Merge.merged k flags target (new :: cvs))]
  returns := fun result => result.toNat = (Merge.merged k flags target (new :: cvs)).length
