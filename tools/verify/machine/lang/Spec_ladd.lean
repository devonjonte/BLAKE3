import Abi
import Spec_levels
open X86

/-! # `ladd`: what is claimed

Definitions only. The theorem is `ladd_meets` (`Proof_ladd.lean`, written by the compiler): the function
`ladd` of the assembled program meets `Ladd.contract`, whatever its arguments. -/

/-- **`ladd(lv, key, flags, plat, cv)`.** A chunk's chaining value arrives: the levels at `lv` over `chunks`
become the levels over `chunks` and the new chunk, whose value is at `cv`; the result is the count. The
key at `key` and the mode's flags (below 256) are those of every call on these levels. `plat` chooses the
kernel and changes nothing else. -/
def Ladd.contract (lv key flags plat cv : BitVec 64) (k : Blake3.CV) (chunks : Array Blake3.Node) (new : Blake3.Node) : Abi.Contract where
  args := [lv, key, flags, plat, cv]
  stack := 256#64
  accepts := chunks.size + 1 < 2 ^ 54 ∧ flags < 256#64
  reads := [Cv.layout.keeps key k, Cv.layout.keeps cv new.cv]
  updates := [(Levels.layout k ⟨flags.setWidth 32⟩).turns lv chunks (chunks.push new)]
  returns := fun result => result.toNat = chunks.size + 1
