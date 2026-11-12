import Try
import Sem
import Blake3
open X86

/-! # The source's meaning, run on the same example

When the assembled code breaks its contract on an example, the same example is run through the meaning
of the source (`Sem.lean`). If the source breaks the contract too, the source or the contract is wrong.
If the source keeps it, the code the compiler made is wrong. A kernel is, to the source, what its
contract says: the specification's compression. Test-side; not a proof. -/

namespace Try

def word32 (m : L.Mem) (a : L.Word) : UInt32 := ⟨(m (a + 3) ++ m (a + 2) ++ m (a + 1) ++ m a)⟩

/-- A one-block compression kernel, as its contract has it: the chaining value at `cv` becomes the first
eight words of the specification's compression of it with the block. -/
def compress (m : L.Mem) (cv block len counter flags : L.Word) : L.Mem :=
  let h : Vector UInt32 8 := Vector.ofFn fun i => word32 m (cv + BitVec.ofNat 64 (4 * i.val))
  let b : Vector UInt32 16 := Vector.ofFn fun i => word32 m (block + BitVec.ofNat 64 (4 * i.val))
  let out := Blake3.BLAKE3_COMPRESS h b ⟨counter⟩ ⟨len.setWidth 32⟩ ⟨flags.setWidth 32⟩
  fun x =>
    let d := (x - cv).toNat
    if d < 32 then (out[d / 4]!.toBitVec >>> (8 * (d % 4))).setWidth 8 else m x

/-- The source's surroundings: its buffers one after another in a scratch area, and the kernels. -/
def semEnv (f : L.Fn) : L.Env where
  buf := fun b =>
    let rec at_ : List (String × Nat) → Nat → Nat
      | [], off => off
      | (n, size) :: rest, off => if n == b then off else at_ rest (off + size)
    0x7FFD0000#64 + BitVec.ofNat 64 (at_ f.bufs 0)
  ext := fun g args m =>
    if g == "blake3_servil_compress_in_place_avx512" || g == "blake3_servil_compress_in_place_sse41" then
      match args with
      | [cv, block, len, counter, flags] => some (compress m cv block len counter flags)
      | _ => none
    else none

/-- Run the source on a machine memory (bytes the program does not own read as zero), for at most 20000
statements deep. -/
def source (f : L.Fn) (args : List (BitVec 64)) (m : Mem) : Option (BitVec 64 × Mem) :=
  (L.Fn.run (semEnv f) 20000 f args (fun x => (m x).getD 0)).map fun (r, st) => (r, fun x => some (st.mem x))

end Try
