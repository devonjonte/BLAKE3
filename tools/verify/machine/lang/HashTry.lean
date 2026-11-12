import TrySem
import HasherOde
import HashContract

/-! # `hash`, tried on examples against its contract, at the level of the source's meaning

Not a proof, and not about the assembled code: the source function `hash` of `hasher.ode` is run by
`Sem.lean` (what the language's statements mean), each kernel being to the source what its contract
says (the specification's compression, one block or many). On each example the 32 bytes left at `out`
must be `Blake3.hashBytes` of the message, as `Hash.byteContract` (`../spec/HashContract.lean`) claims,
and the message and the key must be as they were. What this can show wrong: the source, or the contract. -/

namespace Try

def word64 (m : L.Mem) (a : L.Word) : L.Word :=
  m (a + 7) ++ m (a + 6) ++ m (a + 5) ++ m (a + 4) ++ m (a + 3) ++ m (a + 2) ++ m (a + 1) ++ m a

def cvOf (m : L.Mem) (a : L.Word) : Vector UInt32 8 := Vector.ofFn fun i => word32 m (a + BitVec.ofNat 64 (4 * i.val))
def blockOf (m : L.Mem) (a : L.Word) : Vector UInt32 16 := Vector.ofFn fun i => word32 m (a + BitVec.ofNat 64 (4 * i.val))

/-- Eight words as 32 bytes, each word lowest byte first. -/
def bytesOf (h : Vector UInt32 8) : Array (BitVec 8) :=
  Array.ofFn (n := 32) fun i => (h[i.val / 4]!.toBitVec >>> (8 * (i.val % 4))).setWidth 8

def first8 (o : Vector UInt32 16) : Vector UInt32 8 := Vector.ofFn fun j => o[j.val]!

def place (m : L.Mem) (a : L.Word) (bs : Array (BitVec 8)) : L.Mem :=
  fun x => let d := (x - a).toNat; if d < bs.size then bs[d]! else m x

/-- A one-block compression kernel, as its contract has it: the 32 bytes it leaves at `cv`. (Computed
once, when the kernel is called: `Try.compress` computes them at every read.) -/
def compressNow (m : L.Mem) (cv block len counter flags : L.Word) : Array (BitVec 8) :=
  bytesOf (first8 (Blake3.BLAKE3_COMPRESS (cvOf m cv) (blockOf m block) ⟨counter⟩ ⟨len.setWidth 32⟩ ⟨flags.setWidth 32⟩))

/-- A many-inputs kernel, as its contract has it (`blake3_servil_hash_many_*`): for each of `n` inputs,
`blocks` blocks from its pointer are compressed in turn from the key, with the counter (stepped by one an
input if `inc` is not zero), `flags`, and `fstart` on the first block and `fend` on the last; the eight
words go to `out`, 32 bytes an input. Here: the bytes it leaves at `out`. -/
def hashManyNow (m : L.Mem) (inputs n blocks key counter inc flags fstart fend : L.Word) : Array (BitVec 8) := Id.run do
  let mut out : Array (BitVec 8) := #[]
  for i in [0:n.toNat] do
    let ptr := word64 m (inputs + BitVec.ofNat 64 (8 * i))
    let mut h := cvOf m key
    for b in [0:blocks.toNat] do
      let fl := flags ||| (if b == 0 then fstart else 0) ||| (if b + 1 == blocks.toNat then fend else 0)
      let ctr := if inc == 0 then counter else counter + BitVec.ofNat 64 i
      h := first8 (Blake3.BLAKE3_COMPRESS h (blockOf m (ptr + BitVec.ofNat 64 (64 * b))) ⟨ctr⟩ 64 ⟨fl.setWidth 32⟩)
    out := out ++ bytesOf h
  return out

/-- The surroundings of `hash`: the one-block kernels and the many-inputs kernels, by their contracts. -/
def hashEnv (f : L.Fn) : L.Env :=
  { semEnv f with
    ext := fun g args m =>
      if g == "blake3_servil_compress_in_place_avx512" || g == "blake3_servil_compress_in_place_sse41" then
        match args with
        | [cv, block, len, counter, flags] =>
          let bs := compressNow m cv block len counter flags
          some (place m cv bs)
        | _ => none
      else if g == "blake3_servil_hash_many_sse41" || g == "blake3_servil_hash_many_avx2" || g == "blake3_servil_hash_many_avx512" then
        match args with
        | [inputs, n, blocks, key, counter, inc, flags, fstart, fend, out] =>
          let bs := hashManyNow m inputs n blocks key counter inc flags fstart fend
          some (place m out bs)
        | _ => none
      else none }

def inpAt : L.Word := 0x100000#64
def keyAt : L.Word := 0x200000#64
def outAt : L.Word := 0x300000#64

/-- The message of `n` bytes the test vectors use: byte `i` is `i mod 251`. -/
def message (n : Nat) : List (BitVec 8) := (List.range n).map fun i => BitVec.ofNat 8 (i % 251)

def bytesAt (m : L.Mem) (a : L.Word) (n : Nat) : List (BitVec 8) := (List.range n).map fun i => m (a + BitVec.ofNat 64 i)

/-- One example: the message of `n` bytes, hashed by the source on platform `plat`. `some true`: what
`Hash.byteContract` says holds of the memory left (the 32 bytes at `out` are the specification's hash of
the message; the message and the key are as they were). `none`: the source did not finish. The second
answer is a control: the 32 bytes are not the hash of the message with one byte more. -/
def hashExample (n : Nat) (plat : Nat) : Option Bool × Bool :=
  let msg := message n
  let m0 : L.Mem := place (place (fun _ => 0) inpAt msg.toArray) keyAt Blake3.ivBytes.toArray
  match L.Fn.run (hashEnv Ode.hash) 2000000 Ode.hash [outAt, inpAt, BitVec.ofNat 64 n, keyAt, 0, BitVec.ofNat 64 plat] m0 with
  | none => (none, false)
  | some (_, st) =>
    let out := bytesAt st.mem outAt 32
    (some (out == Blake3.hashBytes msg && bytesAt st.mem inpAt n == msg && bytesAt st.mem keyAt 32 == Blake3.ivBytes),
     out != Blake3.hashBytes (message (n + 1)))

/-- The lengths of the BLAKE3 test vectors. -/
def lengths : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 63, 64, 65, 127, 128, 129, 1023, 1024, 1025, 2048, 2049, 3072, 3073, 4096, 4097,
   5120, 5121, 6144, 6145, 7168, 7169, 8192, 8193, 16384, 31744, 102400]

end Try

-- The empty message's hash begins af 13 49 b9.
#guard (Blake3.hashBytes []).take 4 == [0xaf#8, 0x13#8, 0x49#8, 0xb9#8]

#eval (do
  let mut met := 0
  let mut bad : List (Nat × Nat) := []
  let mut controls := 0
  for plat in [3, 4, 5] do
    for n in Try.lengths do
      -- on AVX-512 above 32 KiB the source calls the 32-lane kernels, whose contracts are not written here
      if plat == 5 && n > 32768 then continue
      let (r, c) := Try.hashExample n plat
      if r == some true then met := met + 1 else bad := (n, plat) :: bad
      if c then controls := controls + 1
  IO.println s!"hash, the source's meaning against Hash.byteContract: {met} examples meet it, {bad.length} do not {bad.reverse}; the control (not the hash of a message one byte longer) holds on {controls}" : IO Unit)
