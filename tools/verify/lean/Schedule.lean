import Blake3

/-! # The hash as a schedule of compressions

`sched n` lists the compressions BLAKE3 performs on an input of `n` bytes,
in order, each naming where its inputs come from: the key, a word of the
input (zero past its end), or the chaining value of an earlier entry. The
last entry is the root. `run` performs them; `blake3_eq_run` proves that
the result is the specification's 32-byte output, for every key, mode,
and input of that length. `Emit` writes `sched n` for the proofs' Python,
which replays it on symbolic words. -/

namespace Schedule

/-- Where a word comes from. -/
inductive Src where
  | key (i : Nat)        -- word i of the key
  | msg (j : Nat)        -- input word j: bytes 4j..4j+3, little-endian, zero past the end
  | cv (e i : Nat)       -- word i of entry e's chaining value (an earlier entry)
  deriving Repr, Inhabited, DecidableEq

/-- One compression: its chaining value's and block's words, counter,
block length, and flags beyond the mode's. -/
structure Entry where
  h : List Src
  m : List Src
  t : Nat
  len : Nat
  flags : Nat
  deriving Repr, Inhabited

/-- Input word j of `b`, zero past its end (section 2.1). -/
def msgWord (b : ByteArray) (j : Nat) : Blake3.Word := (Blake3.wordsLE b (4 * j) 1)[0]

/-- The entries of chunk `i` (`size` bytes), the chain's first entry at
index `base`: one per block, each block's chaining value the previous
entry's (the first, the key's). -/
def chunkEntries (base i size : Nat) : List Entry :=
  let blocks := Blake3.blockCount size
  (List.range blocks).map fun j =>
    { h := if j = 0 then (List.range 8).map Src.key else (List.range 8).map (Src.cv (base + j - 1))
      m := (List.range 16).map fun w => Src.msg (256 * i + 16 * j + w)
      t := i
      len := if j + 1 = blocks then size - 64 * j else 64
      flags := (if j = 0 then 1 else 0) ||| (if j + 1 = blocks then 2 else 0) }

/-- The size of chunk `i` of an input of `n` bytes (`n` > 0 or `i` = 0). -/
def chunkSize (n i : Nat) : Nat := min 1024 (n - 1024 * i)

/-- The entries of the subtree over the `cnt` chunks from chunk `start` of
an input of `n` bytes, appended after `base` entries; its node is the last. -/
def subtree (n : Nat) (base start cnt : Nat) : List Entry :=
  if cnt ≤ 1 then chunkEntries base start (chunkSize n start)
  else
    let k := Blake3.leftCount cnt
    let left := subtree n base start k
    let right := subtree n (base + left.length) (start + k) (cnt - k)
    let l := base + left.length - 1
    let r := base + left.length + right.length - 1
    left ++ right ++
      [{ h := (List.range 8).map Src.key
         m := (List.range 8).map (Src.cv l) ++ (List.range 8).map (Src.cv r)
         t := 0, len := 64, flags := 4 }]
termination_by cnt
decreasing_by
  · exact Blake3.leftCount_lt cnt (by omega)
  · have := Blake3.leftCount_pos cnt; omega

/-- The schedule of an input of `n` bytes. -/
def sched (n : Nat) : List Entry := subtree n 0 0 (max 1 ((n + 1023) / 1024))

/-- A source's word. -/
def word (key : Vector Blake3.Word 8) (b : ByteArray) (cvs : List (Vector Blake3.Word 8)) : Src → Blake3.Word
  | .key i => key[i]!
  | .msg j => msgWord b j
  | .cv e i => (cvs[e]!)[i]!

/-- An entry's compression. -/
def compressEntry (key : Vector Blake3.Word 8) (mode : Blake3.Word) (b : ByteArray)
    (cvs : List (Vector Blake3.Word 8)) (e : Entry) (extra : Blake3.Word) : Vector Blake3.Word 16 :=
  Blake3.BLAKE3_COMPRESS (Vector.ofFn fun i => word key b cvs (e.h[i.val]!))
    (Vector.ofFn fun i => word key b cvs (e.m[i.val]!)) e.t.toUInt64 e.len.toUInt32
    (mode ||| e.flags.toUInt32 ||| extra)

/-- The chaining values of the entries, in order. -/
def cvsOf (key : Vector Blake3.Word 8) (mode : Blake3.Word) (b : ByteArray) : List Entry → List (Vector Blake3.Word 8)
  | es => es.foldl (fun cvs e => cvs ++ [Blake3.first8 (compressEntry key mode b cvs e 0)]) []

/-- The schedule run: the root's 32 bytes. -/
def run (key : Vector Blake3.Word 8) (mode : Blake3.Word) (b : ByteArray) : ByteArray :=
  let es := sched b.size
  let cvs := cvsOf key mode b es.dropLast
  Blake3.bytesLE (Blake3.first8 (compressEntry key mode b cvs es.getLast! Blake3.ROOT)).toList

end Schedule
