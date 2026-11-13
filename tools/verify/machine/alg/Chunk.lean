import Blake3
import Stack

/-! # A chunk as a fold over its blocks, and the output's first 32 bytes

Facts about the specification alone, for the proofs of the code that hashes a chunk and of the code that
writes the hash: no machine is named. Checked by Lean; a reader of a contract reads none of this, for the
contracts speak of `Blake3.chunkNode`, `Blake3.tree` and `Blake3.output` themselves. -/

namespace Blake3

/-- The flags of block `j` of a chunk of `blocks` blocks (section 4.2), as `chunkNode` sets them. -/
def blockFlags (mode : Word) (blocks j : Nat) : Word :=
  mode ||| (if j = 0 then CHUNK_START else 0) ||| (if j + 1 = blocks then CHUNK_END else 0)

/-- The chaining value after the first `j` blocks of a chunk. -/
def chunkFold (key : Vector Word 8) (mode : Word) (chunk : ByteArray) (index : Nat) : Nat → Vector Word 8
  | 0 => key
  | j + 1 => first8 (BLAKE3_COMPRESS (chunkFold key mode chunk index j) (wordsLE chunk (64 * j) 16) index.toUInt64 64
      (blockFlags mode (blockCount chunk.size) j))

theorem chunkFold_range (key : Vector Word 8) (mode : Word) (chunk : ByteArray) (index n : Nat) :
    (List.range n).foldl
      (fun h j => first8 (BLAKE3_COMPRESS h (wordsLE chunk (64 * j) 16) index.toUInt64 64 (blockFlags mode (blockCount chunk.size) j))) key
    = chunkFold key mode chunk index n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl

/-- **The specification's chunk node is the fold over all its blocks but the last, with the last block as
its message.** -/
theorem chunkNode_eq (key : Vector Word 8) (mode : Word) (chunk : ByteArray) (index : Nat) :
    chunkNode key mode chunk index =
      { h := chunkFold key mode chunk index (blockCount chunk.size - 1),
        m := wordsLE chunk (64 * (blockCount chunk.size - 1)) 16,
        t := index.toUInt64,
        len := (chunk.size - 64 * (blockCount chunk.size - 1)).toUInt32,
        flags := blockFlags mode (blockCount chunk.size) (blockCount chunk.size - 1) } := by
  have h := chunkFold_range key mode chunk index (blockCount chunk.size - 1)
  unfold chunkNode
  simp only [Nat.toUInt64_eq, blockFlags, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one, List.forIn_pure_yield_eq_foldl, Nat.toUInt32_eq, bind_pure_comp,
    map_pure] at h ⊢
  rw [← List.range_eq_range', h]; rfl

/-- The tree over one chunk is that chunk. -/
theorem tree_one (key : Vector Word 8) (mode : Word) (chunks : Array Node) (h : chunks.size = 1) :
    tree key mode chunks = chunks[0]! := by
  unfold tree
  rw [h, tree.go]
  simp

/-- The first eight words of a node's output: its compression as the root with the output's counter 0
(sections 4.3.2 and 4.4). -/
def rootWords (root : Node) : Vector Word 8 :=
  first8 (BLAKE3_COMPRESS root.h root.m 0 root.len (root.flags ||| ROOT))

/-- The four bytes of a word, lowest first. -/
def wordBytes (w : Word) : List UInt8 := [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

theorem bytesLE_data (ws : List Word) : (bytesLE ws).data.toList = ws.flatMap wordBytes := by
  simp [bytesLE]; rfl

/-- **An output of 32 bytes is the bytes of the root's first eight output words.** -/
theorem output_32 (root : Node) :
    (output root 32).data.toList = (rootWords root).toList.flatMap wordBytes := by
  unfold output rootWords
  have h1 : (32 + 63) / 64 = 1 := rfl
  simp only [h1, List.range_one, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  show ((bytesLE (BLAKE3_COMPRESS root.h root.m 0 root.len (root.flags ||| ROOT)).toList).extract 0 32).data.toList = _
  generalize BLAKE3_COMPRESS root.h root.m 0 root.len (root.flags ||| ROOT) = v
  obtain ⟨⟨l⟩, hl⟩ := v
  simp only [ByteArray.data_extract, Array.toList_extract, first8]
  have hl' : l.length = 16 := hl
  match l, hl' with
  | [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15], _ =>
    simp only [Vector.toList_mk]
    rfl

/-- A message's bytes as the specification takes them. -/
def ofBytes (bs : List (BitVec 8)) : ByteArray := ⟨(bs.map fun b => (⟨b⟩ : UInt8)).toArray⟩

theorem ofBytes_size (bs : List (BitVec 8)) : (ofBytes bs).size = bs.length := by
  simp [ofBytes, ByteArray.size]

/-- A byte of the message, zero past its end: as the specification's `get!` reads it. -/
theorem ofBytes_get (bs : List (BitVec 8)) (n : Nat) : (ofBytes bs).get! n = ⟨bs.getD n 0#8⟩ := by
  simp only [ofBytes, ByteArray.get!]
  by_cases h : n < bs.length
  · simp [List.getD, h]
  · simp [List.getD, h]; rfl

/-- **The 32 bytes of BLAKE3 are the bytes of the first eight output words of the tree over the input's
chunks.** -/
theorem blake3_32 (key : Vector Word 8) (mode : Word) (input : ByteArray) :
    (blake3 key mode input 32).data.toList = (rootWords (tree key mode (chunksOf key mode input))).toList.flatMap wordBytes :=
  output_32 _

end Blake3

#print axioms Blake3.chunkNode_eq
#print axioms Blake3.blake3_32
