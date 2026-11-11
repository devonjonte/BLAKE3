import Lang
open L

/-! # Functions of the hasher, written in the language

The stack of chaining values is laid out by us, not by a compiler: the length (a word) at offset
0, and from offset 32 up to 55 values of 32 bytes each. A key is 32 bytes. `plat` is the
platform's number as the library records it (5: AVX-512; otherwise SSE4.1 here). -/

def PARENT : Nat := 4
def stackCvs : Nat := 32

/-- The address of value `i` of the stack at `st`. -/
def cvAt (st i : Exp) : Exp := .add (.add st (.const stackCvs)) (.shl i 5)

/-- `CvStack::push`: `cv` on top. The caller owes: fewer than 55 values. -/
def push : Fn where
  name := "b3l_push"
  params := ["st", "cv"]
  locals := ["len"]
  bufs := []
  externs := []
  body := [
    .set "len" (.load 64 (.var "st")),
    .ite (.ltu (.var "len") (.const 55)) [] [.trap],
    .copy 32 (cvAt (.var "st") (.var "len")) (.var "cv"),
    .store 64 (.var "st") (.add (.var "len") (.const 1))]
  ret := .const 0

/-- `CvStack::merge`: while the stack holds more than `target` values, its top two become their
parent. The caller owes: `target ≥ 1`, or a stack of at most `target` values. -/
def merge : Fn where
  name := "b3l_merge"
  params := ["st", "key", "flags", "plat", "target"]
  locals := ["len", "pf", "at"]
  bufs := [("block", 64), ("cv", 32)]
  externs := ["blake3_servil_compress_in_place_avx512", "blake3_servil_compress_in_place_sse41"]
  body := [
    .set "len" (.load 64 (.var "st")),
    .set "pf" (.or (.var "flags") (.const PARENT)),
    .while (.ltu (.var "target") (.var "len")) [
      .ite (.ltu (.var "len") (.const 2)) [.trap] [],
      .set "at" (cvAt (.var "st") (.sub (.var "len") (.const 2))),
      .copy 64 (.buf "block") (.var "at"),
      .copy 32 (.buf "cv") (.var "key"),
      .ite (.eq (.var "plat") (.const 5))
        [.call "blake3_servil_compress_in_place_avx512" [.buf "cv", .buf "block", .const 64, .const 0, .var "pf"]]
        [.call "blake3_servil_compress_in_place_sse41" [.buf "cv", .buf "block", .const 64, .const 0, .var "pf"]],
      .copy 32 (.var "at") (.buf "cv"),
      .set "len" (.sub (.var "len") (.const 1)),
      .store 64 (.var "st") (.var "len")]]
  ret := .var "len"

/-- A hexadecimal digit of a number below 16, with no table and no branch: `'0' + n`, and 39 more
(to `'a'`) when `n` is above 9. -/
def hexDigit (n : Exp) : Exp :=
  .add (.add n (.const 48)) (.and (.sub (.const 0) (.shr (.add n (.const 6)) 4)) (.const 39))

/-- `Hash::to_hex`: the 64 hexadecimal characters of the 32 bytes at `hash`, written at `out`.
No address and no branch depends on the hash's bytes. -/
def toHex : Fn where
  name := "b3l_to_hex"
  params := ["out", "hash"]
  locals := ["i", "b"]
  bufs := []
  externs := []
  body := [
    .set "i" (.const 0),
    .while (.ltu (.var "i") (.const 32)) [
      .set "b" (.load 8 (.add (.var "hash") (.var "i"))),
      .store 8 (.add (.var "out") (.shl (.var "i") 1)) (hexDigit (.shr (.var "b") 4)),
      .store 8 (.add (.add (.var "out") (.shl (.var "i") 1)) (.const 1)) (hexDigit (.and (.var "b") (.const 15))),
      .set "i" (.add (.var "i") (.const 1))]]
  ret := .const 64

/-! ## A whole hash, with no Rust: `hash(input) -> 32 bytes` over the assembly kernels

BLAKE3 of `len` bytes at `input` under `key` and `flags`, 32 bytes to `out`. The whole chunks but
the last go to the widest `hash_many` kernel sixteen at a time; each chunk's value goes on the
stack as the specification's algorithm has it (merging while the count of chunks is even); the
last chunk is compressed block by block; the root is folded from the stack. -/

def CHUNK_START : Nat := 1
def CHUNK_END : Nat := 2
def ROOT : Nat := 8

/-- A call of the one-block kernel the platform has. Lean is the macro language: this is a Lean
function that makes statements. Every argument is a constant, a variable or a buffer. -/
def compress (cv block blockLen counter flags : Exp) : Stmt :=
  .ite (.eq (.var "plat") (.const 5))
    [.call "blake3_servil_compress_in_place_avx512" [cv, block, blockLen, counter, flags]]
    [.call "blake3_servil_compress_in_place_sse41" [cv, block, blockLen, counter, flags]]

/-- `dst` (a variable holding an address) becomes the parent of the values at `left` and `right`
under `pf` (a variable: the flags with PARENT, and ROOT for the root). Uses the buffers `block`
and `pcv`. `dst` may be `left` or `right`. -/
def parentTo (dst left right pf : Exp) : List Stmt := [
  .copy 32 (.buf "block") left,
  .copy 32 (.add (.buf "block") (.const 32)) right,
  .copy 32 (.buf "pcv") (.var "key"),
  compress (.buf "pcv") (.buf "block") (.const 64) (.const 0) pf,
  .copy 32 dst (.buf "pcv")]

/-- `ptrs[i] := base + (i << shift)` for `i` below `count` (a number). -/
def fillPtrs (base : Exp) (shift count : Nat) : List Stmt := [
  .set "i" (.const 0),
  .while (.ltu (.var "i") (.const count)) [
    .store 64 (.add (.buf "ptrs") (.shl (.var "i") 3)) (.add base (.shl (.var "i") shift)),
    .set "i" (.add (.var "i") (.const 1))]]

/-- `m` parents at once on AVX-512: the `2 * m` values at `src` become their `m` parents at `dst`. -/
def parentsMany (src dst : String) (m : Nat) : List Stmt :=
  fillPtrs (.buf src) 6 m ++
  [.call "blake3_servil_hash_many_avx512" [.buf "ptrs", .const m, .const 1, .var "key", .const 0, .const 0, .var "pf", .const 0, .const 0, .buf dst]]

/-- The value at `t` (a subtree that ends the chunks counted in `tc`, in units of its own size) goes
on the stack as the specification's algorithm has it: merged with the top while the count is even. -/
def pushMerging : List Stmt := [
  .while (.eq (.and (.var "tc") (.const 1)) (.const 0)) ([
    .set "slen" (.sub (.var "slen") (.const 1)),
    .set "top" (cvAt (.buf "st") (.var "slen"))] ++
    parentTo (.var "t") (.var "top") (.var "t") (.var "pf") ++ [
    .set "tc" (.shr (.var "tc") 1)]),
  .copy 32 (cvAt (.buf "st") (.var "slen")) (.var "t"),
  .set "slen" (.add (.var "slen") (.const 1))]

def hash : Fn where
  name := "b3l_hash"
  params := ["out", "input", "len", "key", "flags", "plat"]
  locals := ["p", "rem", "counter", "n", "i", "tc", "top", "first", "f", "j", "lastp", "pf", "slen", "t", "done", "kp", "pp"]
  regs := ["p", "rem", "counter", "i", "n", "key"]
  bufs := [("st", 1792), ("cvs", 1024), ("par", 512), ("ptrs", 256), ("block", 64), ("cv", 32), ("pcv", 32)]
  externs := ["blake3_servil_compress_in_place_avx512", "blake3_servil_compress_in_place_sse41",
    "blake3_servil_hash_many_avx512", "blake3_servil_hash_many_avx2", "blake3_servil_hash_many_sse41",
    "blake3_servil_avx512_k32", "blake3_servil_avx512_p16"]
  body := [
    .set "p" (.var "input"),
    .set "rem" (.var "len"),
    .set "counter" (.const 0),
    .set "slen" (.const 0),
    .set "done" (.const 0),
    .set "pf" (.or (.var "flags") (.const PARENT)),
    -- AVX-512: 32 chunks at a time while more than 32 KiB are left, by the 32-lane kernel; their 32
    -- values become one by the 16-lane parent kernel and four rounds of hash_many.
    .ite (.eq (.var "plat") (.const 5)) [
      .set "kp" (.or (.var "flags") (.const (CHUNK_START * 256 + CHUNK_END * 65536 + 64 * 16777216))),
      .set "pp" (.or (.var "pf") (.const (64 * 16777216))),
      .while (.ltu (.const 32768) (.var "rem")) (
        fillPtrs (.var "p") 10 32 ++
        [.call "blake3_servil_avx512_k32" [.buf "ptrs", .const 16, .var "key", .var "counter", .var "kp", .buf "cvs"]] ++
        fillPtrs (.buf "cvs") 6 16 ++
        [.call "blake3_servil_avx512_p16" [.buf "ptrs", .const 1, .var "key", .const 0, .var "pp", .buf "par"]] ++
        parentsMany "par" "cvs" 8 ++ parentsMany "cvs" "par" 4 ++ parentsMany "par" "cvs" 2 ++ parentsMany "cvs" "par" 1 ++
        [.set "t" (.buf "par"),
         .set "tc" (.add (.shr (.var "counter") 5) (.const 1))] ++
        pushMerging ++
        [.set "p" (.add (.var "p") (.const 32768)),
         .set "rem" (.sub (.var "rem") (.const 32768)),
         .set "counter" (.add (.var "counter") (.const 32))])] [],
    -- Whole chunks, up to sixteen at a time, while more than one chunk's bytes are left.
    .while (.ltu (.const 1024) (.var "rem")) [
      .set "n" (.shr (.var "rem") 10),
      .ite (.ltu (.const 16) (.var "n")) [.set "n" (.const 16)] [],
      .set "i" (.const 0),
      .while (.ltu (.var "i") (.var "n")) [
        .store 64 (.add (.buf "ptrs") (.shl (.var "i") 3)) (.add (.var "p") (.shl (.var "i") 10)),
        .set "i" (.add (.var "i") (.const 1))],
      .ite (.eq (.var "plat") (.const 5))
        [.call "blake3_servil_hash_many_avx512" [.buf "ptrs", .var "n", .const 16, .var "key", .var "counter", .const 1, .var "flags", .const CHUNK_START, .const CHUNK_END, .buf "cvs"]]
        [.ite (.eq (.var "plat") (.const 4))
          [.call "blake3_servil_hash_many_avx2" [.buf "ptrs", .var "n", .const 16, .var "key", .var "counter", .const 1, .var "flags", .const CHUNK_START, .const CHUNK_END, .buf "cvs"]]
          [.call "blake3_servil_hash_many_sse41" [.buf "ptrs", .var "n", .const 16, .var "key", .var "counter", .const 1, .var "flags", .const CHUNK_START, .const CHUNK_END, .buf "cvs"]]],
      .set "p" (.add (.var "p") (.shl (.var "n") 10)),
      .set "rem" (.sub (.var "rem") (.shl (.var "n") 10)),
      .set "i" (.const 0),
      .while (.ltu (.var "i") (.var "n")) [
        .set "t" (.add (.buf "cvs") (.shl (.var "i") 5)),
        .set "tc" (.add (.add (.var "counter") (.var "i")) (.const 1)),
        -- The message's last chunk is not pushed: the root is folded from it.
        .set "done" (.const 0),
        .ite (.eq (.var "rem") (.const 0)) [.ite (.eq (.add (.var "i") (.const 1)) (.var "n")) [.set "done" (.const 1)] []] [],
        .ite (.eq (.var "done") (.const 1)) [.copy 32 (.buf "cv") (.var "t")] pushMerging,
        .set "i" (.add (.var "i") (.const 1))],
      .set "counter" (.add (.var "counter") (.var "n"))],
    .ite (.eq (.var "done") (.const 0)) [
      -- The last chunk, at most 1024 bytes, block by block.
      .copy 32 (.buf "cv") (.var "key"),
      .set "first" (.const CHUNK_START),
      .while (.ltu (.const 64) (.var "rem")) [
        .set "f" (.or (.var "flags") (.var "first")),
        compress (.buf "cv") (.var "p") (.const 64) (.var "counter") (.var "f"),
        .set "first" (.const 0),
        .set "p" (.add (.var "p") (.const 64)),
        .set "rem" (.sub (.var "rem") (.const 64))],
      -- Its last block: whole from the input, or copied into a zeroed block.
      .ite (.eq (.var "rem") (.const 64))
        [.set "lastp" (.var "p")]
        ((List.range 8).map (fun k => Stmt.store 64 (.add (.buf "block") (.const (8 * k))) (.const 0)) ++ [
          .set "j" (.const 0),
          .while (.ltu (.var "j") (.var "rem")) [
            .store 8 (.add (.buf "block") (.var "j")) (.load 8 (.add (.var "p") (.var "j"))),
            .set "j" (.add (.var "j") (.const 1))],
          .set "lastp" (.buf "block")]),
      .set "f" (.or (.or (.var "flags") (.var "first")) (.const CHUNK_END)),
      -- One chunk alone is the root.
      .ite (.eq (.var "slen") (.const 0)) [.set "f" (.or (.var "f") (.const ROOT))] [],
      compress (.buf "cv") (.var "lastp") (.var "rem") (.var "counter") (.var "f"),
      .ite (.eq (.var "slen") (.const 0)) [.copy 32 (.var "out") (.buf "cv")] []] [],
    .ite (.ne (.var "slen") (.const 0)) ([
      .set "t" (.buf "cv"),
      -- Fold the stack from the top; the last parent is the root.
      .while (.ltu (.const 1) (.var "slen")) ([
        .set "slen" (.sub (.var "slen") (.const 1)),
        .set "top" (cvAt (.buf "st") (.var "slen"))] ++
        parentTo (.var "t") (.var "top") (.var "t") (.var "pf")),
      .set "pf" (.or (.var "pf") (.const ROOT)),
      .set "top" (cvAt (.buf "st") (.const 0))] ++
      parentTo (.var "out") (.var "top") (.var "t") (.var "pf")) []]
  ret := .const 0

def all : List Fn := [push, merge, toHex, hash]

/-- The functions under another prefix, so that two printings link into one program. -/
def named (prefix_ : String) : List Fn := all.map fun f => { f with name := prefix_ ++ f.name.drop 4 }

def main (args : List String) : IO Unit :=
  match args with
  | ["rust", p] => IO.print (rustFile (named p))
  | ["asm", p] => IO.print (asmFile (named p))
  | _ => IO.eprintln "usage: rust PREFIX | asm PREFIX"
