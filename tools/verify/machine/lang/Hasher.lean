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

def all : List Fn := [push, merge, toHex]

/-- The functions under another prefix, so that two printings link into one program. -/
def named (prefix_ : String) : List Fn := all.map fun f => { f with name := prefix_ ++ f.name.drop 4 }

def main (args : List String) : IO Unit :=
  match args with
  | ["rust", p] => IO.print (rustFile (named p))
  | ["asm", p] => IO.print (asmFile (named p))
  | _ => IO.eprintln "usage: rust PREFIX | asm PREFIX"
