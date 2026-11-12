import Lang
open L

/-! Written by odec.py from levels.ode. Not edited by hand. -/

namespace Ode

def ladd : Fn where
  name := "b3l_ladd"
  params := ["lv", "key", "flags", "plat", "t"]
  locals := ["pf", "ln", "q", "k", "j", "dst", "src"]
  regs := []
  bufs := []
  externs := ["blake3_servil_compress_in_place_avx512", "blake3_servil_compress_in_place_sse41"]
  body := [
    .set "pf" (.or (.var "flags") (.const 4)),
    .set "ln" (.const 0),
    .set "q" (.const 0),
    .set "k" (.const 0),
    .set "j" (.const 0),
    .set "dst" (.const 0),
    .set "src" (.const 0),
    .set "ln" (.load 64 (.var "lv")),
    .set "q" (.add (.var "ln") (.const 1)),
    .set "k" (.const 0),
    .while (.eq (.and (.var "q") (.const 1)) (.const 1)) [
      .ite (.eq (.var "q") (.const 1)) [
        .set "q" (.const 0)] [
        .set "k" (.add (.var "k") (.const 1)),
        .set "q" (.shr (.var "q") 1)]],
    .set "j" (.const 0),
    .ite (.ne (.var "q") (.const 0)) [
      .set "j" (.const 1)] [],
    .while (.ltu (.const 0) (.var "k")) [
      .set "dst" (.add (.add (.add (.var "lv") (.const 64)) (.shl (.var "k") 6)) (.shl (.var "j") 5)),
      .set "src" (.add (.add (.var "lv") (.const 64)) (.shl (.sub (.var "k") (.const 1)) 6)),
      .copy 32 (.var "dst") (.var "key"),
      .ite (.eq (.var "plat") (.const 5)) [
        .call "blake3_servil_compress_in_place_avx512" [(.var "dst"), (.var "src"), (.const 64), (.const 0), (.var "pf")]] [
        .call "blake3_servil_compress_in_place_sse41" [(.var "dst"), (.var "src"), (.const 64), (.const 0), (.var "pf")]],
      .set "j" (.const 0),
      .set "k" (.sub (.var "k") (.const 1))],
    .copy 32 (.add (.add (.add (.var "lv") (.const 64)) (.const 0)) (.shl (.var "j") 5)) (.var "t"),
    .store 64 (.var "lv") (.add (.var "ln") (.const 1))]
  ret := (.add (.var "ln") (.const 1))

def lroot : Fn where
  name := "b3l_lroot"
  params := ["out", "lv", "key", "flags", "plat"]
  locals := ["pf", "ln", "m", "q", "pw", "base", "have_p", "have_c", "h", "single", "f"]
  regs := []
  bufs := [("blk", 64), ("pr", 32), ("old", 32), ("acc", 32)]
  externs := ["blake3_servil_compress_in_place_avx512", "blake3_servil_compress_in_place_sse41"]
  body := [
    .set "pf" (.or (.var "flags") (.const 4)),
    .set "ln" (.const 0),
    .set "m" (.const 0),
    .set "q" (.const 0),
    .set "pw" (.const 0),
    .set "base" (.const 0),
    .set "have_p" (.const 0),
    .set "have_c" (.const 0),
    .set "h" (.const 0),
    .set "single" (.const 0),
    .set "f" (.const 0),
    .set "ln" (.load 64 (.var "lv")),
    .set "m" (.var "ln"),
    .set "q" (.add (.var "ln") (.const 1)),
    .set "pw" (.const 2),
    .set "base" (.add (.var "lv") (.const 64)),
    .set "have_p" (.const 0),
    .set "have_c" (.const 0),
    .while (.ne (.var "m") (.const 0)) [
      .set "h" (.const 0),
      .ite (.ltu (.const 1) (.var "q")) [
        .set "h" (.add (.const 1) (.and (.var "q") (.const 1)))] [],
      .set "single" (.const 0),
      .set "f" (.var "pf"),
      .ite (.eq (.var "ln") (.var "pw")) [
        .set "f" (.or (.var "pf") (.const 8))] [],
      .ite (.eq (.var "h") (.const 2)) [
        .ite (.eq (.var "have_p") (.const 1)) [
          .copy 32 (.buf "old") (.buf "pr"),
          .set "single" (.buf "old")] [],
        .copy 32 (.buf "pr") (.var "key"),
        .ite (.eq (.var "plat") (.const 5)) [
          .call "blake3_servil_compress_in_place_avx512" [(.buf "pr"), (.var "base"), (.const 64), (.const 0), (.var "f")]] [
          .call "blake3_servil_compress_in_place_sse41" [(.buf "pr"), (.var "base"), (.const 64), (.const 0), (.var "f")]],
        .set "have_p" (.const 1)] [
        .ite (.eq (.var "h") (.const 1)) [
          .ite (.eq (.var "have_p") (.const 1)) [
            .copy 32 (.buf "blk") (.var "base"),
            .copy 32 (.add (.buf "blk") (.const 32)) (.buf "pr"),
            .copy 32 (.buf "pr") (.var "key"),
            .ite (.eq (.var "plat") (.const 5)) [
              .call "blake3_servil_compress_in_place_avx512" [(.buf "pr"), (.buf "blk"), (.const 64), (.const 0), (.var "f")]] [
              .call "blake3_servil_compress_in_place_sse41" [(.buf "pr"), (.buf "blk"), (.const 64), (.const 0), (.var "f")]]] [
            .set "single" (.var "base")]] [
          .ite (.eq (.var "have_p") (.const 1)) [
            .set "single" (.buf "pr"),
            .set "have_p" (.const 0)] []]],
      .ite (.ne (.var "single") (.const 0)) [
        .ite (.eq (.var "have_c") (.const 1)) [
          .set "f" (.var "pf"),
          .ite (.eq (.var "m") (.const 1)) [
            .set "f" (.or (.var "pf") (.const 8))] [],
          .copy 32 (.buf "blk") (.var "single"),
          .copy 32 (.add (.buf "blk") (.const 32)) (.buf "acc"),
          .copy 32 (.buf "acc") (.var "key"),
          .ite (.eq (.var "plat") (.const 5)) [
            .call "blake3_servil_compress_in_place_avx512" [(.buf "acc"), (.buf "blk"), (.const 64), (.const 0), (.var "f")]] [
            .call "blake3_servil_compress_in_place_sse41" [(.buf "acc"), (.buf "blk"), (.const 64), (.const 0), (.var "f")]]] [
          .copy 32 (.buf "acc") (.var "single"),
          .set "have_c" (.const 1)]] [],
      .set "m" (.shr (.var "m") 1),
      .set "q" (.shr (.var "q") 1),
      .set "pw" (.add (.var "pw") (.var "pw")),
      .set "base" (.add (.var "base") (.const 64))],
    .copy 32 (.var "out") (.buf "acc")]
  ret := (.const 0)
  noResult := true

def hash2 : Fn where
  name := "b3l_hash2"
  params := ["out", "input", "len", "key", "flags", "plat"]
  locals := ["p", "rem", "counter", "pf", "i", "n", "t", "f", "ln", "q", "k", "j", "dst", "src", "m", "pw", "base", "have_p", "have_c", "h", "single", "one", "tail", "first", "lastp", "jj"]
  regs := ["p", "rem", "counter", "i", "n", "key"]
  bufs := [("lv", 3520), ("cvs", 1024), ("ptrs", 256), ("block", 64), ("cv", 32), ("blk", 64), ("pr", 32), ("old", 32), ("acc", 32)]
  externs := ["blake3_servil_hash_many_avx512", "blake3_servil_hash_many_avx2", "blake3_servil_hash_many_sse41", "blake3_servil_compress_in_place_avx512", "blake3_servil_compress_in_place_sse41"]
  body := [
    .set "p" (.var "input"),
    .set "rem" (.var "len"),
    .set "counter" (.const 0),
    .set "pf" (.or (.var "flags") (.const 4)),
    .set "i" (.const 0),
    .set "n" (.const 0),
    .set "t" (.const 0),
    .set "f" (.const 0),
    .set "ln" (.const 0),
    .set "q" (.const 0),
    .set "k" (.const 0),
    .set "j" (.const 0),
    .set "dst" (.const 0),
    .set "src" (.const 0),
    .set "m" (.const 0),
    .set "pw" (.const 0),
    .set "base" (.const 0),
    .set "have_p" (.const 0),
    .set "have_c" (.const 0),
    .set "h" (.const 0),
    .set "single" (.const 0),
    .store 64 (.buf "lv") (.const 0),
    .while (.ltu (.const 1024) (.var "rem")) [
      .set "n" (.shr (.var "rem") 10),
      .ite (.ltu (.const 16) (.var "n")) [
        .set "n" (.const 16)] [],
      .set "i" (.const 0),
      .while (.ltu (.var "i") (.var "n")) [
        .store 64 (.add (.buf "ptrs") (.shl (.var "i") 3)) (.add (.var "p") (.shl (.var "i") 10)),
        .set "i" (.add (.var "i") (.const 1))],
      .ite (.eq (.var "plat") (.const 5)) [
        .call "blake3_servil_hash_many_avx512" [(.buf "ptrs"), (.var "n"), (.const 16), (.var "key"), (.var "counter"), (.const 1), (.var "flags"), (.const 1), (.const 2), (.buf "cvs")]] [
        .ite (.eq (.var "plat") (.const 4)) [
          .call "blake3_servil_hash_many_avx2" [(.buf "ptrs"), (.var "n"), (.const 16), (.var "key"), (.var "counter"), (.const 1), (.var "flags"), (.const 1), (.const 2), (.buf "cvs")]] [
          .call "blake3_servil_hash_many_sse41" [(.buf "ptrs"), (.var "n"), (.const 16), (.var "key"), (.var "counter"), (.const 1), (.var "flags"), (.const 1), (.const 2), (.buf "cvs")]]],
      .set "p" (.add (.var "p") (.shl (.var "n") 10)),
      .set "rem" (.sub (.var "rem") (.shl (.var "n") 10)),
      .set "i" (.const 0),
      .while (.ltu (.var "i") (.var "n")) [
        .set "t" (.add (.buf "cvs") (.shl (.var "i") 5)),
        .set "ln" (.load 64 (.buf "lv")),
        .set "q" (.add (.var "ln") (.const 1)),
        .set "k" (.const 0),
        .while (.eq (.and (.var "q") (.const 1)) (.const 1)) [
          .ite (.eq (.var "q") (.const 1)) [
            .set "q" (.const 0)] [
            .set "k" (.add (.var "k") (.const 1)),
            .set "q" (.shr (.var "q") 1)]],
        .set "j" (.const 0),
        .ite (.ne (.var "q") (.const 0)) [
          .set "j" (.const 1)] [],
        .while (.ltu (.const 0) (.var "k")) [
          .set "dst" (.add (.add (.add (.buf "lv") (.const 64)) (.shl (.var "k") 6)) (.shl (.var "j") 5)),
          .set "src" (.add (.add (.buf "lv") (.const 64)) (.shl (.sub (.var "k") (.const 1)) 6)),
          .copy 32 (.var "dst") (.var "key"),
          .ite (.eq (.var "plat") (.const 5)) [
            .call "blake3_servil_compress_in_place_avx512" [(.var "dst"), (.var "src"), (.const 64), (.const 0), (.var "pf")]] [
            .call "blake3_servil_compress_in_place_sse41" [(.var "dst"), (.var "src"), (.const 64), (.const 0), (.var "pf")]],
          .set "j" (.const 0),
          .set "k" (.sub (.var "k") (.const 1))],
        .copy 32 (.add (.add (.add (.buf "lv") (.const 64)) (.const 0)) (.shl (.var "j") 5)) (.var "t"),
        .store 64 (.buf "lv") (.add (.var "ln") (.const 1)),
        .set "i" (.add (.var "i") (.const 1))],
      .set "counter" (.add (.var "counter") (.var "n"))],
    .set "one" (.const 0),
    .ite (.eq (.var "counter") (.const 0)) [
      .set "one" (.const 1)] [],
    .set "tail" (.var "one"),
    .ite (.ne (.var "rem") (.const 0)) [
      .set "tail" (.const 1)] [],
    .ite (.eq (.var "tail") (.const 1)) [
      .copy 32 (.buf "cv") (.var "key"),
      .set "first" (.const 1),
      .while (.ltu (.const 64) (.var "rem")) [
        .set "f" (.or (.var "flags") (.var "first")),
        .ite (.eq (.var "plat") (.const 5)) [
          .call "blake3_servil_compress_in_place_avx512" [(.buf "cv"), (.var "p"), (.const 64), (.var "counter"), (.var "f")]] [
          .call "blake3_servil_compress_in_place_sse41" [(.buf "cv"), (.var "p"), (.const 64), (.var "counter"), (.var "f")]],
        .set "first" (.const 0),
        .set "p" (.add (.var "p") (.const 64)),
        .set "rem" (.sub (.var "rem") (.const 64))],
      .set "lastp" (.var "p"),
      .ite (.ne (.var "rem") (.const 64)) [
        .store 64 (.add (.buf "block") (.const 0)) (.const 0),
        .store 64 (.add (.buf "block") (.const 8)) (.const 0),
        .store 64 (.add (.buf "block") (.const 16)) (.const 0),
        .store 64 (.add (.buf "block") (.const 24)) (.const 0),
        .store 64 (.add (.buf "block") (.const 32)) (.const 0),
        .store 64 (.add (.buf "block") (.const 40)) (.const 0),
        .store 64 (.add (.buf "block") (.const 48)) (.const 0),
        .store 64 (.add (.buf "block") (.const 56)) (.const 0),
        .set "jj" (.const 0),
        .while (.ltu (.var "jj") (.var "rem")) [
          .store 8 (.add (.buf "block") (.var "jj")) (.load 8 (.add (.var "p") (.var "jj"))),
          .set "jj" (.add (.var "jj") (.const 1))],
        .set "lastp" (.buf "block")] [],
      .set "f" (.or (.or (.var "flags") (.var "first")) (.const 2)),
      .ite (.eq (.var "one") (.const 1)) [
        .set "f" (.or (.var "f") (.const 8))] [],
      .ite (.eq (.var "plat") (.const 5)) [
        .call "blake3_servil_compress_in_place_avx512" [(.buf "cv"), (.var "lastp"), (.var "rem"), (.var "counter"), (.var "f")]] [
        .call "blake3_servil_compress_in_place_sse41" [(.buf "cv"), (.var "lastp"), (.var "rem"), (.var "counter"), (.var "f")]]] [],
    .ite (.eq (.var "one") (.const 1)) [
      .copy 32 (.var "out") (.buf "cv")] [
      .ite (.eq (.var "tail") (.const 1)) [
        .set "t" (.buf "cv"),
        .set "ln" (.load 64 (.buf "lv")),
        .set "q" (.add (.var "ln") (.const 1)),
        .set "k" (.const 0),
        .while (.eq (.and (.var "q") (.const 1)) (.const 1)) [
          .ite (.eq (.var "q") (.const 1)) [
            .set "q" (.const 0)] [
            .set "k" (.add (.var "k") (.const 1)),
            .set "q" (.shr (.var "q") 1)]],
        .set "j" (.const 0),
        .ite (.ne (.var "q") (.const 0)) [
          .set "j" (.const 1)] [],
        .while (.ltu (.const 0) (.var "k")) [
          .set "dst" (.add (.add (.add (.buf "lv") (.const 64)) (.shl (.var "k") 6)) (.shl (.var "j") 5)),
          .set "src" (.add (.add (.buf "lv") (.const 64)) (.shl (.sub (.var "k") (.const 1)) 6)),
          .copy 32 (.var "dst") (.var "key"),
          .ite (.eq (.var "plat") (.const 5)) [
            .call "blake3_servil_compress_in_place_avx512" [(.var "dst"), (.var "src"), (.const 64), (.const 0), (.var "pf")]] [
            .call "blake3_servil_compress_in_place_sse41" [(.var "dst"), (.var "src"), (.const 64), (.const 0), (.var "pf")]],
          .set "j" (.const 0),
          .set "k" (.sub (.var "k") (.const 1))],
        .copy 32 (.add (.add (.add (.buf "lv") (.const 64)) (.const 0)) (.shl (.var "j") 5)) (.var "t"),
        .store 64 (.buf "lv") (.add (.var "ln") (.const 1))] [],
      .set "ln" (.load 64 (.buf "lv")),
      .set "m" (.var "ln"),
      .set "q" (.add (.var "ln") (.const 1)),
      .set "pw" (.const 2),
      .set "base" (.add (.buf "lv") (.const 64)),
      .set "have_p" (.const 0),
      .set "have_c" (.const 0),
      .while (.ne (.var "m") (.const 0)) [
        .set "h" (.const 0),
        .ite (.ltu (.const 1) (.var "q")) [
          .set "h" (.add (.const 1) (.and (.var "q") (.const 1)))] [],
        .set "single" (.const 0),
        .set "f" (.var "pf"),
        .ite (.eq (.var "ln") (.var "pw")) [
          .set "f" (.or (.var "pf") (.const 8))] [],
        .ite (.eq (.var "h") (.const 2)) [
          .ite (.eq (.var "have_p") (.const 1)) [
            .copy 32 (.buf "old") (.buf "pr"),
            .set "single" (.buf "old")] [],
          .copy 32 (.buf "pr") (.var "key"),
          .ite (.eq (.var "plat") (.const 5)) [
            .call "blake3_servil_compress_in_place_avx512" [(.buf "pr"), (.var "base"), (.const 64), (.const 0), (.var "f")]] [
            .call "blake3_servil_compress_in_place_sse41" [(.buf "pr"), (.var "base"), (.const 64), (.const 0), (.var "f")]],
          .set "have_p" (.const 1)] [
          .ite (.eq (.var "h") (.const 1)) [
            .ite (.eq (.var "have_p") (.const 1)) [
              .copy 32 (.buf "blk") (.var "base"),
              .copy 32 (.add (.buf "blk") (.const 32)) (.buf "pr"),
              .copy 32 (.buf "pr") (.var "key"),
              .ite (.eq (.var "plat") (.const 5)) [
                .call "blake3_servil_compress_in_place_avx512" [(.buf "pr"), (.buf "blk"), (.const 64), (.const 0), (.var "f")]] [
                .call "blake3_servil_compress_in_place_sse41" [(.buf "pr"), (.buf "blk"), (.const 64), (.const 0), (.var "f")]]] [
              .set "single" (.var "base")]] [
            .ite (.eq (.var "have_p") (.const 1)) [
              .set "single" (.buf "pr"),
              .set "have_p" (.const 0)] []]],
        .ite (.ne (.var "single") (.const 0)) [
          .ite (.eq (.var "have_c") (.const 1)) [
            .set "f" (.var "pf"),
            .ite (.eq (.var "m") (.const 1)) [
              .set "f" (.or (.var "pf") (.const 8))] [],
            .copy 32 (.buf "blk") (.var "single"),
            .copy 32 (.add (.buf "blk") (.const 32)) (.buf "acc"),
            .copy 32 (.buf "acc") (.var "key"),
            .ite (.eq (.var "plat") (.const 5)) [
              .call "blake3_servil_compress_in_place_avx512" [(.buf "acc"), (.buf "blk"), (.const 64), (.const 0), (.var "f")]] [
              .call "blake3_servil_compress_in_place_sse41" [(.buf "acc"), (.buf "blk"), (.const 64), (.const 0), (.var "f")]]] [
            .copy 32 (.buf "acc") (.var "single"),
            .set "have_c" (.const 1)]] [],
        .set "m" (.shr (.var "m") 1),
        .set "q" (.shr (.var "q") 1),
        .set "pw" (.add (.var "pw") (.var "pw")),
        .set "base" (.add (.var "base") (.const 64))],
      .copy 32 (.var "out") (.buf "acc")]]
  ret := (.const 0)
  noResult := true

def all : List Fn := [ladd, lroot, hash2]

/-- Each kernel written here, and the symbol it takes the place of. -/
def replaces : List (String × String) := []

def data : List (String × List Nat) := []

end Ode

def main (args : List String) : IO Unit :=
  match args with
  | ["rust", p] => IO.print (rustFile (rename p [] Ode.all))
  | ["asm", p] => IO.print (asmFile (rename p [] Ode.all) Ode.data)
  | ["asm", p, "own"] => IO.print (asmFile (rename p Ode.replaces Ode.all) Ode.data)
  | ["asm", p, "only", n] => IO.print (asmFile ((rename p [] Ode.all).filter (·.name == p ++ n)) (Ode.data.filter fun d => (Ode.all.filter (·.name == "b3l_" ++ n)).any fun f => f.body.any fun s => match s with | .ins t => (t.splitOn d.1).length > 1 | _ => false))
  | ["layout", n] => match Ode.all.find? (·.name == "b3l_" ++ n) with
    | some f => do
      let L := f.layout
      IO.println ("saved " ++ " ".intercalate L.saved)
      IO.println s!"frame {L.frame}"
      for x in f.params ++ f.locals do IO.println s!"home {x} {L.home x}"
      for b in f.bufs do IO.println s!"buf {b.1} {L.bufAt b.1}"
    | none => IO.eprintln "no such function"
  | _ => IO.eprintln "usage: rust PREFIX | asm PREFIX [own]"
