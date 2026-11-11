import Fold

/-! # A function is written here, in Lean; its Rust is printed from it

A very small language of 32-bit words: enough for the body of a loop over a slice. A term has
one meaning, `Exp.eval`, an ordinary Lean function; and one printing, `Exp.rust`. The printed
Rust is not trusted: what is proved is that the machine code rustc makes of it computes `eval`. -/

inductive Exp
  /-- The value carried from word to word. -/
  | acc
  /-- The word of the slice. -/
  | word
  | lit (v : BitVec 32)
  | xor (a b : Exp)
  | add (a b : Exp)
  | and (a b : Exp)
  | or (a b : Exp)
  | not (a : Exp)
  | rotl (a : Exp) (n : Nat)
  | shr (a : Exp) (n : Nat)

namespace Exp

/-- What a term means, given the carried value and the word. -/
def eval (a w : BitVec 32) : Exp → BitVec 32
  | acc => a
  | word => w
  | lit v => v
  | xor x y => x.eval a w ^^^ y.eval a w
  | add x y => x.eval a w + y.eval a w
  | and x y => x.eval a w &&& y.eval a w
  | or x y => x.eval a w ||| y.eval a w
  | not x => ~~~ x.eval a w
  | rotl x n => (x.eval a w).rotateLeft n
  | shr x n => x.eval a w >>> n

/-- The term as a Rust expression over `a: u32` and `w: u32`. -/
def rust : Exp → String
  | acc => "a"
  | word => "w"
  | lit v => s!"{v.toNat}u32"
  | xor x y => s!"({x.rust} ^ {y.rust})"
  | add x y => s!"{x.rust}.wrapping_add({y.rust})"
  | and x y => s!"({x.rust} & {y.rust})"
  | or x y => s!"({x.rust} | {y.rust})"
  | not x => s!"(!{x.rust})"
  | rotl x n => s!"{x.rust}.rotate_left({n})"
  | shr x n => s!"({x.rust} >> {n})"

end Exp

/-- A function over a slice of words: each word is replaced by the body's value, which is also
carried to the next word; the last value is returned. -/
structure Scan where
  name : String
  body : Exp

namespace Scan

/-- The body as a function of the carried value and the word. -/
def step (f : Scan) (a w : BitVec 32) : BitVec 32 := f.body.eval a w

/-- The value returned: the body folded over the words. -/
def fold (f : Scan) : BitVec 32 → List (BitVec 32) → BitVec 32 := foldW f.step

/-- The words left in the slice. -/
def scan (f : Scan) : BitVec 32 → List (BitVec 32) → List (BitVec 32) := scanW f.step

/-- The function as Rust. -/
def rust (f : Scan) : String :=
  s!"#[no_mangle]\npub fn {f.name}(words: &mut [u32], seed: u32) -> u32 \{\n    let mut a = seed;\n    for word in words.iter_mut() \{\n        let w = *word;\n        a = {f.body.rust};\n        *word = a;\n    }\n    a\n}\n"

end Scan

/-! The functions of this experiment. -/

/-- The first experiment's loop: rotate, xor. -/
def rotxor : Scan := ⟨"rotxor", .xor (.rotl .acc 5) .word⟩

/-- An addition, a rotation and the carried value twice. -/
def addrot : Scan := ⟨"addrot", .xor (.rotl (.add .acc .word) 7) .acc⟩

/-- A choice between the bits of two values, by a constant mask, and a shift. -/
def mix : Scan := ⟨"mix", .add (.or (.and .acc (.lit 0x0F0F0F0F)) (.and (.not .word) (.lit 0xF0F0F0F0))) (.shr .word 3)⟩

/-- A running sum. -/
def sum : Scan := ⟨"sum", .add .acc .word⟩

/-- Two additions, a constant and a rotation: the shape of a quarter of BLAKE3's G. -/
def quarter : Scan := ⟨"quarter", .xor (.rotl (.add (.add .acc .word) (.lit 0x9E3779B9)) 16) .word⟩

/-- And, or, and a rotation of the word. -/
def blend : Scan := ⟨"blend", .or (.and .acc .word) (.rotl .word 13)⟩

/-- A complement of a sum. -/
def invert : Scan := ⟨"invert", .not (.add .acc (.rotl .word 1))⟩

/-- A shift of the carried value into the word. -/
def shift : Scan := ⟨"shift", .xor (.shr .acc 3) (.add .word .acc)⟩

def all : List Scan := [rotxor, addrot, mix, sum, quarter, blend, invert, shift]

def main : IO Unit := IO.print (String.join (all.map Scan.rust))
