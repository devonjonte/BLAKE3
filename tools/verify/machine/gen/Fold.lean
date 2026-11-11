/-! The fold and the scan of a function of the carried value and a word: what the language's loop means. -/

def foldW (f : BitVec 32 → BitVec 32 → BitVec 32) (a : BitVec 32) : List (BitVec 32) → BitVec 32
  | [] => a
  | w :: ws => foldW f (f a w) ws

def scanW (f : BitVec 32 → BitVec 32 → BitVec 32) (a : BitVec 32) : List (BitVec 32) → List (BitVec 32)
  | [] => []
  | w :: ws => f a w :: scanW f (f a w) ws
