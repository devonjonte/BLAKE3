/-! # `Params.new?` of craftsoldier/equihash-lean, copied

Copied character for character from `Equihash/Verifier/Params.lean` (lines 20–34) of
https://github.com/craftsoldier/equihash-lean at commit 5f468f0, Copyright 2026 Julian Abraham,
MIT OR Apache-2.0: its Lean transcription of `Params::new` of `zakura-equihash 4.0.0`
(`src/params.rs`, lines 9–30). A copy only because that repository builds with Mathlib and Lean
4.35 and this folder with neither; the next step is to import it. `ℕ` there is Mathlib's notation
for `Nat`. -/

namespace Equihash.Verifier

local notation "ℕ" => Nat

structure Params where
  n : ℕ
  k : ℕ

namespace Params

/-- `Params::new` (lines 9–30): the parameters, when they are ones the verifier supports. -/
def new? (n k : ℕ) : Option Params :=
  if n % 8 = 0 ∧ k ≥ 3 ∧ k < n ∧ n % (k + 1) = 0 ∧ n ≤ 512 ∧
      8 ≤ n / (k + 1) ∧ n / (k + 1) ≤ 24 then
    some { n, k }
  else none

end Params

end Equihash.Verifier
