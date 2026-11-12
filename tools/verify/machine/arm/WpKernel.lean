import Arm64
import ProofLib
import KernelAttr
open Arm64 ProofLib

/-! # Two lemmas the compiler's proofs of kernels use, over Google's proof library (not to be read) -/

/-- Eight turns of a loop that never stops early, written out (their vector permutes are such loops). -/
theorem forIn_range8_yield {β : Type} (init : β) (g : Nat → β → β) :
    (forIn (m := Id) [:8] init (fun i s => pure (ForInStep.yield (g i s)))) =
      pure (g 7 (g 6 (g 5 (g 4 (g 3 (g 2 (g 1 (g 0 init)))))))) := by
  simp [List.range']

/-- The spatial context may be replaced by an equal one: by the specification's, which leaves the
equalities of values as goals (their `wp_done` closes only those it can, and hands none back). -/
theorem SepWP.of_eq {prog : Program} {target_pc : BitVec 64} {s : State} {P P' : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : P = P') (hw : SepWP prog target_pc s P' post oom) : SepWP prog target_pc s P post oom := h ▸ hw
