import Lean
import Abi
open Lean Elab Command Meta

/-! # What a contract accepts, read from the contract itself

`#checks NAME` reads the `accepts` field of the contract `NAME` (a conjunction of comparisons of the
arguments and numbers) and prints one line a comparison. The compiler makes the checked entry's code from
these lines, so what is tested is stated once, in the contract. Nothing here is trusted: the code made
from the lines is proved against the contract. -/

namespace Checks

partial def listElems (e : Expr) : List Expr :=
  match e.getAppFnArgs with
  | (``List.cons, #[_, h, t]) => h :: listElems t
  | _ => []

partial def conjuncts (e : Expr) : List Expr :=
  match e.getAppFnArgs with
  | (``And, #[a, b]) => conjuncts a ++ conjuncts b
  | _ => [e]

/-- An operand: an argument (its position and name) or a number. -/
def operand (args : List Expr) (e : Expr) : MetaM String := do
  if let some i := args.findIdx? (· == e) then
    if i < args.length then
      let n ← e.fvarId!.getUserName
      return s!"@{i}:{n}"
  match ← getBitVecValue? e with
  | some ⟨_, v⟩ => return s!"#{v.toNat}"
  | none => throwError "an operand of `accepts` is neither an argument nor a number: {e}"

elab "#checks " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some (.defnInfo d) := (← getEnv).find? name | throwError "{name} is not a definition"
  let lines ← liftTermElabM <| lambdaTelescope d.value fun _ body => do
    let body ← instantiateMVars body
    let fields := getStructureFields (← getEnv) ``Abi.Contract
    let some ia := fields.findIdx? (· == `args) | throwError "no args"
    let some ic := fields.findIdx? (· == `accepts) | throwError "no accepts"
    let xs := body.getAppArgs
    unless body.isAppOf ``Abi.Contract.mk && xs.size == fields.size do throwError "{name} is not written as a contract's fields"
    let args := listElems xs[ia]!
    let mut out : Array String := #[]
    for c in conjuncts xs[ic]! do
      if c.isConstOf ``True then continue
      let (op, a, b) ← match c.getAppFnArgs with
        | (``LE.le, #[_, _, a, b]) => pure ("le", a, b)
        | (``LT.lt, #[_, _, a, b]) => pure ("lt", a, b)
        | (``GE.ge, #[_, _, a, b]) => pure ("le", b, a)
        | (``GT.gt, #[_, _, a, b]) => pure ("lt", b, a)
        | _ => throwError "`accepts` has a part that is not a comparison: {c}"
      out := out.push s!"check {op} {← operand args a} {← operand args b}"
    return out
  logInfo ("\n".intercalate lines.toList)

end Checks
