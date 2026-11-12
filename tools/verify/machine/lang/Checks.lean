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

/-- `#pieces NAME` prints the contract `NAME` in parts, as text: its parameters, what it accepts, each
piece of memory (the layout, the address, the value before and after) and what it returns. The tool that
tries a function on examples makes its tests from these lines, so they follow the contract. -/
elab "#pieces " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some (.defnInfo d) := (← getEnv).find? name | throwError "{name} is not a definition"
  let lines ← liftTermElabM <| lambdaTelescope d.value fun params body => do
    let body ← instantiateMVars body
    let fields := getStructureFields (← getEnv) ``Abi.Contract
    let xs := body.getAppArgs
    unless body.isAppOf ``Abi.Contract.mk && xs.size == fields.size do throwError "{name} is not written as a contract's fields"
    let field (f : Name) : MetaM Expr := do
      let some i := fields.findIdx? (· == f) | throwError "no field {f}"
      return xs[i]!
    let show_ (e : Expr) : MetaM String := do return (← ppExpr e).pretty 100000
    let mut out : Array String := #[]
    for p in params do
      out := out.push s!"param {← p.fvarId!.getUserName} : {← show_ (← inferType p)}"
    out := out.push s!"accepts {← show_ (← field `accepts)}"
    for (kind, f) in [("read", `reads), ("update", `updates)] do
      for piece in listElems (← field f) do
        match piece.getAppFnArgs with
        | (``Abi.Layout.keeps, #[_, l, a, v]) => out := out.push s!"{kind} | {← show_ l} | {← show_ a} | {← show_ v} | {← show_ v}"
        | (``Abi.Layout.turns, #[_, l, a, v, w]) => out := out.push s!"{kind} | {← show_ l} | {← show_ a} | {← show_ v} | {← show_ w}"
        | (``Abi.Layout.fills, #[_, l, a, w]) => out := out.push s!"fill | {← show_ l} | {← show_ a} | - | {← show_ w}"
        | _ => throwError "a piece is neither `keeps`, `turns` nor `fills`: {piece}"
    let ret ← lambdaTelescope (← field `returns) fun rs b => do
      return s!"returns {← rs[0]!.fvarId!.getUserName} | {← show_ b}"
    return out.push ret
  logInfo ("\n".intercalate lines.toList)

end Checks
