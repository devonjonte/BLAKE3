import ReadingList
open Lean Elab Command Meta

/-! `#reading_core T`: the part of Lean's own library that the statement of `T` depends on, in lines:
the definitions reached from the statement that live in Lean's `Init`, `Std` and `Lean` modules, by the
same walk as `#reading_list` (a definition's type and body; an inductive type's constructors; never a
proof). One line a module group, then the total. -/

namespace ReadingList

elab "#reading_core " id:ident : command => do
  let env ← getEnv
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some info := env.find? name | throwError "unknown"
  let all := walk env (constsOf info.type).toList {}
  let mut perMod : Std.HashMap String (Nat × Nat) := {}
  let mut total := 0
  let mut count := 0
  let mut norange := 0
  for c in all.toList do
    let m := match env.getModuleIdxFor? c with
      | some i => env.header.moduleNames[i.toNat]!
      | none => env.mainModule
    unless isCore m do continue
    if c.isInternalDetail || (c matches .str _ "rec") || (c matches .str _ "casesOn") || (c matches .str _ "recOn") then continue
    if env.isProjectionFn c || (env.find? c matches some (.ctorInfo _)) then continue
    let lines ← liftCoreM do
      match ← findDeclarationRanges? c with
      | some r => pure (r.range.endPos.line - r.range.pos.line + 1)
      | none => pure 0
    if lines == 0 then norange := norange + 1
    let comps := m.components.map toString
    let key := ".".intercalate (comps.take 3)
    let (k, n) := perMod.getD key (0, 0)
    perMod := perMod.insert key (k + 1, n + lines)
    total := total + lines
    count := count + 1
  let mods := perMod.toArray.qsort (fun a b => a.2.2 > b.2.2)
  let mut msg := m!"core of `{name}`: {count} definitions, {total} lines ({norange} without a place in a file)\n"
  for (m, (k, n)) in mods.toList.take 14 do
    msg := msg ++ m!"  {m}: {k} definitions, {n} lines\n"
  logInfo msg

end ReadingList
