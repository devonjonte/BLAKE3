import Lean
open Lean Elab Command Meta

/-! # What must be read to know what a theorem says

`#reading_list T` asks Lean, not a person's bookkeeping: which definitions does the *statement* of `T`
depend on, through every definition those use, and which axioms does its proof rest on? That is what a
reader must read and judge. Everything else in the project (every lemma, every proof, every tactic,
every generator) is checked by Lean's kernel on the way to `T` and need not be read.

Followed: a definition's type and body; an inductive type's constructors; a structure's fields. Not
followed: the proof of any theorem (only its statement, should a statement mention one). -/

namespace ReadingList

def constsOf (e : Expr) : Array Name := e.getUsedConstants

partial def walk (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | c :: rest =>
    if seen.contains c then walk env rest seen else
    let seen := seen.insert c
    match env.find? c with
    | none => walk env rest seen
    | some info =>
      let more : Array Name := constsOf info.type ++ (match info with
        | .defnInfo d => constsOf d.value
        | .inductInfo i => i.ctors.toArray
        | .ctorInfo k => #[k.induct]
        | _ => #[])
      walk env (more.toList ++ rest) seen

/-- Is this module part of Lean itself (its core library), not of this project? -/
def isCore (m : Name) : Bool := [`Init, `Std, `Lean].contains m.getRoot

elab "#reading_list " id:ident : command => do
  let env ← getEnv
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some info := env.find? name | throwError "unknown"
  let all := walk env (constsOf info.type).toList {}
  let mut perMod : Std.HashMap Name (Array Name × Nat) := {}
  let mut core := 0
  for c in all.toList do
    let m := match env.getModuleIdxFor? c with
      | some i => env.header.moduleNames[i.toNat]!
      | none => env.mainModule
    if isCore m then core := core + 1 else
      -- generated helpers (matchers, recursors, equation lemmas) are counted with what they belong to
      if c.isInternalDetail || (c matches .str _ "rec") || (c matches .str _ "casesOn") || (c matches .str _ "recOn") then continue
      -- a structure's fields and constructor are lines of the structure itself
      if env.isProjectionFn c || (env.find? c matches some (.ctorInfo _)) then continue
      let lines ← liftCoreM do
        match ← findDeclarationRanges? c with
        | some r => pure (r.range.endPos.line - r.range.pos.line + 1)
        | none => pure 0
      let (cs, n) := perMod.getD m (#[], 0)
      perMod := perMod.insert m (cs.push c, n + lines)
  let axioms ← liftCoreM <| collectAxioms name
  let mods := perMod.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let total : Nat := mods.foldl (fun (n : Nat) (x : Name × Array Name × Nat) => n + x.2.2) 0
  let ndefs : Nat := mods.foldl (fun (n : Nat) (x : Name × Array Name × Nat) => n + x.2.1.size) 0
  let mut msg := m!"To know what `{name}` says, read {ndefs} definitions ({total} lines) in {mods.size} files:\n"
  for (m, (cs, l)) in mods do
    let names := (cs.qsort (fun a b => a.toString < b.toString)).toList.map toString
    msg := msg ++ m!"  {m}: {cs.size} definitions, {l} lines: {", ".intercalate (names.take 12)}{if names.length > 12 then ", ..." else ""}\n"
  msg := msg ++ m!"and trust: Lean's kernel and core library ({core} of its definitions are used), and {axioms.size} axioms:\n"
  let std := axioms.filter (fun a => [`propext, `Classical.choice, `Quot.sound].contains a)
  let other := axioms.filter (fun a => !([`propext, `Classical.choice, `Quot.sound].contains a))
  msg := msg ++ m!"  {std.size} standard ({", ".intercalate (std.toList.map toString)}); {other.size} others" ++
    (if other.isEmpty then m!"" else m!" (each says: a compiled checker accepted a solver's certificate), e.g. {other[0]!}")
  logInfo msg

/-- The same, as data: one line a definition (`def MODULE NAME LINES`) and one an axiom, for tools that
compare what two theorems' statements depend on. -/
elab "#reading_defs " id:ident : command => do
  let env ← getEnv
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let some info := env.find? name | throwError "unknown"
  let all := walk env (constsOf info.type).toList {}
  let mut out : Array String := #[]
  for c in all.toList do
    let m := match env.getModuleIdxFor? c with
      | some i => env.header.moduleNames[i.toNat]!
      | none => env.mainModule
    if isCore m then continue
    if c.isInternalDetail || (c matches .str _ "rec") || (c matches .str _ "casesOn") || (c matches .str _ "recOn") then continue
    if env.isProjectionFn c || (env.find? c matches some (.ctorInfo _)) then continue
    let lines ← liftCoreM do
      match ← findDeclarationRanges? c with
      | some r => pure (r.range.endPos.line - r.range.pos.line + 1)
      | none => pure 0
    out := out.push s!"def {m} {c} {lines}"
  for a in ← liftCoreM <| collectAxioms name do out := out.push s!"axiom {a}"
  logInfo ("\n".intercalate out.toList)

end ReadingList
