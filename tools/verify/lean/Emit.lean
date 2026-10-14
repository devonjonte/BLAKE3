import Sound
import Schedule
import Std.Data.HashMap

/-! `symbolic` (`Sound.lean`), written as a graph for `lean_spec.py`: each node once, as the
evaluation shared it. `Sound.lean` proves `symbolic` evaluates to the specification's compression
function under the meaning `Term.eval` gives each node, the meaning `lean_spec.py` gives it in Z3.
The specification's own outputs at a few inputs go beside the graph, so that `emit.py` checks this
printer and `lean_spec.py` against them. -/

/-- Nodes in order, each shared subterm once: sharing is the evaluation's own (a value read
twice is one object), found by address. -/
unsafe def graph (outs : List Term) : String := Id.run do
  let mut ids : Std.HashMap USize Nat := {}
  let mut nodes : Array String := #[]
  let mut stack : List (Term × Bool) := outs.reverse.map (·, false)
  while !stack.isEmpty do
    let (t, ready) := stack.head!
    stack := stack.tail!
    let key := ptrAddrUnsafe t
    if ids.contains key then continue
    let kids : List Term := match (t : Term) with
      | .add a b | .xor a b => [a, b]
      | .rotr a _ => [a]
      | _ => []
    if !ready && kids.any (fun k => !ids.contains (ptrAddrUnsafe k)) then
      stack := kids.map (·, false) ++ (t, true) :: stack
      continue
    let id (k : Term) : Nat := match ids[ptrAddrUnsafe k]? with
      | some n => n
      | none => panic! "a child written after its parent"
    let node : String := match (t : Term) with
      | .var n => s!"[\"var\", \"{n}\"]"
      | .const v => s!"[\"const\", {v}]"
      | .add a b => s!"[\"add\", {id a}, {id b}]"
      | .xor a b => s!"[\"xor\", {id a}, {id b}]"
      | .rotr a n => s!"[\"rotr\", {id a}, {n}]"
      | .low c => s!"[\"low\", \"{c}\"]"
      | .high c => s!"[\"high\", \"{c}\"]"
    ids := ids.insert key nodes.size
    nodes := nodes.push node
  let outIds := outs.map fun o => toString ids[ptrAddrUnsafe o]!
  return "{\"nodes\": [\n" ++ ",\n".intercalate nodes.toList ++ "\n],\n\"outputs\": [" ++ ", ".intercalate outIds ++ "]}\n"

@[implemented_by graph] opaque graphSafe (outs : List Term) : String

/-- Sample inputs: words from a fixed sequence (i * 0x9E3779B9 + k), the counter likewise. -/
def sample (k : Nat) : (String → UInt32) × UInt64 :=
  let word (n : Nat) : UInt32 := (n * 0x9E3779B9 + 977 * k + 1).toUInt32
  (fun name => word (name.hash.toNat % 1000003), (k * 0x9E3779B97F4A7C15 + 5).toUInt64)

/-- An entry of `Schedule.sched`, as `whole.py` reads it: `[h, m, t, len, flags]`, `h` the
key's words (`-1`) or entry `e`'s chaining value (`e`), `m` input words `j` to `j + 15` (`j`)
or entries `l`'s and `r`'s chaining values (`[l, r]`). Any other shape stops the printer. -/
def entryJson (e : Schedule.Entry) : String :=
  let h := if e.h = (List.range 8).map Schedule.Src.key then "-1" else match e.h with
    | Schedule.Src.cv x 0 :: _ => if e.h = (List.range 8).map (Schedule.Src.cv x) then toString x else panic! "an unexpected h"
    | _ => panic! "an unexpected h"
  let m := match e.m with
    | Schedule.Src.msg j :: _ => if e.m = (List.range 16).map (fun k => Schedule.Src.msg (j + k)) then toString j else panic! "an unexpected m"
    | Schedule.Src.cv l 0 :: _ => match e.m[8]? with
      | some (Schedule.Src.cv r 0) =>
        if e.m = (List.range 8).map (Schedule.Src.cv l) ++ (List.range 8).map (Schedule.Src.cv r) then s!"[{l}, {r}]"
        else panic! "an unexpected m"
      | _ => panic! "an unexpected m"
    | _ => panic! "an unexpected m"
  s!"[{h}, {m}, {e.t}, {e.len}, {e.flags}]"

/-- `compress.json`, `samples.json`, then with a third path and input lengths, the schedules of
those lengths (`ScheduleProofs.lean`'s `run_eq`) as `{"n": [entry, ...], ...}`. -/
def main (args : List String) : IO Unit := do
  IO.FS.writeFile (args.head!) (graphSafe symbolic.toList)
  -- The specification's outputs at the samples, with the inputs that gave them.
  let names := (List.range 8).map (s!"h{·}") ++ (List.range 16).map (s!"m{·}") ++ ["len", "flags"]
  let rows := (List.range 4).map fun k =>
    let (env, t) := sample k
    let out := Blake3.BLAKE3_COMPRESS (Vector.ofFn fun i => env s!"h{i.val}") (Vector.ofFn fun i => env s!"m{i.val}")
      t (env "len") (env "flags")
    let ins := ", ".intercalate (names.map fun n => s!"\"{n}\": {(env n).toNat}")
    s!"\{\"inputs\": \{{ins}, \"t\": {t.toNat}}, \"outputs\": {out.toList.map (·.toNat)}}"
  IO.FS.writeFile (args[1]!) ("[\n" ++ ",\n".intercalate rows ++ "\n]\n")
  if let some (path : String) := args[2]? then
    let rows := (args.drop 3).map fun n =>
      s!"\"{n}\": [" ++ ", ".intercalate ((Schedule.sched n.toNat!).map entryJson) ++ "]"
    IO.FS.writeFile path ("{\n" ++ ",\n".intercalate rows ++ "\n}\n")
