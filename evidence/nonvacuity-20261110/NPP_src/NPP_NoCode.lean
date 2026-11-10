import Lean
/-! NPP_ read-only scan (native tool): the no-code closure of the given roots, i.e. definitions
without compiled IR that are reached through definition values from the roots, excluding type
formers and propositions, and excluding core/Std/Mathlib/Batteries constants. This is the
compiler's criterion; the NPO_L035 scan used the noncomputable tag, which imported definitions from
a `noncomputable section` need not carry. Output NPP_NOCODE.json. -/
open Lean Meta

def isLib (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => [`Init, `Lean, `Std, `Mathlib, `Batteries].contains (env.header.moduleNames[i.toNat]!).getRoot
  | none => false

/-- the codomain of a Pi type is a sort (a type former) -/
partial def endsInSort : Expr → Bool
  | .forallE _ _ b _ => endsInSort b
  | .sort _ => true
  | _ => false

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `NNH_ReturnsBundle}, {module := `NNG_TotalProducer345},
    {module := `NNH_Run6Installed}] {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "NPP_NoCode", fileMap := default, maxHeartbeats := 0 }
  let st : Core.State := { env }
  let act : MetaM (Array Json) := do
    let mut seen : Std.HashSet Name := {}
    let mut stack := (args.map String.toName).toArray
    let mut rows : Array Json := #[]
    while h : stack.size > 0 do
      let n := stack.back; stack := stack.pop
      if seen.contains n then continue
      seen := seen.insert n
      if isLib env n then continue
      let some ci := env.find? n | continue
      let .defnInfo d := ci | continue
      if (Lean.IR.findEnvDecl env n).isSome then continue
      if endsInSort d.type then continue
      let isP ← try isProp d.type catch _ => pure false
      if isP then continue
      let deps := d.value.getUsedConstants
      let classical := deps.filter fun c => c.getRoot == `Classical || c == ``Exists.choose
      rows := rows.push (Json.mkObj [("n", toJson n.toString), ("classical", toJson (classical.map toString))])
      for c in deps do stack := stack.push c
    return rows
  let (rows, _) ← (act.run' {} {}).toIO ctx st
  IO.FS.writeFile "NPP_NOCODE.json" (Json.arr rows).pretty
  IO.println s!"nocode={rows.size}"
  return 0
