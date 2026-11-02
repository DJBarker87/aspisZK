import Lean
import NER_Walker
open Lean
namespace NER
/-- Inspect each module's own declarations against the checked private environment. -/
def loadedScan (env : Environment) (output : System.FilePath)
    (expected : Std.HashMap String (Array String)) : IO Bool := do
 let env := env.setExporting false
 let out ← IO.FS.Handle.mk output .write
 let mut failed := false
 for h : idx in [0:env.header.moduleNames.size] do
  let n := env.header.moduleNames[idx]
  let data := env.header.moduleData[idx]!
  let mut dangling : Array Json := #[]
  let mut edges := 0
  for c in data.constants do
   let mut refs := c.type.getUsedConstants ++ ((c.value? true).map Expr.getUsedConstants).getD #[]
   if let .inductInfo v := c then refs := refs ++ v.ctors.toArray
   for dep in refs do
    edges := edges + 1
    if (env.checked.get.find? dep).isNone then
     dangling := dangling.push (Json.mkObj [("parent",toJson c.name.toString),("missing",toJson dep.toString)])
  let imports := data.imports.map (fun i => i.module.toString)
  let importMatch := match expected[n.toString]? with
   | some baseline => imports == baseline
   | none => false
  if !dangling.isEmpty || !importMatch then failed := true
  out.putStrLn (Json.mkObj [("module",toJson n.toString), ("imports",toJson imports),
   ("imports_match",toJson importMatch), ("dangling",toJson dangling),
   ("declarations",toJson data.constants.size), ("edges",toJson edges)]).compress
 return failed
end NER

open Lean Elab Command
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let modules := #[`RPx_Deployed, `NDR_CombinedAudit]
  let roots := #[`AspisR1.RPx_Deployed.deployed, `AspisR1.NDR_CombinedAudit.sourceOnHeadline]
  let mode := "final"
  let env ← importModules (modules.map fun n => ({module := n, importAll := true} : Import))
    {} (loadExts := true) (level := .private)
  let mut expected : Std.HashMap String (Array String) := {}
  for line in ← IO.FS.lines "NER_MANIFEST.jsonl" do
    let j ← IO.ofExcept (Json.parse line)
    expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
      (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
  let scanFailed ← NER.loadedScan env "NER_LOADED_final.jsonl" expected
  if scanFailed then
    IO.eprintln "NER_SCAN_FAILED"
    return 3
  IO.println "NER_SCAN_ZERO_DANGLING"
  let ctx : Command.Context := {
    fileName := "NEP_Driver"
    fileMap := FileMap.ofString ""
    snap? := none
    cancelTk? := none
  }
  let action : CommandElabM Bool := do
    let mut failed := false
    for root in roots do
      try
        elabCommand (← `(command| #print axioms $(mkIdent root)))
        NEP.audit root ("NER_" ++ mode ++ "_" ++ root.toString)
      catch e =>
        logError e.toMessageData
        failed := true
    return failed
  let result ← ((action.run ctx).run (Command.mkState env)).toBaseIO
  match result with
  | .error e =>
    IO.eprintln (← e.toMessageData.toString)
    return 2
  | .ok (failed, state) =>
    for msg in state.messages.toList do IO.println (← msg.data.toString)
    return if failed then 1 else 0
