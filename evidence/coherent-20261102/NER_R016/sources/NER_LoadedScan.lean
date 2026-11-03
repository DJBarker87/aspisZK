import Lean
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
  let matches := match expected[n.toString]? with
   | some baseline => imports == baseline
   | none => false
  if !dangling.isEmpty || !matches then failed := true
  out.putStrLn (Json.mkObj [("module",toJson n.toString), ("imports",toJson imports),
   ("imports_match",toJson matches), ("dangling",toJson dangling),
   ("declarations",toJson data.constants.size), ("edges",toJson edges)]).compress
 return failed
end NER
unsafe def main (args : List String) : IO UInt32 := do
 enableInitializersExecution
 let mode := args.headD "fixtures"
 let roots := if mode == "fixtures" then #[`Init, `NER_PlantObject, `NER_PlantControl]
   else #[`RPx_Deployed, `NDR_CombinedAudit]
 let env ← importModules (roots.map fun n => ({module:=n,importAll:=true} : Import))
   {} (loadExts:=true) (level:=.private)
 let mut expected : Std.HashMap String (Array String) := {}
 if mode == "fixtures" then
  for h : i in [0:env.header.moduleNames.size] do
   expected := expected.insert env.header.moduleNames[i].toString
    (env.header.moduleData[i]!.imports.map (fun x => x.module.toString))
 else
  for line in ← IO.FS.lines "NER_MANIFEST.jsonl" do
   let j ← IO.ofExcept (Json.parse line)
   expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
    (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
 let failed ← NER.loadedScan env ("NER_LOADED_" ++ mode ++ ".jsonl") expected
 return if failed then 1 else 0
