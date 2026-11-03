import Lean
import NER_Walker
open Lean
namespace NER
/-- Include recursor reduction rules and constant-name metadata, not only values. -/
def referenceNames (c : ConstantInfo) : Array Name := Id.run do
 let mut refs := c.type.getUsedConstants ++ ((c.value? true).map Expr.getUsedConstants).getD #[]
 match c with
 | .defnInfo v => refs := refs ++ v.all.toArray
 | .thmInfo v => refs := refs ++ v.all.toArray
 | .opaqueInfo v => refs := refs ++ v.all.toArray
 | .inductInfo v => refs := refs ++ v.ctors.toArray ++ v.all.toArray
 | .ctorInfo v => refs := refs.push v.induct
 | .recInfo v =>
  refs := refs ++ v.all.toArray
  for rule in v.rules do refs := refs.push rule.ctor ++ rule.rhs.getUsedConstants
 | _ => pure ()
 return refs
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
   let refs := referenceNames c
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

unsafe def main (_ : List String) : IO UInt32 := do
 let env ← importModules #[{module:=`Init,importAll:=true}] {} (loadExts:=false) (level:=.private)
 let some (.recInfo v) := env.checked.get.find? `Nat.rec | throw (IO.userError "missing Nat.rec")
 for (mod, missing) in #[(`NER_RecursorPlant, true), (`NER_RecursorControl, false)] do
  let c := ConstantInfo.recInfo {v with
   name := Name.str mod "rec"
   rules := [{ctor:=`Nat.zero,nfields:=0,rhs:=mkConst (if missing then `NER_RecursorMissing else `Nat.zero)}]}
  saveModuleData (mod.toString ++ ".olean") mod {
   isModule:=false,imports:=#[{module:=`Init}],constants:=#[c],constNames:=#[c.name],extraConstNames:=#[],entries:=#[]}
 let env ← importModules #[{module:=`NER_RecursorPlant,importAll:=true},{module:=`NER_RecursorControl,importAll:=true}]
   {} (loadExts:=false) (level:=.private)
 let mut expected : Std.HashMap String (Array String) := {}
 for h : i in [0:env.header.moduleNames.size] do
  expected := expected.insert env.header.moduleNames[i].toString
   (env.header.moduleData[i]!.imports.map fun x => x.module.toString)
 let failed ← NER.loadedScan env "NER_RECURSOR_TEST_ROWS.jsonl" expected
 unless failed do throw (IO.userError "planted recursor reference was missed")
 let mut found := #[]
 for line in ← IO.FS.lines "NER_RECURSOR_TEST_ROWS.jsonl" do
  let j ← IO.ofExcept (Json.parse line)
  let ds ← IO.ofExcept (j.getObjValAs? (Array Json) "dangling")
  for d in ds do found := found.push (← IO.ofExcept (d.getObjValAs? String "missing"))
 unless found == #["NER_RecursorMissing"] do throw (IO.userError "unexpected recursor scan result")
 IO.println "NER_RECURSOR_MUTATION_PASS"
 return 0
