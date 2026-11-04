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
/-- Same stable first-occurrence projection as NER_ModuleTables.inspect. -/
def canonicalImports (xs : Array String) : Array String := Id.run do
 let mut result := #[]
 for x in xs do
  if !result.contains x then result := result.push x
 return result
def importsMatch (actual expected : Array String) : Bool := canonicalImports actual == expected
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
  for declared in data.constants do
   let some c := env.checked.get.find? declared.name | do
    dangling := dangling.push (Json.mkObj [("parent",toJson declared.name.toString),("missing",toJson declared.name.toString),("phase",toJson "own_declaration")])
    continue
   let refs := referenceNames c
   for dep in refs do
    edges := edges + 1
    if (env.checked.get.find? dep).isNone then
     dangling := dangling.push (Json.mkObj [("parent",toJson c.name.toString),("missing",toJson dep.toString)])
  let loaderImports := data.imports.map (fun i => i.module.toString)
  let imports := canonicalImports loaderImports
  let importMatch := match expected[n.toString]? with
   | some baseline => imports == baseline
   | none => false
  if !dangling.isEmpty || !importMatch then failed := true
  out.putStrLn (Json.mkObj [("module",toJson n.toString), ("imports",toJson imports),
   ("loader_imports",toJson loaderImports), ("imports_match",toJson importMatch), ("dangling",toJson dangling),
   ("declarations",toJson data.constants.size), ("edges",toJson edges)]).compress
 return failed
end NER

unsafe def main (_ : List String) : IO UInt32 := do
 let raw := #["Init", "A", "Init", "B", "A"]
 unless NER.canonicalImports raw == #["Init", "A", "B"] do throw (IO.userError "bad stable import projection")
 for bad in #[#["Init", "A"], #["Init", "A", "B", "Extra"], #["A", "Init", "B"]] do
  if NER.importsMatch raw bad then throw (IO.userError "import mutation accepted")
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
   (NER.canonicalImports (env.header.moduleData[i]!.imports.map fun x => x.module.toString))
 let failed ← NER.loadedScan env "NER_V2_TEST_ROWS.jsonl" expected
 unless failed do throw (IO.userError "planted recursor reference was missed")
 let mut found := #[]
 for line in ← IO.FS.lines "NER_V2_TEST_ROWS.jsonl" do
  let j ← IO.ofExcept (Json.parse line)
  let ds ← IO.ofExcept (j.getObjValAs? (Array Json) "dangling")
  for d in ds do found := found.push (← IO.ofExcept (d.getObjValAs? String "missing"))
 unless found == #["NER_RecursorMissing"] do throw (IO.userError "unexpected recursor scan result")
 IO.println "NER_V2_REFERENCE_AND_IMPORT_MUTATIONS_PASS"
 return 0
