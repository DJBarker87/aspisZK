import Lean
import NFR_MemoryLimit
open Lean
namespace NGG_Coherence
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

end NGG_Coherence
unsafe def main (_args : List String) : IO UInt32 := do
 NFO_MemoryLimit.set
 initSearchPath (← findSysroot)
 enableInitializersExecution
 let env ← importModules ((#[`NFV_PoolReturnData,`NGG_Count,`NGG_Loader,`NGG_Compare,`NGG_Metadata,`NGG_Payer,`NGG_Transport,`NGG_Scalar,`NGG_LayoutValue,`NGG_DecodePrefix,`NGG_RequestLength,`NGG_LayoutBounds,`NGG_PaymentWindows,`NGG_EnvelopePrefix,`NGG_MarkerZero,`NGG_ErrorImage]).map (fun n => ({module := n, importAll := true} : Import))) {} (loadExts := true) (level := .private)
 let env := env.setExporting false
 let output ← IO.FS.Handle.mk "NGG_LOADED.jsonl" .write
 let mut failures := 0
 let mut declarations := 0
 let mut totalEdges := 0
 for idx in [0:env.header.moduleNames.size] do
  let name := env.header.moduleNames[idx]!
  let data := env.header.moduleData[idx]!
  let path ← findOLean name
  let mut missing : Array Json := #[]
  let mut edges := 0
  for declared in data.constants do
   declarations := declarations + 1
   let some c := env.checked.get.find? declared.name | do
    missing := missing.push (Json.mkObj [("parent",toJson declared.name.toString),("missing",toJson declared.name.toString)])
    continue
   for dep in NGG_Coherence.referenceNames c do
    edges := edges + 1
    if (env.checked.get.find? dep).isNone then
     missing := missing.push (Json.mkObj [("parent",toJson c.name.toString),("missing",toJson dep.toString)])
  totalEdges := totalEdges + edges
  failures := failures + missing.size
  output.putStrLn (Json.mkObj [("module",toJson name.toString),("path",toJson path.toString),("imports",toJson (data.imports.map (fun i => i.module.toString))), ("declarations",toJson data.constants.size),("edges",toJson edges),("dangling",toJson missing)]).compress
 IO.println (Json.mkObj [("modules",toJson env.header.moduleNames.size),("declarations",toJson declarations),("edges",toJson totalEdges),("dangling_references",toJson failures),("scope",toJson "local NGG/Pool closure; combined headline import FAILED B053; raw import lists and every unresolved reference, none waived")]).compress
 return if failures == 0 then 0 else 1
