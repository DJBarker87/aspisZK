import Lean
import NFR_MemoryLimit
open Lean
namespace NFV_Coherence
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

end NFV_Coherence
unsafe def main (_args : List String) : IO UInt32 := do
 NFO_MemoryLimit.set
 initSearchPath (← findSysroot)
 enableInitializersExecution
 let env ← importModules #[{module := `NFV_Accounts, importAll := true},{module := `NFV_HelperModel, importAll := true},{module := `NFV_Copy, importAll := true},{module := `NFV_ListFrames, importAll := true},{module := `NFV_Envelope, importAll := true},{module := `NFV_RequestWindows, importAll := true},{module := `NFV_RequestOracle, importAll := true},{module := `NFV_RequestIndexes, importAll := true},{module := `NFV_RequestGuards, importAll := true},{module := `NFV_PoolReturnData, importAll := true},{module := `NFR_AfterstateForward, importAll := true},{module := `NFR_AfterstateForward00, importAll := true},{module := `NFR_AfterstateForward04, importAll := true},{module := `NFR_AfterstateForward08, importAll := true},{module := `NFR_AfterstateForward12, importAll := true},{module := `NFR_AfterstateForward16, importAll := true},{module := `NFR_AfterstateForwardHelpers, importAll := true},{module := `NFR_CHelper, importAll := true},{module := `NFR_CHelperBridge, importAll := true},{module := `NFR_CSettlement, importAll := true},{module := `NFR_DigestForward, importAll := true},{module := `NFR_ExtractedDecode, importAll := true},{module := `NFR_ModelJoin, importAll := true},{module := `NFR_PoolReturnData, importAll := true},{module := `NFR_RawInverse, importAll := true},{module := `NFR_RawInverseFrames, importAll := true},{module := `NFR_RawInverseHelpers, importAll := true},{module := `NFR_RawInverseValidator, importAll := true},{module := `NFR_ResultForward, importAll := true},{module := `NFR_ResultForwardHelpers, importAll := true}] {} (loadExts := true) (level := .private)
 let env := env.setExporting false
 let output ← IO.FS.Handle.mk "NFV_LOADED.jsonl" .write
 let mut failures := 0
 let mut declarations := 0
 let mut totalEdges := 0
 for idx in [0:env.header.moduleNames.size] do
  let name := env.header.moduleNames[idx]!
  let data := env.header.moduleData[idx]!
  let mut missing : Array Json := #[]
  let mut edges := 0
  for declared in data.constants do
   declarations := declarations + 1
   let some c := env.checked.get.find? declared.name | do
    missing := missing.push (Json.mkObj [("parent",toJson declared.name.toString),("missing",toJson declared.name.toString)])
    continue
   for dep in NFV_Coherence.referenceNames c do
    edges := edges + 1
    if (env.checked.get.find? dep).isNone then
     missing := missing.push (Json.mkObj [("parent",toJson c.name.toString),("missing",toJson dep.toString)])
  totalEdges := totalEdges + edges
  failures := failures + missing.size
  output.putStrLn (Json.mkObj [("module",toJson name.toString),("imports",toJson (data.imports.map (fun i => i.module.toString))), ("declarations",toJson data.constants.size),("edges",toJson edges),("dangling",toJson missing)]).compress
 IO.println (Json.mkObj [("modules",toJson env.header.moduleNames.size),("declarations",toJson declarations),("edges",toJson totalEdges),("dangling_references",toJson failures),("scope",toJson "loaded NFV and inherited NFR closure; raw import lists reported, no independent upstream import baseline comparison")]).compress
 return if failures == 0 then 0 else 1
