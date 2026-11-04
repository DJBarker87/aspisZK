import Lean
import NFA_WALKER
import NFA_MemoryLimit
open Lean Elab Command
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

/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  NFA_MemoryLimit.set
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    if mode == "proof0" then
      (#[`NFS_COMBINED_IMPORT], #[`NFS_NEV_AccumPacket.raw_length, `NFS_NEV_AccumPacket.result_state_effects, `NFS_NEV_AccumPacket.no_base_dependency, `NFS_NEV_AccumulateComplete.reference])
    else if mode == "proof1" then
      (#[`NFS_COMBINED_IMPORT], #[`NFS_NEV_AccumulateComplete.native, `AspisR1.RPx_Deployed.deployed, `AspisR1.NFM_ProductInstance.installed, `AspisR1.NFM_ProductInstance.wrapper])
    else if mode == "proof2" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFG_QueryLoopSource.complete, `NFN_NFB_GeometryComposed.result_state_effects, `AspisR1.NFP_QueryTrace.erased, `AspisR1.NFP_LoopTransport.complete])
    else if mode == "proof3" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFS_AccumDomain.line, `AspisR1.NFS_AccumDomain.domain, `AspisR1.NFS_AccumInstall.installed, `AspisR1.NFS_QueryOps.line])
    else if mode == "proof4" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFS_QueryOps.accumulation, `AspisR1.NFS_QueryBack.installed, `AspisR1.NFS_FoldInstall.rows, `AspisR1.NFS_FoldInstall.map_map])
    else if mode == "proof5" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFS_FoldInstall.line, `AspisR1.NFS_FoldInstall.circle, `AspisR1.NFS_FoldInstall.domains, `AspisR1.NFS_TraceBack.eval_bind])
    else if mode == "proof6" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFS_TraceBack.model_congr, `AspisR1.NFS_TraceBack.source, `AspisR1.NFS_TraceBack.installed, `AspisR1.NFS_DotTrace.head])
    else if mode == "proof7" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFS_QueryValuesPacket.source, `AspisR1.NFS_QueryValuesPacket.result, `AspisR1.NFS_ReadCanonical.limbs, `AspisR1.NFS_ReadCanonical.bytes])
    else if mode == "proof8" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFS_ReadCanonical.field, `AspisR1.NFS_ReadCanonical.read_canonical, `AspisR1.NFS_QueryInvariant.form, `AspisR1.NFS_QueryInvariant.active])
    else if mode == "proof9" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFS_QueryInvariant.step, `AspisR1.NFS_CallerDomains.no_seed, `AspisR1.NFS_CallerDomains.loop_property, `AspisR1.NFS_CallerDomains.array_property])
    else if mode == "proof10" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFS_CallerDomains.fields, `AspisR1.NFS_CallerDomains.dots, `AspisR1.NFS_CallerDomains.folds, `AspisR1.NFS_QueryLoopRoot.finite])
    else if mode == "proof11" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFS_QueryLoopRoot.root, `AspisR1.NFS_QueryLoopRoot.tx1, `AspisR1.NFS_QueryLoopRoot.tx2, `AspisR1.NFS_LoopTraceDefs.bind_congr])
    else if mode == "proof12" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFS_LoopTraceDefs.compare, `AspisR1.NFS_LoopTraceDefs.erased, `AspisR1.NFS_LoopTrace.erase_fixed, `AspisR1.NFS_LoopTrace.source])
    else if mode == "proof13" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFS_PacketRoot.geometry, `AspisR1.NFS_PacketRoot.node, `AspisR1.NFS_PacketRoot.query, `AspisR1.NFS_PacketRoot.loop])
    else if mode == "proof14" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFP_Advance.accepted, `AspisR1.NFP_Carrier.from_to, `AspisR1.NFP_Carrier.to_from, `AspisR1.NFP_Carrier.words])
    else if mode == "proof15" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFP_Carrier.canonical, `AspisR1.NFP_DotCaller.tail, `AspisR1.NFP_DotCaller.query, `AspisR1.NFP_DotDomains.returned])
    else if mode == "proof16" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFP_DotInstall.dot_result, `AspisR1.NFP_DotInstall.head, `AspisR1.NFP_FrameExt.raw, `AspisR1.NFP_GeometryDomains.reads])
    else if mode == "proof17" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFP_HeadDomain.reached, `AspisR1.NFP_LoopBudget.tx1, `AspisR1.NFP_LoopBudget.tx2, `AspisR1.NFP_LoopBudget.maximum])
    else if mode == "proof18" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFP_LoopTerminals.error, `AspisR1.NFP_LoopTerminals.stopped, `AspisR1.NFP_LoopTerminals.rejected, `AspisR1.NFP_LoopTerminals.failed])
    else if mode == "proof19" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFP_LoopTerminals.diverged, `AspisR1.NFP_LoopTransport.child, `AspisR1.NFP_NatBase.sub_word, `AspisR1.NFP_NatBase.add])
    else if mode == "proof20" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFP_NatBase.sub, `AspisR1.NFP_NodeDictionary.product, `AspisR1.NFP_NodeDictionary.add, `AspisR1.NFP_NodeDictionary.sub])
    else if mode == "proof21" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFP_NodeDictionary.node, `AspisR1.NFP_ObserverErasure.query, `AspisR1.NFP_ObserverErasure.phase, `AspisR1.NFP_ObserverErasure.trace])
    else if mode == "proof22" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFP_ProductLaw.emitted, `AspisR1.NFP_ProductLaw.node, `AspisR1.NFP_QueryAdvance.accepted, `AspisR1.NFP_QueryAdvance.offset])
    else if mode == "proof23" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFP_QueryCuts.source, `AspisR1.NFP_RejectionTrace.guard, `AspisR1.NFP_RejectionTrace.rejected_prefix, `AspisR1.NFP_Resume.tx1])
    else if mode == "proof24" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFP_Resume.tx2, `AspisR1.NFP_ReturnCuts.erased, `AspisR1.NFP_ReturnCuts.continuation, `AspisR1.NFP_SuffixCuts.source])
    else if mode == "proof25" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFP_TraceBack.erased, `AspisR1.NFP_TraceFront.erased, `AspisR1.NFP_TraceHead.erased, `AspisR1.NFP_TraceTypes.pure_result])
    else if mode == "proof26" then
      (#[`NFS_COMBINED_IMPORT], #[`AspisR1.NFM_Cuts.abort_prefix, `AspisR1.NFG_PushRoot.private_result, `AspisR1.NFG_PushRoot.public_result])
    else if mode == "fixtures" then
      (#[`NEP_Planted, `NEP_Mutations],
       #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
         `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
         `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
    else (#[], #[])
  let env ← importModules (modules.map fun n => ({module := n, importAll := true} : Import))
    {} (loadExts := true) (level := .private)
  if mode == "scan" || mode == "queryscan" then
    let mut expected : Std.HashMap String (Array String) := {}
    for line in ← IO.FS.lines (if mode == "queryscan" then "NFN_QUERY_EXPECTED_IMPORTS.jsonl" else "NFN_EXPECTED_IMPORTS.jsonl") do
      let j ← IO.ofExcept (Json.parse line)
      expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
        (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
    let failed ← NER.loadedScan env (if mode == "queryscan" then "NFN_QUERY_LOADED_scan.jsonl" else "NFN_LOADED_scan.jsonl") expected
    IO.println (if failed then "NFN_SCAN_FAILED" else "NFN_SCAN_ZERO_DANGLING")
    return if failed then 1 else 0
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
        NEP.audit root ("NEP_" ++ mode ++ "_" ++ root.toString)
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
