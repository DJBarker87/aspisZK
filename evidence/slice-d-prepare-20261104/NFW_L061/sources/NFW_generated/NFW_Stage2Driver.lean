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
    if mode == "stage0" then
      (#[`NFW_STAGE2_IMPORT], #[`AspisR1.NFW_Bind.same, `AspisR1.NFW_Transcript.seed, `AspisR1.NFW_Transcript.absorb, `AspisR1.NFW_Transcript.block, `AspisR1.NFW_TranscriptDomain.rows, `AspisR1.NFW_TranscriptDomain.payloads, `AspisR1.NFW_TranscriptDomain.tag, `AspisR1.NFW_PreparedControl.source])
    else if mode == "stage1" then
      (#[`NFW_STAGE2_IMPORT], #[`AspisR1.NFW_PreparedResults.query_error, `AspisR1.NFW_PreparedResults.claim_error, `AspisR1.NFW_PreparedResults.prepare_query_error, `AspisR1.NFW_PreparedResults.success, `AspisR1.NFW_PreparedResults.after_opening, `AspisR1.NFW_PreparedFields.source, `AspisR1.NFW_StoredLayout.exact_offsets, `AspisR1.NFW_StoredLayout.bounds])
    else if mode == "stage2" then
      (#[`NFW_STAGE2_IMPORT], #[`AspisR1.NFW_StoredLayout.logical_split, `AspisR1.NFW_StoredLayout.folded_payload, `AspisR1.NFW_StoredWindows.width, `AspisR1.NFW_StoredWindows.join, `AspisR1.NFW_StoredWindows.selected, `AspisR1.NFW_QueryEntry.progress, `AspisR1.NFW_QueryEntry.power, `AspisR1.NFW_QueryEntry.rhs])
    else if mode == "stage3" then
      (#[`NFW_STAGE2_IMPORT], #[`AspisR1.NFW_QueryEntry.weights_canonical, `AspisR1.NFW_QueryEntry.domain, `AspisR1.NFW_QueryStart.tx1, `AspisR1.NFW_PreparedPort.rho_canonical, `AspisR1.NFW_PreparedPort.fields, `AspisR1.NFW_QueryResume.progress, `AspisR1.NFW_QueryResume.domain, `AspisR1.NFW_QueryResume.tx2])
    else if mode == "stage4" then
      (#[`NFW_STAGE2_IMPORT], #[`AspisR1.NFW_ReferenceEq.control, `AspisR1.NFW_ReferenceEq.row_domain, `AspisR1.NFW_ReferenceEq.scratch, `AspisR1.NFW_ReferenceEq.tx1, `AspisR1.NFW_ReferenceEq.tx2, `AspisR1.NFW_SampledDomains.roundtrip, `AspisR1.NFW_SampledDomains.gamma_canonical, `AspisR1.NFW_SampledDomains.rho])
    else if mode == "stage5" then
      (#[`NFW_STAGE2_IMPORT], #[`AspisR1.NFW_SampledDomains.prepared_gamma, `AspisR1.NFW_SampledDomains.same_gamma, `AspisR1.NFW_SampledDomains.powers, `AspisR1.NFW_FoldedPayload.length, `AspisR1.NFW_FoldedPayload.selected, `AspisR1.NFW_FoldedPayload.rejoin, `AspisR1.NFW_Invert.bind, `AspisR1.NFW_PreparedCalls.calls])
    else if mode == "stage6" then
      (#[`NFW_STAGE2_IMPORT], #[`AspisR1.NFW_ScalarRho.sample, `AspisR1.NFW_ScalarRho.prepared, `AspisR1.NFW_PreparedProducer.cell, `AspisR1.NFW_PreparedProducer.array, `AspisR1.NFW_PreparedProducer.scratch, `AspisR1.NFW_PrepareQuery.domains, `AspisR1.NFW_PrepareQuery.tx1, `AspisR1.NFW_ErrorReferenceEq.wire_injective])
    else if mode == "stage7" then
      (#[`NFW_STAGE2_IMPORT], #[`AspisR1.NFW_ErrorReferenceEq.prefix_error, `AspisR1.NFW_ErrorReferenceEq.semantic, `AspisR1.NFW_ErrorReferenceEq.split, `AspisR1.NFW_ErrorReferenceEq.resume])
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
    for line in ← IO.FS.lines (if mode == "queryscan" then "NFQ_QUERY_EXPECTED_IMPORTS.jsonl" else "NFQ_EXPECTED_IMPORTS.jsonl") do
      let j ← IO.ofExcept (Json.parse line)
      expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
        (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
    let failed ← NER.loadedScan env (if mode == "queryscan" then "NFQ_QUERY_LOADED_scan.jsonl" else "NFQ_LOADED_scan.jsonl") expected
    IO.println (if failed then "NFQ_SCAN_FAILED" else "NFQ_SCAN_ZERO_DANGLING")
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
