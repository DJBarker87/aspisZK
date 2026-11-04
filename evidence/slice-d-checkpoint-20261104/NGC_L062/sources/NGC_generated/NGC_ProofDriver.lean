import Lean
import NGC_WALKER
import NGC_MemoryLimit
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
    if mode == "fixtures" then
      (#[`NEP_Planted,`NEP_Mutations],#[`NEP_Planted.matcher,`NEP_Planted.viaPrivate,`NEP_Planted.proof,`NEP_Planted.viaAux,`NEP_MutateMatch.matcher,`NEP_MutatePrivate.viaPrivate,`NEP_MutateProof.proof,`NEP_MutateAux.viaAux])
    else if mode == "proof0" then
      (#[`NGC_COMBINED_IMPORT],#[`NGC_ByteWriters.cm,`NGC_ByteWriters.qm,`AspisR1.NGC_Initialization.heap_result,`AspisR1.NGC_Initialization.constructor,`AspisR1.NGC_Initialization.accepted,`AspisR1.NGC_Initialization.rejection,`AspisR1.RPx_Deployed.deployed,`AspisR1.NGC_FinishFrame.result_frame,`AspisR1.NGC_DigestBridge.observed,`AspisR1.NGC_DigestBridge.forwarding])
    else if mode == "proof1" then
      (#[`NGC_COMBINED_IMPORT],#[`AspisR1.NGC_DigestBridge.checkpoint_oracle,`AspisR1.NGC_KNE_Caller.every_reached_call,`AspisR1.NGC_PreparationBoundary.canonicalK,`AspisR1.NGC_PreparationBoundary.canonicalE,`AspisR1.NGC_QueryPoststate.finite,`AspisR1.NGC_QueryPoststate.tx1,`AspisR1.NGC_WriterDomain.after_finish,`AspisR1.NGC_WriterDomain.from_query_loop,`AspisR1.NGC_LPi_SerializationFold.contents,`AspisR1.NGC_LPi_SerializationFold.byte_length])
    else if mode == "proof2" then
      (#[`NGC_COMBINED_IMPORT],#[`AspisR1.NGC_LPi_SerializationFold.length,`AspisR1.NGC_LPi_SerializationFold.weights64,`AspisR1.NGC_LPm_WeightLoop.result,`AspisR1.NGC_LPm_WeightLoop.exists_trace,`AspisR1.NGC_LPm_WeightLoop.native_weights,`AspisR1.NGC_LPm_WeightLoop.reached_size,`AspisR1.NGC_LPm_WeightLoop.reached_domain,`AspisR1.NGC_LPm_CheckpointBody.source_body,`AspisR1.NGC_LPm_CheckpointBody.weights_port,`AspisR1.NGC_LPm_CheckpointProgram.materialize_eq])
    else if mode == "proof3" then
      (#[`NGC_COMBINED_IMPORT],#[`AspisR1.NGC_LPm_CheckpointProgram.returned_eq,`AspisR1.NGC_LPm_CheckpointProgram.program_eq,`AspisR1.NGC_LPm_CheckpointProgram.result_and_effects,`NGC_KND_Schedule.data_independent,`NGC_KND_Schedule.exact_schedule,`NGC_KND_Schedule.append_count,`NGC_KND_Schedule.final_length,`NGC_KND_Schedule.no_growth,`NGC_KND_Schedule.body_length,`AspisR1.NGC_KNE_Model.indexed_payload])
    else if mode == "proof4" then
      (#[`NGC_COMBINED_IMPORT],#[`AspisR1.NGC_KNE_Model.indexed_shape,`AspisR1.NGC_KNE_Model.flatten_ofFn,`AspisR1.NGC_KNE_Model.rawK_length,`AspisR1.NGC_KNE_Model.bodyEmissions_payload,`AspisR1.NGC_KNE_Model.bodyEmissions_shape,`AspisR1.NGC_KNE_Schedule.writer_shape,`AspisR1.NGC_KNE_Schedule.caller_final_len,`AspisR1.NGC_KNE_Schedule.derived_schedule,`AspisR1.NGC_KNE_Schedule.native_body_decomposition,`AspisR1.NGC_KNE_Schedule.returned_decomposition])
    else if mode == "proof5" then
      (#[`NGC_COMBINED_IMPORT],#[`AspisR1.NGC_KNE_Composition.compose,`AspisR1.NGC_KNE_Composition.annotate_left,`AspisR1.NGC_KNE_Composition.body_entries,`AspisR1.NGC_KNE_Composition.body_bytes,`AspisR1.NGC_KNE_Writer.emission_count,`AspisR1.NGC_KNE_Writer.appendAll_eq,`AspisR1.NGC_KNE_Writer.bodyList_eq,`AspisR1.NGC_KNE_Writer.materialize_eq,`AspisR1.NGC_KNE_Writer.returnList_eq,`AspisR1.NGC_KNE_Writer.returned_eq])
    else if mode == "proof6" then
      (#[`NGC_COMBINED_IMPORT],#[`AspisR1.NGC_KNE_Writer.program_eq,`AspisR1.NGC_KNE_Writer.cohort_program_eq,`AspisR1.NGC_KNE_Leaf.native_result,`AspisR1.NGC_KNE_Final.schedule_facts,`AspisR1.NGC_ValueBridge.value,`AspisR1.NGC_CheckpointBridge.derived_packet,`AspisR1.NGC_AppendFrame.bytes,`AspisR1.NGC_AppendFrame.prefix_frame,`AspisR1.NGC_AppendFrame.byte_domain,`AspisR1.NGC_AppendFrame.local_correct])
    else if mode == "proof7" then
      (#[`NGC_COMBINED_IMPORT],#[`AspisR1.NGC_NFW_QueryEntry.progress,`AspisR1.NGC_NFW_QueryEntry.power,`AspisR1.NGC_NFW_QueryEntry.rhs,`AspisR1.NGC_NFW_QueryEntry.weights_canonical,`AspisR1.NGC_NFW_QueryEntry.domain,`AspisR1.NGC_FinishContents.contents,`AspisR1.NGC_InitialInvariant.initial,`AspisR1.NGC_FillInduction.result,`AspisR1.NGC_FillInduction.empty,`AspisR1.NGC_FillInduction.length])
    else if mode == "proof8" then
      (#[`NGC_COMBINED_IMPORT],#[`AspisR1.NGC_FillInduction.spare_capacity,`AspisR1.NGC_ReferenceValues.resize_empty,`AspisR1.NGC_ReferenceValues.roundtrip,`AspisR1.NGC_ReferenceValues.heap,`AspisR1.NGC_ReferenceValues.finish_step])
    else
      (#[`NGC_COMBINED_IMPORT],#[])
  let env ← importModules (modules.map fun n => ({module := n, importAll := true} : Import))
    {} (loadExts := true) (level := .private)
  if mode == "scan" || mode == "queryscan" then
    let mut expected : Std.HashMap String (Array String) := {}
    for line in ← IO.FS.lines (if mode == "queryscan" then "NGC_QUERY_EXPECTED_IMPORTS.jsonl" else "NGC_EXPECTED_IMPORTS.jsonl") do
      let j ← IO.ofExcept (Json.parse line)
      expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
        (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
    let failed ← NER.loadedScan env (if mode == "queryscan" then "NGC_QUERY_LOADED_scan.jsonl" else "NGC_LOADED_scan.jsonl") expected
    IO.println (if failed then "NGC_SCAN_FAILED" else "NGC_SCAN_ZERO_DANGLING")
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
