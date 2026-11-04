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
    if mode == "stage2proof0" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_AdapterGetters.key, `NFU_AdapterGetters.owner, `NFU_AdapterGetters.readonly, `NFU_AdapterGetters.readonly_frame, `NFU_AdapterGetters.key_frame, `NFU_AdapterGetters.owner_frame, `NFU_CompactLeaves.validate_result, `NFU_CompactLeaves.check_result])
    else if mode == "stage2proof1" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_CompactLeaves.expand_result, `NFU_CompactLeaves.expand_reject, `NFU_Retarget.LPl_A.Check.loop_eq_model, `NFU_Retarget.LPl_A.Check.shipped_leaf_model, `NFU_Retarget.LPl_A.Check.loop_eq_fold, `NFU_Retarget.LPl_A.Check.accepts_iff, `NFU_Retarget.LPl_A.Check.rejects_of_bad_stage, `NFU_Retarget.LPl_A.Echeck.loop_eq_model])
    else if mode == "stage2proof2" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPl_A.Echeck.shipped_leaf_model, `NFU_Retarget.LPl_A.Echeck.loop_eq_fold, `NFU_Retarget.LPl_A.Echeck.accepts_iff, `NFU_Retarget.LPl_A.Echeck.rejects_of_bad_stage, `NFU_Retarget.LPl_A.Expand.loop_eq_map, `NFU_Retarget.LPl_A.Expand.loop_eq_fold, `NFU_Retarget.LPl_A.Expand.shipped_leaf_model, `NFU_Retarget.LPl_A.Expand.loop_length])
    else if mode == "stage2proof3" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPl_A.Expand.low_half, `NFU_Retarget.LPl_A.Expand.high_half, `NFU_Retarget.LPl_A.Expand.y1_loop_fold, `NFU_Retarget.LPl_A.firstBad_find, `NFU_Retarget.LPl_A.firstBad_fold, `NFU_Retarget.LPl_A.stages_fold, `NFU_Retarget.LPl_A.stages_all, `NFU_Retarget.LPl_A.stages_append])
    else if mode == "stage2proof4" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPl_A.build_map, `NFU_Retarget.LPl_A.build_fold, `NFU_Retarget.LPl_A.check_stage_congruence, `NFU_Retarget.LPl_A.echeck_stage_congruence, `NFU_Retarget.LPl_A.stages_congr, `NFU_Retarget.LPl_A.firstBad_bound, `NFU_Retarget.LPl_A.firstBad_none, `NFU_Retarget.LPl_A.firstBad_is_bad])
    else if mode == "stage2proof5" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPl_A.build_length, `NFU_Retarget.LPl_A.Validate.loop_eq_model, `NFU_Retarget.LPl_A.Validate.loop_eq_fold, `NFU_Retarget.LPl_A.Validate.shipped_leaf_model, `NFU_Retarget.LPl_A.Validate.error_index_bound, `NFU_Retarget.LPl_A.Validate.error_exact, `NFU_Retarget.LPl_A.Validate.accepts_of_all_stages, `NFU_Retarget.LPl_C.Echeck.caller_iff])
    else if mode == "stage2proof6" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPl_C.Echeck.tail_class, `NFU_Retarget.LPl_C.Echeck.count_with_tail, `NFU_Retarget.LPl_C.Check.caller_iff, `NFU_Retarget.LPl_C.Check.caller_reject, `NFU_Retarget.LPl_C.Validate.caller_success, `NFU_Retarget.LPl_C.Validate.caller_error_bound, `NFU_Retarget.LPl_C.window_append, `NFU_Retarget.LPl_C.Expand.row_low])
    else if mode == "stage2proof7" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPl_C.Expand.row_high, `NFU_Retarget.LPl_C.Expand.caller_rows, `NFU_Retarget.LPl_C.fold_simulation, `NFU_Retarget.LPl_C.Echeck.append_tail, `NFU_Retarget.LPl.Check.chunk_eq, `NFU_Retarget.LPl.Check.window, `NFU_Retarget.LPl.Check.stage, `NFU_Retarget.LPl.Check.native_result])
    else if mode == "stage2proof8" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPl.Check.unique, `NFU_Retarget.LPl.Check.total, `NFU_Retarget.LPl.Check.zero_chunk, `NFU_Retarget.LPl.Check.rejected_chunk, `NFU_Retarget.LPl.Echeck.word_eq_le32, `NFU_Retarget.LPl.Echeck.chunk_eq, `NFU_Retarget.LPl.Echeck.window, `NFU_Retarget.LPl.Echeck.run_all])
    else if mode == "stage2proof9" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPl.Echeck.run_loop, `NFU_Retarget.LPl.Echeck.native_result, `NFU_Retarget.LPl.Echeck.unique, `NFU_Retarget.LPl.Echeck.exists_trace, `NFU_Retarget.LPl.Echeck.read_eq, `NFU_Retarget.LPl.Echeck.read_size, `NFU_Retarget.LPl.Echeck.advance, `NFU_Retarget.LPl.Echeck.trace_result])
    else if mode == "stage2proof10" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPl.Expand.inside, `NFU_Retarget.LPl.Expand.outside, `NFU_Retarget.LPl.Expand.length, `NFU_Retarget.LPl.Expand.invariant, `NFU_Retarget.LPl.Expand.update_write, `NFU_Retarget.LPl.Expand.total, `NFU_Retarget.LPl.Expand.output, `NFU_Retarget.LPl.Expand.unique])
    else if mode == "stage2proof11" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPl.Expand.double, `NFU_Retarget.LPl.Expand.native_result, `NFU_Retarget.LPl.Expand.length_error, `NFU_Retarget.LPl_G.window_contained, `NFU_Retarget.LPl_G.scan928, `NFU_Retarget.LPl_G.record3712, `NFU_Retarget.LPl_G.claims_window, `NFU_Retarget.LPl_G.echeck_stages])
    else if mode == "stage2proof12" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPl_G.check_stages, `NFU_Retarget.LPl_G.first_error_sticky, `NFU_Retarget.LPl_G.validation_error, `NFU_Retarget.LPl.Scan.result, `NFU_Retarget.LPl.Scan.run_find, `NFU_Retarget.LPl.Scan.first_error, `NFU_Retarget.LPl.Scan.unique, `NFU_Retarget.LPl.Scan.exists_trace])
    else if mode == "stage2proof13" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPl.Scan.window_eq, `NFU_Retarget.LPl.Scan.bool_none, `NFU_Retarget.LPl.Validate.bad_eq, `NFU_Retarget.LPl.Validate.window, `NFU_Retarget.LPl.Validate.first_error, `NFU_Retarget.LPl.Validate.native_result, `NFU_Retarget.LPl.Validate.error_bound, `NFU_Retarget.LPl.Validate.earlier_error])
    else if mode == "stage2proof14" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPl.Validate.unique, `NFU_Retarget.LPl.Validate.total, `NFU_Retarget.LPn.Expand.coordinate_bound, `NFU_Retarget.LPn.Expand.local_global, `NFU_Retarget.LPn.Expand.write_of_observations, `NFU_Retarget.LPn.Expand.windows_disjoint, `NFU_Retarget.LPn.Expand.iterator_partition, `NFU_Retarget.LPn.Expand.to_inherited])
    else if mode == "stage2proof15" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_Retarget.LPn.Expand.of_inherited, `NFU_Retarget.LPn.Expand.total, `NFU_Retarget.LPn.Expand.native_result, `NFU_Retarget.LPn.Expand.unique, `NFU_Retarget.LPn.Expand.length_error, `NFU_PacketDomains.payload_bound, `NFU_PacketDomains.framed_bound, `NFU_PacketDomains.compact_payload_bound])
    else if mode == "stage2proof16" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_PacketDomains.payload_aligned, `NFU_PacketDomains.low_window, `NFU_PacketDomains.expansion_window, `NFU_PacketDomains.expansion_disjoint, `NFU_PacketDomains.checkpoint_s2, `NFU_PrefixRecords.record, `NFU_PrefixRecords.validated_record, `NFU_RecordGetters.row])
    else if mode == "stage2proof17" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_RecordGetters.framed, `NFU_RecordGetters.parser_row, `NFU_RecordGetters.parser_framed, `NFU_RecordGetters.same_token, `NFU_RowDomains.shape, `NFU_RowDomains.parser_shape, `NFU_RowDomains.framed, `NFU_TransportTag.model])
    else if mode == "stage2proof18" then
      (#[`NFU_STAGE2_IMPORT], #[`NFU_TransportTag.canonical_range, `NFU_TransportTag.deployed_s2, `NFU_ZeroPort.head, `NFU_ZeroPort.length, `NFU_ZeroPort.advance, `NFU_ZeroPort.index_advance, `NFU_ZeroPort.source])
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
    for line in ← IO.FS.lines (if mode == "queryscan" then "NFU_QUERY_EXPECTED_IMPORTS.jsonl" else "NFU_EXPECTED_IMPORTS.jsonl") do
      let j ← IO.ofExcept (Json.parse line)
      expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
        (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
    let failed ← NER.loadedScan env (if mode == "queryscan" then "NFU_QUERY_LOADED_scan.jsonl" else "NFU_LOADED_scan.jsonl") expected
    IO.println (if failed then "NFU_SCAN_FAILED" else "NFU_SCAN_ZERO_DANGLING")
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
