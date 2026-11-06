import Lean
import NFA_WALKER
import NFA_MemoryLimit
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  NFA_MemoryLimit.set
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) := if mode == "fixtures" then
    (#[`NEP_Planted, `NEP_Mutations],
     #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
       `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
       `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
    else if mode == "proof0" then
      (#[`NLE_COMBINED_IMPORT], #[`NLE_Auth.parse_result, `NLE_Auth.parse_frame, `NLE_Auth.parse_reject, `NLE_Auth.mark_result, `NLE_Auth.mark_events, `NLE_Auth.common_result, `NLE_Auth.mark_abort, `NLE_Auth.fold_source])
    else if mode == "proof1" then
      (#[`NLE_COMBINED_IMPORT], #[`NLE_Auth.parameterized_fold, `NLE_Length.proof_extent, `NLE_Length.validated_length, `NLE_Length.public_extent, `NLE_Length.public_scope, `NLE_SnapshotClause.proof_bytes, `NLE_SnapshotClause.proof_scope, `NLE_RangeClause.caller_proof])
    else if mode == "proof2" then
      (#[`NLE_COMBINED_IMPORT], #[`NLE_ParseInstall.success, `NLE_ParseInstall.emitted, `NLE_AuthScope.mark_stub_domain, `NLE_AuthScope.entered, `NLE_AuthScope.common_domain, `NLE_AuthLiteral.installed, `NLE_Owned.errorMap_result, `NLE_Owned.source])
    else if mode == "proof3" then
      (#[`NLE_COMBINED_IMPORT], #[`NLE_OwnedStep.validate_result, `NLE_OwnedStep.validate_events, `NLE_OwnedStep.proof_result, `NLE_OwnedStep.proof_events, `NLE_OwnedStep.checkpoint_result, `NLE_OwnedStep.checkpoint_events, `NLE_OwnedStep.encode_result, `NLE_OwnedStep.encode_events])
    else if mode == "proof4" then
      (#[`NLE_COMBINED_IMPORT], #[`NLE_OwnedStep.emit_result, `NLE_OwnedStep.emit_events, `NLE_OwnedStep.tx2_result, `NLE_OwnedStep.release_observer, `NLE_OwnedFine.installed, `NLE_OwnedFine.source, `NLE_MapError.success, `NLE_MapError.rejection])
    else if mode == "proof5" then
      (#[`NLE_COMBINED_IMPORT], #[`NLE_MapError.abort, `NLE_MapError.diverge, `NLE_ErrorPrefix.abort, `NLE_ErrorPrefix.diverge, `NLE_ErrorPrefix.rejected, `NLE_Wrapper.fold_source, `NLE_Wrapper.snapshot_frame, `NLE_Wrapper.snapshot_result])
    else if mode == "proof6" then
      (#[`NLE_COMBINED_IMPORT], #[`NLE_Wrapper.clear_result, `NLE_Dispatch.source, `NLE_Dispatch.emitted, `NLE_Entry.source, `NLE_Entry.emitted, `NLE_Entry.rejected, `NLE_RouteFold.asq8_route, `NLE_RouteFold.entry])
    else if mode == "proof7" then
      (#[`NLE_COMBINED_IMPORT], #[`NLE_RouteFold.child_packet, `NLE_NativeTags.error_roundtrip, `NLE_NativeTags.parse_roundtrip, `NLE_NativeTags.common_roundtrip, `NLE_NativeTags.parse_domain, `NLE_NativeTags.common_domain, `NLE_SafeCuts.parse_continuation, `NLE_SafeCuts.parse_error])
    else if mode == "proof8" then
      (#[`NLE_COMBINED_IMPORT], #[`NLE_SafeCuts.common_reply, `NLE_CallerScope.checkpoint, `NLE_CallerScope.scope, `AspisR1.RPx_Deployed.deployed, `NKU_ParentFold.source, `NKU_ParentFold.cohort, `NKU_ParentFold.clauses])
    else (#[], #[])
  let env ← importModules (modules.map fun n => ({module := n, importAll := true} : Import))
    {} (loadExts := true) (level := .private)
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
