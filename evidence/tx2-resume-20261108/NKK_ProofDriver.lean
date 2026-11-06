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
      (#[`NKK_COMBINED_IMPORT], #[`NKK_AllocationBind.rejected, `NKK_AllocationStage.events, `NKK_AllocationStage.rejected, `NKK_AllocationStage.width, `NKK_ClauseRoot.source, `NKK_ClauseRoot.cohort, `NKK_Clauses.raw, `NKK_Clauses.k, `NKK_Clauses.e, `NKK_Clauses.semantic])
    else if mode == "proof1" then
      (#[`NKK_COMBINED_IMPORT], #[`NKK_Clauses.weights, `NKK_Clauses.validate, `NKK_Clauses.filled, `NKK_Clauses.headerAny, `NKK_Clauses.digest, `NKK_ResumeClauses.finishTail, `NKK_ResumeClauses.queryBlock, `NKK_ResumeClauses.queryEnd, `NKK_ResumeClauses.queryMid, `NKK_ResumeClauses.resumeBody])
    else if mode == "proof2" then
      (#[`NKK_COMBINED_IMPORT], #[`NKK_ResumeClauses.run, `NKK_Compare.list_result, `NKK_Compare.eq_result, `NKK_Compare.ne_result, `NKK_Compare.branch, `NKK_DecoderDomain.e, `NKK_DecoderDomain.k, `NKK_DigestChain.source_eq_model, `NKK_DigestCut.same_call, `NKK_DigestCut.byte_frame])
    else if mode == "proof3" then
      (#[`NKK_COMBINED_IMPORT], #[`NKK_DigestSource.source_eq_model, `NKK_EmbedRaw.result, `NKK_EmbedRaw.pure, `NKK_EmbedRaw.bind, `NKK_EmbedRaw.record, `NKK_EmbedRaw.raw, `NKK_FieldFold.association, `NKK_FieldCps.map_cont, `NKK_FieldCps.source, `NKK_FieldDomain.bounded])
    else if mode == "proof4" then
      (#[`NKK_COMBINED_IMPORT], #[`NKK_FieldDomain.inside, `NKK_FieldFold.error_prefix, `NKK_FieldFold.abort_prefix, `NKK_FieldFold.div_prefix, `NKK_FieldLiteral.call_k, `NKK_FieldLiteral.call_e, `NKK_FieldLiteral.source, `NKK_FieldShape.call_tag, `NKK_FieldShape.shape, `NKK_FieldSites.gamma])
    else if mode == "proof5" then
      (#[`NKK_COMBINED_IMPORT], #[`NKK_FieldSites.z, `NKK_FieldSites.gamma_fold, `NKK_FieldSites.z_fold, `NKK_FieldStages.gamma_source, `NKK_HeaderFactor.source, `NKK_Invoke.bind, `NKK_Invoke.abort, `NKK_Invoke.diverges, `NKK_LogAlgebra.bind_congr, `NKK_LogAlgebra.bind_assoc])
    else if mode == "proof6" then
      (#[`NKK_COMBINED_IMPORT], #[`NKK_LogClauses.pure, `NKK_LogClauses.lift, `NKK_LogClauses.liftM, `NKK_LogClauses.record, `NKK_LogClauses.bind, `NKK_LogClauses.branch, `NKK_LogClauses.flow, `NKK_LogReduce.pure_bind, `NKK_LogReduce.lift_ok_bind, `NKK_LogReduce.liftM_ok_bind])
    else if mode == "proof7" then
      (#[`NKK_COMBINED_IMPORT], #[`NKK_NativeRaw.backing, `NKK_NativeRaw.advance, `NKK_NativeRaw.one, `NKK_QueryBlockJoin.source, `NKK_QueryDomain.eight, `NKK_QueryDomain.six, `NKK_QueryEndJoin.source, `NKK_QueryMidJoin.source, `NKK_QueryStage.stage8, `NKK_QueryStage.stage6])
    else if mode == "proof8" then
      (#[`NKK_COMBINED_IMPORT], #[`NKK_QueryWindows.domain, `NKK_RawFold.association, `NKK_NativeRaw.read_chain, `NKK_NativeRaw.read_result, `NKK_RawCps.source, `NKK_RawFold.fold_nil, `NKK_RawFold.fold_cons, `NKK_RawFold.fail_stays, `NKK_RawFold.div_stays, `NKK_RawFold.length])
    else if mode == "proof9" then
      (#[`NKK_COMBINED_IMPORT], #[`NKK_RawPrefix.source, `NKK_RawPrefix.associated, `NKK_RawResult.source, `NKK_RawSlots.query8, `NKK_RawSlots.query6, `NKK_RawSlots.roots, `NKK_RawFold.clauses, `NKK_RawFold.synchronized, `NKK_ReadFrames.k, `NKK_ReadFrames.e])
    else if mode == "proof10" then
      (#[`NKK_COMBINED_IMPORT], #[`NKK_ResumeBodyFactor.source, `NKK_RunEval.bind_eq, `NKK_RunEval.pure_eq, `NKK_SectionFrames.semantic, `NKK_SectionFrames.weights, `NKK_Try.branch, `NKK_ZStage.source_eq_model, `NJU_ResumeRoot.source, `NJU_ResumeRoot.cohort, `AspisR1.RPx_Deployed.deployed])
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
