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
      (#[`NKE_COMBINED_IMPORT], #[`NKE_ActualCuts.geometry, `NKE_ActualCuts.geometry_post, `NKE_BorrowPrefix.geometry, `NKE_BorrowPrefix.same, `NKE_BorrowPrefix.at_actual, `NKE_CommonAssociation.source, `NKE_CommonAssociation.prefixes, `NKE_CommonCalls.source, `NKE_CommonCalls.Clause, `NKE_CommonClauses.pending, `NKE_CommonClauses.flush, `NKE_CommonClauses.query])
    else if mode == "proof1" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_CommonCodec.resume, `NKE_CommonCodec.powers, `NKE_CommonCodec.inactive, `NKE_CommonCodec.merkle, `NKE_CommonCodec.geometry, `NKE_CommonCodec.pending, `NKE_CommonCodec.query, `NKE_CommonCodec.flush, `NKE_CommonCodec.finish, `NKE_CommonDomain.source, `NKE_CommonEval.source, `NKE_CommonNative.event_exact])
    else if mode == "proof2" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_CommonNative.fold, `NKE_CommonNative.actual, `NKE_CommonSource.clauses, `NKE_EAtSource.total, `NKE_EAtSource.bounded, `NKE_Entered.bind_all, `NKE_Entered.lift_ok, `NKE_EventAll.bind_all, `NKE_EventAll.lift_all, `NKE_EventAll.pure_all, `NKE_EventAll.record_all, `NKE_FinishSupplement.finish])
    else if mode == "proof3" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_FinishSupplement.ported, `NKE_FinishSupplement.at_current, `NKE_FlushNative.step, `NKE_FlushNative.source, `NKE_Free.eval_bind, `NKE_Free.eval_record, `NKE_Free.eval_liftM, `NKE_Free.eval_pure, `NKE_Free.eval_if, `NKE_Free.eval_flow, `NKE_FreeReplay.seed_unused, `NKE_FreeReplay.source])
    else if mode == "proof4" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_FreeReplay.prefixes, `NKE_GeometryCuts.same, `NKE_GeometryCuts.at_call, `NKE_GeometryDomain.returned, `NKE_KAtSource.total, `NKE_KAtSource.bounded, `NKE_LogPrefix.append, `NKE_LogPrefix.prefixes, `NKE_LogPrefix.abort, `NKE_LogPrefix.diverge, `NKE_PendingAtSource.source, `NKE_PendingAtSource.native_rows])
    else if mode == "proof5" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_PendingNative.cut, `NKE_PendingNative.source, `NKE_QueryInput.same, `NKE_QueryInput.child_at_same_arguments, `NKE_QueryReturn.cut, `NKE_QueryReturn.complete, `NKE_QueryReturn.observed_exact, `NKE_RawAtSource.source, `NKE_ResumeAssociation.source, `NKE_ResumeAssociation.prefixes, `NKE_ResumeAssociation.at_common, `NKE_ResumeAtCommon.source])
    else if mode == "proof6" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_ResumeClauses.finishTailG, `NKE_ResumeClauses.queryEndG, `NKE_ResumeClauses.queryMidG, `NKE_ResumeClauses.queryBlockG, `NKE_ResumeClauses.resumeBodyG, `NKE_ResumeClauses.run, `NKE_ResumeCodec.digest, `NKE_ResumeCodec.headerAny, `NKE_ResumeCodec.k, `NKE_ResumeCodec.e, `NKE_ResumeCodec.semantic, `NKE_ResumeCodec.weights])
    else if mode == "proof7" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_ResumeCodec.validate, `NKE_ResumeCodec.filled, `NKE_ResumeCodec.raw, `NKE_ResumeDomain.action_ok, `NKE_ResumeDomain.returned, `NKE_ResumeEval.finishTailG, `NKE_ResumeEval.queryEndG, `NKE_ResumeEval.queryMidG, `NKE_ResumeEval.queryBlockG, `NKE_ResumeEval.resumeBodyG, `NKE_ResumeEval.run, `NKE_ResumeWidth.checkpoint])
    else if mode == "proof8" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_ResumeWidth.returned, `AspisR1.RPx_Deployed.deployed, `NKE_RunExt.bind, `NKE_RustBind.lower, `NKE_Stores.length, `NKE_Stores.step, `NKE_Stores.complete, `NKE_ViewCut.ext, `NKE_ViewCut.same, `NKE_ViewWindows.final_cells, `NKE_ViewWindows.slice_cells, `AspisR1.NJU_GeneralFinishRoot.finish])
    else if mode == "proof9" then
      (#[`NKE_COMBINED_IMPORT], #[`AspisR1.NJU_GeneralFinishRoot.ported, `NJU_FinishAtCurrent.source_view])
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
