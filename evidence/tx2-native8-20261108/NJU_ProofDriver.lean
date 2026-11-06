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
      (#[`NJU_COMBINED_IMPORT], #[`NJU_BadWindow.witness, `NJU_BadWindow.noncanonical, `NJU_BadWindow.read_bounds, `NJU_BadWindow.short, `NJU_CommonObserved.source, `NJU_CurrentWindows.split, `NJU_CurrentWindows.rejects, `NJU_FieldDecode.total, `NJU_FieldDecode.word_value, `NJU_FieldDecode.none_of_bad])
    else if mode == "proof1" then
      (#[`NJU_COMBINED_IMPORT], #[`NJU_FieldDecode.slice_none, `NJU_FieldFailure.noncanonical, `NJU_FieldFailure.short, `NJU_FieldFailure.primitive_noncanonical, `NJU_FieldScalar.eq_of_value, `NJU_FieldScalar.checked, `NJU_FieldScalar.abort_none, `NJU_FieldScalar.abort_short, `NJU_FieldScalar.returns, `NJU_FinishAtCurrent.source_view])
    else if mode == "proof2" then
      (#[`NJU_COMBINED_IMPORT], #[`NJU_FinishCaller.reached, `NJU_FinishCase.current, `NJU_FinishCore.selected, `NJU_FinishCore.reached, `NJU_FinishCore.source, `NJU_FinishDomain.reached, `AspisR1.NJU_FinishInput.intrinsic, `AspisR1.NJU_FinishInput.of_original, `NJU_FinishInstall.at_call, `NJU_FinishObserved.bind_ext])
    else if mode == "proof3" then
      (#[`NJU_COMBINED_IMPORT], #[`NJU_FinishObserved.skeleton, `NJU_FinishObserved.source, `AspisR1.NJU_GeneralFinishRoot.finish, `AspisR1.NJU_GeneralFinishRoot.ported, `NJU_Log.erase_bind, `NJU_Log.erase_pure, `NJU_Log.erase_lift, `NJU_Log.erase_liftM, `NJU_Log.erase_record, `NJU_Log.erase_if])
    else if mode == "proof4" then
      (#[`NJU_COMBINED_IMPORT], #[`NJU_Log.erase_flow, `NJU_Log.prod_cases, `NJU_Log.fail_prefix, `NJU_Log.div_prefix, `NJU_ResumeErase.finishTail, `NJU_ResumeErase.queryEnd, `NJU_ResumeErase.queryMid, `NJU_ResumeErase.queryBlock, `NJU_ResumeErase.resumeBody, `NJU_ResumeErase.header])
    else if mode == "proof5" then
      (#[`NJU_COMBINED_IMPORT], #[`NJU_ResumeReference.source, `NJU_ResumeRoot.source, `NJU_ResumeRoot.cohort, `NJU_ViewWindows.entered_size, `NJU_ViewWindows.lengths, `NJU_ViewWindows.bad_current, `AspisR1.NJU_WeakAlignAfterPhase.trace, `AspisR1.NJU_WeakAlignAllocatorPhase.trace, `AspisR1.NJU_WeakAlignAllocatorPhase.source, `AspisR1.NJU_WeakAlignPairPhase.certificate])
    else if mode == "proof6" then
      (#[`NJU_COMBINED_IMPORT], #[`AspisR1.NJU_WeakAlignPairPhaseSource.source, `AspisR1.NJU_WeakAlignRegularPhase.trace, `AspisR1.NJU_WeakAlignRegularPhaseSource.source, `AspisR1.NJU_WeakAlignRegularPhaseSource.frames, `AspisR1.NJU_WeakAlignSharedPhase.trace, `AspisR1.NJU_WeakAllocatorChain.interpreted, `AspisR1.NJU_WeakAllocatorChain.complete, `AspisR1.NJU_WeakAllocatorInstantiation.source, `AspisR1.NJU_WeakFinishComposedLog.source, `AspisR1.NJU_WeakFinishObserved.detail_source])
    else if mode == "proof7" then
      (#[`NJU_COMBINED_IMPORT], #[`AspisR1.NJU_WeakFinishObserved.source, `AspisR1.NJU_WeakFinishObserved.source_log, `AspisR1.NJU_WeakFinishPairCertificate.observe_bound, `AspisR1.NJU_WeakFinishPairCertificate.source, `AspisR1.NJU_WeakFinishPort.source, `AspisR1.NJU_WeakPairCaller.alphas, `AspisR1.NJU_WeakPairCaller.new_owner, `AspisR1.NJU_WeakPairCaller.caller, `AspisR1.NJU_WeakPairDomain.of_original, `AspisR1.NJU_WeakPairInstalled.source])
    else if mode == "proof8" then
      (#[`NJU_COMBINED_IMPORT], #[`AspisR1.NJU_WeakPairInstantiation.source, `AspisR1.NJU_WeakPairInstantiation.root, `AspisR1.NJU_WeakRegularChain.after_interpreted, `AspisR1.NJU_WeakRegularChain.after_exists, `AspisR1.NJU_WeakRegularChain.interpreted, `AspisR1.NJU_WeakRegularChain.complete, `AspisR1.NJU_WeakRegularContinuation.source, `AspisR1.NJU_WeakSharedChain.shared_interpreted, `AspisR1.NJU_WeakSharedComplete.complete, `NJU_ResumeObserved.run])
    else if mode == "proof9" then
      (#[`NJU_COMBINED_IMPORT], #[`NJU_ResumeObserved.runRef, `AspisR1.NJF_Root.finish, `AspisR1.RPx_Deployed.deployed])
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
