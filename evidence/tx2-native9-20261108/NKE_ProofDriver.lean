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
      (#[`NKE_COMBINED_IMPORT], #[`NKE_BadWindow.witness, `NKE_BadWindow.noncanonical, `NKE_BadWindow.read_bounds, `NKE_BadWindow.short, `NKE_CommonObserved.source, `NKE_CurrentWindows.split, `NKE_CurrentWindows.rejects, `NKE_FieldDecode.total, `NKE_FieldDecode.word_value, `NKE_FieldDecode.none_of_bad])
    else if mode == "proof1" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_FieldDecode.slice_none, `NKE_FieldFailure.noncanonical, `NKE_FieldFailure.short, `NKE_FieldFailure.primitive_noncanonical, `NKE_FieldScalar.eq_of_value, `NKE_FieldScalar.checked, `NKE_FieldScalar.abort_none, `NKE_FieldScalar.abort_short, `NKE_FieldScalar.returns, `NKE_FinishAtCurrent.source_view])
    else if mode == "proof2" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_FinishCaller.reached, `NKE_FinishCase.current, `NKE_FinishCore.selected, `NKE_FinishCore.reached, `NKE_FinishCore.source, `NKE_FinishDomain.reached, `AspisR1.NKE_FinishInput.intrinsic, `AspisR1.NKE_FinishInput.of_original, `NKE_FinishInstall.at_call, `NKE_FinishObserved.bind_ext])
    else if mode == "proof3" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_FinishObserved.skeleton, `NKE_FinishObserved.source, `AspisR1.NKE_GeneralFinishRoot.finish, `AspisR1.NKE_GeneralFinishRoot.ported, `NKE_Log.erase_bind, `NKE_Log.erase_pure, `NKE_Log.erase_lift, `NKE_Log.erase_liftM, `NKE_Log.erase_record, `NKE_Log.erase_if])
    else if mode == "proof4" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_Log.erase_flow, `NKE_Log.prod_cases, `NKE_Log.fail_prefix, `NKE_Log.div_prefix, `NKE_ResumeErase.finishTail, `NKE_ResumeErase.queryEnd, `NKE_ResumeErase.queryMid, `NKE_ResumeErase.queryBlock, `NKE_ResumeErase.resumeBody, `NKE_ResumeErase.header])
    else if mode == "proof5" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_ResumeReference.source, `NKE_ResumeRoot.source, `NKE_ResumeRoot.cohort, `NKE_ViewWindows.entered_size, `NKE_ViewWindows.lengths, `NKE_ViewWindows.bad_current, `AspisR1.NKE_WeakAlignAfterPhase.trace, `AspisR1.NKE_WeakAlignAllocatorPhase.trace, `AspisR1.NKE_WeakAlignAllocatorPhase.source, `AspisR1.NKE_WeakAlignPairPhase.certificate])
    else if mode == "proof6" then
      (#[`NKE_COMBINED_IMPORT], #[`AspisR1.NKE_WeakAlignPairPhaseSource.source, `AspisR1.NKE_WeakAlignRegularPhase.trace, `AspisR1.NKE_WeakAlignRegularPhaseSource.source, `AspisR1.NKE_WeakAlignRegularPhaseSource.frames, `AspisR1.NKE_WeakAlignSharedPhase.trace, `AspisR1.NKE_WeakAllocatorChain.interpreted, `AspisR1.NKE_WeakAllocatorChain.complete, `AspisR1.NKE_WeakAllocatorInstantiation.source, `AspisR1.NKE_WeakFinishComposedLog.source, `AspisR1.NKE_WeakFinishObserved.detail_source])
    else if mode == "proof7" then
      (#[`NKE_COMBINED_IMPORT], #[`AspisR1.NKE_WeakFinishObserved.source, `AspisR1.NKE_WeakFinishObserved.source_log, `AspisR1.NKE_WeakFinishPairCertificate.observe_bound, `AspisR1.NKE_WeakFinishPairCertificate.source, `AspisR1.NKE_WeakFinishPort.source, `AspisR1.NKE_WeakPairCaller.alphas, `AspisR1.NKE_WeakPairCaller.new_owner, `AspisR1.NKE_WeakPairCaller.caller, `AspisR1.NKE_WeakPairDomain.of_original, `AspisR1.NKE_WeakPairInstalled.source])
    else if mode == "proof8" then
      (#[`NKE_COMBINED_IMPORT], #[`AspisR1.NKE_WeakPairInstantiation.source, `AspisR1.NKE_WeakPairInstantiation.root, `AspisR1.NKE_WeakRegularChain.after_interpreted, `AspisR1.NKE_WeakRegularChain.after_exists, `AspisR1.NKE_WeakRegularChain.interpreted, `AspisR1.NKE_WeakRegularChain.complete, `AspisR1.NKE_WeakRegularContinuation.source, `AspisR1.NKE_WeakSharedChain.shared_interpreted, `AspisR1.NKE_WeakSharedComplete.complete, `NKE_ResumeObserved.run])
    else if mode == "proof9" then
      (#[`NKE_COMBINED_IMPORT], #[`NKE_ResumeObserved.runRef, `AspisR1.NJF_Root.finish, `AspisR1.RPx_Deployed.deployed])
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
