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
      (#[`NLT_COMBINED_IMPORT], #[`NLT_AllocationInstalled.resume, `NLT_AllocationInstalled.pending, `NLT_C04Installed.at_event, `NLT_C04Installed.installed, `NLT_C04NativeInstalled.installed, `NLT_Chronology.prepend, `NLT_Chronology.native, `NLT_Chronology.installed, `NLT_CodecQuestions.resume, `NLT_CodecQuestions.powers, `NLT_CodecQuestions.inactive, `NLT_CodecQuestions.merkle])
    else if mode == "proof1" then
      (#[`NLT_COMBINED_IMPORT], #[`NLT_CodecQuestions.geometry, `NLT_CodecQuestions.pending, `NLT_CodecQuestions.query, `NLT_CodecQuestions.flush, `NLT_CodecQuestions.finish, `NLT_Continuation.source, `NLT_EraseCompatible.erase, `NLT_FinishInstalled.installed, `NLT_FrameFromCuts.resume_rank, `NLT_FrameFromCuts.pending_rank, `NLT_FrameFromCuts.finish_rank, `NLT_FrameFromCuts.compatible])
    else if mode == "proof2" then
      (#[`NLT_COMBINED_IMPORT], #[`NLT_Interpreted.step, `NLT_Continuation.no_invalid, `NLT_InvalidTransport.ordered, `NLT_InvalidTransport.reseed, `NLT_InvalidTransport.erase, `NLT_NativeFacts.member, `NLT_NativeFacts.resume_scope, `NLT_NativeInvocation.erase, `NLT_NativeOrder.rank_call, `NLT_NativeOrder.ordered, `NLT_NativeSource.source, `NLT_NativeWindows.interpreted])
    else if mode == "proof3" then
      (#[`NLT_COMBINED_IMPORT], #[`NLT_NativeWindows.rank_question, `NLT_NativeWindows.rank_window, `NLT_NoInvalid.source, `NLT_ParentInvocation.source, `NLT_QueryInstalled.installed, `NLT_QuestionStep.source, `NLT_RecordFrames.questions, `NLT_RecordFrames.parent, `NLT_ReplyInstalled.at_event, `NLT_ReplyInstalled.installed, `NLT_Reseed.source, `NLT_ReseedTransport.forward])
    else if mode == "proof4" then
      (#[`NLT_COMBINED_IMPORT], #[`NLT_Root.root, `NLT_RuntimeDigest.resume_same, `NLT_RuntimeDigest.reply_same, `NLT_Select.unique, `NLT_SiteOrder.source, `NLT_Subcuts.erase, `NLB_Parent.native_fold, `NKU_ParentFold.source, `NKU_ParentFold.cohort, `NKU_ParentFold.clauses, `NLN_TX2_053.root, `AspisR1.RPx_Deployed.deployed])
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
