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
      (#[`NKO_COMBINED_IMPORT], #[`NKO_Branch.continued, `NKO_C02.at_actual, `NKO_C02.source, `NKO_C03.step_source, `NKO_C03.select_abort, `NKO_C03.source_abort, `NKO_C03.occurrence, `NKO_C03.source, `NKO_C03.option_result, `NKO_C03.selected, `NKO_C03.short, `NKO_C03.at_actual])
    else if mode == "proof1" then
      (#[`NKO_COMBINED_IMPORT], #[`NKO_C05.at_query, `NKO_C05.source, `NKO_C06.pending_eq, `NKO_C06.returned, `NKO_C07.at_actual, `NKO_C07.source, `NKO_C08.occurrence, `NKO_C08.row_at_actual, `NKO_C08.source, `NKO_C09.bounds_at_actual, `NKO_C09.child_at_actual, `NKO_C09.source])
    else if mode == "proof2" then
      (#[`NKO_COMBINED_IMPORT], #[`NKO_FinishDomain.writeback, `NKO_FrameAtActual.source, `NKO_FrameG.proof_source, `NKO_FrameG.args_source, `NKO_HalfProofWindows.retained_tail, `NKO_HalfProofWindows.cover, `NKO_HalfProofWindows.same, `NKO_IncomingCuts.transcribe, `NKO_IncomingCuts.at_actual, `NKO_LayoutArithmetic.weaken, `NKO_LayoutArithmetic.step0, `NKO_LayoutArithmetic.step1])
    else if mode == "proof3" then
      (#[`NKO_COMBINED_IMPORT], #[`NKO_LayoutArithmetic.step2, `NKO_LayoutArithmetic.step3, `NKO_LayoutArithmetic.step4, `NKO_LayoutArithmetic.step5, `NKO_LayoutArithmetic.step6, `NKO_LayoutArithmetic.step7, `NKO_LayoutArithmetic.step8, `NKO_LayoutArithmetic.step9, `NKO_LayoutArithmetic.step10, `NKO_LayoutArithmetic.step11, `NKO_LayoutArithmetic.step12, `NKO_LayoutArithmetic.step13])
    else if mode == "proof4" then
      (#[`NKO_COMBINED_IMPORT], #[`NKO_LayoutArithmetic.step14, `NKO_LayoutArithmetic.step15, `NKO_LayoutArithmetic.step16, `NKO_LayoutArithmetic.step17, `NKO_Offsets.inactive, `NKO_Offsets.round0, `NKO_Offsets.folded, `NKO_Offsets.round1, `NKO_Offsets.final_message, `NKO_Offsets.openings, `NKO_PowersResult.returned, `NKO_ProofWindows.cover])
    else if mode == "proof5" then
      (#[`NKO_COMBINED_IMPORT], #[`NKO_ProofWindows.same, `NKO_ProofWindows.disjoint, `NKO_QueryPost.returned, `NKO_QueryPost.widths, `NKO_QueryReturnG.full_result, `NKO_QueryReturnG.retained_return, `NKO_ReadonlyFrame.view_frame, `NKO_ReadonlyFrame.payload, `NKO_ReadonlyFrame.required_windows, `NKO_StageG.geometry_source, `NKO_StageG.pending_source, `NKO_StageG.geometry_error])
    else if mode == "proof6" then
      (#[`NKO_COMBINED_IMPORT], #[`NKO_StageG.geometry_success, `NKO_ViewRanges.val0, `NKO_ViewRanges.val1, `NKO_ViewRanges.valFinal, `NKO_ViewRanges.diff0, `NKO_ViewRanges.diff1, `NKO_ViewRanges.diffFinal, `NKO_ViewRanges.round0, `NKO_ViewRanges.round1, `NKO_ViewRanges.final_message, `AspisR1.NJU_GeneralFinishRoot.finish, `AspisR1.NJU_GeneralFinishRoot.ported])
    else if mode == "proof7" then
      (#[`NKO_COMBINED_IMPORT], #[`NJU_FinishAtCurrent.source_view, `AspisR1.RPx_Deployed.deployed])
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
