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
  let (modules, roots) :=
    if mode == "proof0" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_BaseMultiply.product_bound, `AspisR1.NFF_QueryProduct.emitted, `AspisR1.NFI_InnerCut.same_input, `AspisR1.NFI_TraceResult.erase_pure])
    else if mode == "proof1" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_LoggedOuterLoop.replay, `AspisR1.NFF_FullWrapper.replay, `AspisR1.NFI_InnerCut.erased, `AspisR1.NFI_TraceResult.fail_prefix])
    else if mode == "proof2" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_RawLog.same_log, `AspisR1.NFF_LoggedStep.active, `AspisR1.NFI_InnerTrace.replay, `AspisR1.NFI_TraceResult.div_prefix])
    else if mode == "proof3" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_BaseMultiply.word_product, `AspisR1.RPx_Deployed.deployed, `AspisR1.NFI_InnerTrace.frames, `AspisR1.NFI_WrapperDomains.reached])
    else if mode == "proof4" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_LoggedOuterStep.active, `AspisR1.NFF_FullWrapper.headline, `AspisR1.NFI_OpeningFrame.original_byte, `AspisR1.NFI_WrapperTrace.erased])
    else if mode == "proof5" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_RawLog.replay, `AspisR1.NFF_LoggedTail.replay, `AspisR1.NFI_OpeningFrame.same_heap_frame, `AspisR1.NFI_WrapperTrace.headline])
    else if mode == "proof6" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_BaseMultiply.source, `AspisR1.NFE_DotBridge.one, `AspisR1.NFI_OpeningFrame.arbitrary_complement, `AspisR1.NFF_LoggedOuterStep.stopped])
    else if mode == "proof7" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_LoggedEight.cell_replay, `AspisR1.NFI_OpeningFrame.receiver_and_return_frame, `AspisR1.NFF_RawTypedLog.canonical, `AspisR1.NFF_LoggedWrapper.replay])
    else if mode == "proof8" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFI_OuterActual.emitted, `AspisR1.NFF_Cell.replay, `AspisR1.NFE_WrapperBridge.four, `AspisR1.NFI_OuterCut.same_input])
    else if mode == "proof9" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_LoggedPush.private_replay, `AspisR1.NFF_LoggedEight.replay, `AspisR1.NFI_OuterCut.erased, `AspisR1.NFF_RawTypedLog.operands])
    else if mode == "proof10" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_LoggedWrapper.headline, `AspisR1.NFI_OuterTrace.replay, `AspisR1.NFF_Cell.primitive_reply, `AspisR1.NFF_LoggedDomains.one])
    else if mode == "proof11" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFI_OuterTrace.frames, `AspisR1.NFF_LoggedPush.public_replay, `AspisR1.NFF_LoggedLoop.replay, `AspisR1.NFI_PrivateCuts.installed])
    else if mode == "proof12" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_RawTypedLog.replay, `AspisR1.NFF_ProductCall.replay, `AspisR1.NFI_SingleDomains.reached, `AspisR1.NFF_CoreReduction.same])
    else if mode == "proof13" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_LoggedDomains.four, `AspisR1.NFI_SingleTrace.main_erased, `AspisR1.NFF_LoggedRaw.replay, `AspisR1.NFF_LoggedOne.replay])
    else if mode == "proof14" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFI_SingleTrace.erased, `AspisR1.NFF_ReadDomains.canonical, `AspisR1.NFF_RawLog.natural, `AspisR1.NFI_SingleTrace.emitted])
    else if mode == "proof15" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_CoreReduction.source, `AspisR1.NFI_FailurePrefixes.rejected, `AspisR1.NFI_TailTrace.erased, `AspisR1.NFF_LoggedRaw.headline])
    else if mode == "proof16" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFI_FailurePrefixes.trace_prefix, `AspisR1.NFI_TailTrace.emitted, `AspisR1.NFF_ReadDomains.selected, `AspisR1.NFI_InnerActual.emitted])
    else if mode == "proof17" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFI_TraceResult.erase_bind, `AspisR1.NFF_FullOne.replay, `AspisR1.NFI_InnerActual.borrowed_frame, `AspisR1.NFI_TraceResult.erase_lift])
    else if mode == "proof18" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFF_LoggedStep.update_replay, `AspisR1.NFI_InnerActual.canonical_at_cut, `AspisR1.NFI_TraceResult.erase_mark, `AspisR1.NFM_Control.next0])
    else if mode == "proof19" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_Control.next1, `AspisR1.NFM_Control.next2, `AspisR1.NFM_Control.next3, `AspisR1.NFM_Control.next4])
    else if mode == "proof20" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_Control.next5, `AspisR1.NFM_Control.next6, `AspisR1.NFM_Control.fixed_outer, `AspisR1.NFM_Control.fixed_terms])
    else if mode == "proof21" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_Control.term_count, `AspisR1.NFM_Control.state_sequence, `AspisR1.NFM_Control.next_at, `AspisR1.NFM_Control.body_at])
    else if mode == "proof22" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_Control.stopped, `AspisR1.NFM_InnerControl.active, `AspisR1.NFM_InnerControl.complete, `AspisR1.NFM_InnerControl.at_cut])
    else if mode == "proof23" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_Thread.advance0, `AspisR1.NFM_Thread.advance1, `AspisR1.NFM_Thread.advance2, `AspisR1.NFM_Thread.advance3])
    else if mode == "proof24" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_Thread.advance4, `AspisR1.NFM_Thread.advance5, `AspisR1.NFM_Thread.advance6, `AspisR1.NFM_Thread.body])
    else if mode == "proof25" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_Thread.advance, `AspisR1.NFM_Thread.main, `AspisR1.NFM_Cuts.window_erased])
    else if mode == "proof26" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_Cuts.erased, `AspisR1.NFM_Cuts.main, `AspisR1.NFM_Cuts.abort_prefix])
    else if mode == "proof27" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_Single.main_same, `AspisR1.NFM_Single.same, `AspisR1.NFM_Single.emitted])
    else if mode == "proof28" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_Single.domains, `AspisR1.NFM_Domains.limb_cap, `AspisR1.NFM_Domains.sums_reset])
    else if mode == "proof29" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_Domains.slots, `AspisR1.NFM_Span.scalar, `AspisR1.NFM_Span.tail])
    else if mode == "proof30" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_Span.window, `AspisR1.NFM_Frames.window, `AspisR1.NFM_Frames.sequence])
    else if mode == "proof31" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_CallDomains.tail_counts, `AspisR1.NFM_CallDomains.terminal, `AspisR1.NFM_ProductInstance.main_law])
    else if mode == "proof32" then
      (#[`NFM_CombinedFinal], #[`AspisR1.NFM_ProductInstance.tail_law, `AspisR1.NFM_ProductInstance.installed, `AspisR1.NFM_ProductInstance.wrapper])
    else if mode == "fixtures" then
      (#[`NEP_Planted, `NEP_Mutations],
       #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
         `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
         `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
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
