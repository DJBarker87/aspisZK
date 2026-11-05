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
      (#[`NIL_COMBINED_IMPORT], #[`NIL_Carriers.k_roundtrip, `NIL_Carriers.k_reverse, `NIL_Carriers.e_roundtrip, `NIL_Carriers.e_reverse, `NIL_Carriers.reader_roundtrip, `NIL_Carriers.reader_reverse, `NIL_Carriers.variant_roundtrip, `NIL_Carriers.error_roundtrip, `NIL_Carriers.error_reverse, `NIL_StatePort.point_roundtrip, `NIL_StatePort.point_reverse, `NIL_StatePort.variant_reverse, `NIL_StatePort.prepared_roundtrip, `NIL_StatePort.prepared_reverse, `NIL_StatePort.accumulator_roundtrip, `NIL_StatePort.accumulator_reverse, `NIL_StatePort.pair_roundtrip, `NIL_StatePort.pair_injective, `NIL_StatePort.reply_injective, `NIL_ResultTransport.outer_bind])
    else if mode == "proof1" then
      (#[`NIL_COMBINED_IMPORT], #[`NIL_ResultTransport.outer_comp, `NIL_ResultTransport.outer_roundtrip, `NIL_ResultTransport.inner_roundtrip, `NIL_ResultTransport.outer_injective, `NIL_ResultTransport.inner_injective, `NIL_ResultTransport.outer_ok_iff, `NIL_ResultTransport.array_comp, `NIL_ResultTransport.array_roundtrip, `NIL_ResultTransport.vec_roundtrip, `NIL_ResultReverse.inner_reverse, `NIL_ResultReverse.bind_outer, `NIL_ResultReverse.outer_if, `NIL_ResultReverse.outer_fail_iff, `NIL_ResultReverse.outer_div_iff, `NIL_FreshOps.raw_port, `NIL_FreshOps.k_port, `NIL_FreshOps.e_port, `NIL_SectionPorts.semantic, `NIL_SectionPorts.weights, `NIL_SectionPorts.validation])
    else if mode == "proof2" then
      (#[`NIL_COMBINED_IMPORT], #[`NIL_HeaderAny.loop, `NIL_HeaderAny.source, `NIL_TryTransport.map_try, `NIL_TryTransport.fresh_err, `NIL_TryTransport.fresh_ok, `NIL_AllocationPort.source, `NIL_CursorSub.value, `NIL_CursorSub.source, `NIL_MerkleStep.selected, `NIL_QueryPending.source, `NIL_QueryPending.width, `NIL_QueryPending.copied, `NIL_QueryPending.frame, `NIL_QueryPending.kmx, `NIL_WindowLayout.block, `NIL_WindowLayout.round0, `NIL_WindowLayout.round1, `NIL_WindowLayout.final, `NIL_WindowLayout.scan_final, `NIL_ReadOutput.k])
    else if mode == "proof3" then
      (#[`NIL_COMBINED_IMPORT], #[`NIL_ReadOutput.e, `NIL_ResultCases.outer_ok, `NIL_ResultCases.outer_fail, `NIL_ResultCases.outer_div, `NIL_ResultCases.inner_ok, `NIL_ResultCases.inner_err, `NIL_ResultCases.outer_ite, `NIL_ResultCases.outer_prodlet, `NIL_ResultCases.bind_congr, `NIL_ResultCases.branch_congr, `NIL_ResultCases.map_match, `NIL_ResultCases.match_congr, `NIL_ResultCases.map_bind_congr, `NIL_ResultCases.checkpoint_error, `NIL_ResumePrefixPort.source, `NIL_SpineCongr.prod, `NIL_ResumeSplit.source, `NIL_CohortSplit.source, `NIL_PortBind.source, `NIL_PortBind.read])
    else if mode == "proof4" then
      (#[`NIL_COMBINED_IMPORT], #[`NIL_ResumeComposition.source, `AspisR1.RPx_Deployed.deployed])
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
