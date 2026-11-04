import Lean
import PV_B3P_NEPWalker569227
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (_args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := "b3p6_cohort592"
  let modules := #[
    `PV_B3P_RangeComputedEvents592227,
    `PV_B3P_RangeArithmetic592227,
    `PV_B3P_TableEvents592227,
    `PV_B3P_TableIndices592227,
    `PV_B3P_CountdownEvents592227,
    `PV_B3P_CountdownIndices592227,
    `PV_B3P_StableIndices592227,
    `PV_B3P_CallerIndices592227,
    `PV_B3P_InclusiveEvents592227,
    `PV_B3P_PreweightedIndices592227,
    `PV_B3P_ExpandEvents592227,
    `PV_B3P_ExpandFrame592227,
    `PV_B3P_ExpandIndices592227,
    `PV_B3P_FoldIndices592227,
    `PV_B3P_RowEvents592227,
    `PV_B3P_RowIndices592227]
  let roots := #[
    `PV_B3P_RangeComputedEvents592227.event_certificate,
    `PV_B3P_RangeArithmetic592227.certificate_0,
    `PV_B3P_RangeArithmetic592227.certificate_1,
    `PV_B3P_RangeArithmetic592227.certificate_2,
    `PV_B3P_RangeArithmetic592227.certificate_3,
    `PV_B3P_RangeArithmetic592227.certificate_4,
    `PV_B3P_RangeArithmetic592227.certificate_5,
    `PV_B3P_TableEvents592227.event_certificate,
    `PV_B3P_TableIndices592227.certificate_70_29689,
    `PV_B3P_TableIndices592227.certificate_70_29694,
    `PV_B3P_TableIndices592227.certificate_70_29699,
    `PV_B3P_TableIndices592227.certificate_70_29704,
    `PV_B3P_TableIndices592227.certificate_70_29709,
    `PV_B3P_TableIndices592227.certificate_245_30521,
    `PV_B3P_CountdownEvents592227.counter_bound,
    `PV_B3P_CountdownEvents592227.event_certificate,
    `PV_B3P_CountdownIndices592227.certificate_0,
    `PV_B3P_CountdownIndices592227.certificate_1,
    `PV_B3P_CountdownIndices592227.certificate_2,
    `PV_B3P_StableIndices592227.certificate_0,
    `PV_B3P_CallerIndices592227.certificate_15_0,
    `PV_B3P_CallerIndices592227.certificate_15_1,
    `PV_B3P_CallerIndices592227.certificate_15_2,
    `PV_B3P_CallerIndices592227.certificate_15_3,
    `PV_B3P_CallerIndices592227.certificate_15_4,
    `PV_B3P_CallerIndices592227.certificate_15_5,
    `PV_B3P_CallerIndices592227.certificate_39_0,
    `PV_B3P_CallerIndices592227.certificate_39_1,
    `PV_B3P_CallerIndices592227.certificate_39_2,
    `PV_B3P_CallerIndices592227.certificate_240_0,
    `PV_B3P_CallerIndices592227.certificate_240_1,
    `PV_B3P_CallerIndices592227.certificate_240_2,
    `PV_B3P_CallerIndices592227.certificate_240_3,
    `PV_B3P_CallerIndices592227.certificate_240_4,
    `PV_B3P_CallerIndices592227.certificate_240_5,
    `PV_B3P_CallerIndices592227.certificate_240_6,
    `PV_B3P_CallerIndices592227.certificate_240_7,
    `PV_B3P_CallerIndices592227.mask_column,
    `PV_B3P_InclusiveEvents592227.next_end,
    `PV_B3P_InclusiveEvents592227.event_certificate,
    `PV_B3P_PreweightedIndices592227.certificate_3ee816ee3badc75d5ede_29589_0,
    `PV_B3P_PreweightedIndices592227.certificate_3ee816ee3badc75d5ede_29589_1,
    `PV_B3P_PreweightedIndices592227.certificate_3ee816ee3badc75d5ede_29594_0,
    `PV_B3P_PreweightedIndices592227.certificate_3ee816ee3badc75d5ede_29594_1,
    `PV_B3P_PreweightedIndices592227.certificate_412c274a9954e734bc86_29589_0,
    `PV_B3P_PreweightedIndices592227.certificate_412c274a9954e734bc86_29589_1,
    `PV_B3P_PreweightedIndices592227.certificate_412c274a9954e734bc86_29594_0,
    `PV_B3P_PreweightedIndices592227.certificate_412c274a9954e734bc86_29594_1,
    `PV_B3P_PreweightedIndices592227.certificate_5a23c8cad0af20d0f4fb_29589_0,
    `PV_B3P_PreweightedIndices592227.certificate_5a23c8cad0af20d0f4fb_29594_0,
    `PV_B3P_PreweightedIndices592227.certificate_b4548570fddcc1efb85f_29589_0,
    `PV_B3P_PreweightedIndices592227.certificate_b4548570fddcc1efb85f_29594_0,
    `PV_B3P_PreweightedIndices592227.certificate_b58ea6f00dc81e4bbc15_29589_0,
    `PV_B3P_PreweightedIndices592227.certificate_b58ea6f00dc81e4bbc15_29594_0,
    `PV_B3P_PreweightedIndices592227.certificate_d86379aa4e1f98af6102_29589_0,
    `PV_B3P_PreweightedIndices592227.certificate_d86379aa4e1f98af6102_29594_0,
    `PV_B3P_ExpandEvents592227.depth_step,
    `PV_B3P_ExpandEvents592227.width_step,
    `PV_B3P_ExpandEvents592227.event_certificate,
    `PV_B3P_ExpandFrame592227.countdown_value,
    `PV_B3P_ExpandFrame592227.coordinate_step,
    `PV_B3P_ExpandFrame592227.width_value_step,
    `PV_B3P_ExpandIndices592227.certificate_64_29747,
    `PV_B3P_ExpandIndices592227.certificate_64_29732,
    `PV_B3P_ExpandIndices592227.certificate_64_29737,
    `PV_B3P_ExpandIndices592227.certificate_64_29742,
    `PV_B3P_ExpandIndices592227.certificate_16_29747,
    `PV_B3P_ExpandIndices592227.certificate_16_29732,
    `PV_B3P_ExpandIndices592227.certificate_16_29737,
    `PV_B3P_ExpandIndices592227.certificate_16_29742,
    `PV_B3P_FoldIndices592227.array_value,
    `PV_B3P_FoldIndices592227.inclusive_value,
    `PV_B3P_FoldIndices592227.range_0_0,
    `PV_B3P_FoldIndices592227.range_1_0,
    `PV_B3P_FoldIndices592227.range_2_0,
    `PV_B3P_FoldIndices592227.range_2_1,
    `PV_B3P_RowEvents592227.event_certificate,
    `PV_B3P_RowIndices592227.certificate_0,
    `PV_B3P_RowIndices592227.certificate_1,
    `PV_B3P_RowIndices592227.certificate_2,
    `PV_B3P_RowIndices592227.certificate_3,
    `PV_B3P_RowIndices592227.certificate_4,
    `PV_B3P_RowIndices592227.certificate_5,
    `PV_B3P_RowIndices592227.certificate_6,
    `PV_B3P_RowIndices592227.certificate_7,
    `PV_B3P_RowIndices592227.certificate_8,
    `PV_B3P_RowIndices592227.certificate_9,
    `PV_B3P_RowIndices592227.certificate_10,
    `PV_B3P_RowIndices592227.certificate_11,
    `PV_B3P_RowIndices592227.certificate_12,
    `PV_B3P_RowIndices592227.certificate_13,
    `PV_B3P_RowIndices592227.certificate_14,
    `PV_B3P_RowIndices592227.certificate_15,
    `PV_B3P_RowIndices592227.certificate_16,
    `PV_B3P_RowIndices592227.certificate_17,
    `PV_B3P_RowIndices592227.certificate_18]
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
