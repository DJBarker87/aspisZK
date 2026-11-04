import Lean
import PV_B3P_NEPWalker569227
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (_args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := "b3p6_cohort587"
  let modules := #[
    `PV_B3P_MinRangeEvents587227,
    `PV_B3P_SliceMetadata581227,
    `PV_B3P_FourWayEvents587227,
    `PV_B3P_TrailingEvents587227,
    `PV_B3P_PositiveRangeEvents587227,
    `PV_B3P_NestedIndices587227,
    `PV_B3P_MinRangeIndices587227,
    `PV_B3P_RangeSlice587227,
    `PV_B3P_StepPanic587227,
    `PV_B3P_CaptureGuards587227,
    `PV_B3P_SharedScalarIndices587227,
    `PV_B3P_TrailingIndices587227,
    `PV_B3P_PositiveRange587227]
  let roots := #[
    `PV_B3P_MinRangeEvents587227.sourceMin_le_right,
    `PV_B3P_MinRangeEvents587227.event_guard,
    `PV_B3P_MinRangeEvents587227.event_certificate,
    `PV_B3P_SliceMetadata581227.ordered_wrapped_width,
    `PV_B3P_SliceMetadata581227.event_guard,
    `PV_B3P_SliceMetadata581227.event_certificate,
    `PV_B3P_FourWayEvents587227.event_guard,
    `PV_B3P_FourWayEvents587227.event_certificate,
    `PV_B3P_TrailingEvents587227.event_guard,
    `PV_B3P_TrailingEvents587227.event_certificate,
    `PV_B3P_PositiveRangeEvents587227.counter_bounds,
    `PV_B3P_PositiveRangeEvents587227.source_next,
    `PV_B3P_PositiveRangeEvents587227.event_guard,
    `PV_B3P_PositiveRangeEvents587227.event_certificate,
    `PV_B3P_NestedIndices587227.certificate_0,
    `PV_B3P_NestedIndices587227.certificate_1,
    `PV_B3P_NestedIndices587227.certificate_2,
    `PV_B3P_NestedIndices587227.certificate_3,
    `PV_B3P_NestedIndices587227.certificate_4,
    `PV_B3P_NestedIndices587227.certificate_5,
    `PV_B3P_NestedIndices587227.certificate_6,
    `PV_B3P_MinRangeIndices587227.certificate_0,
    `PV_B3P_MinRangeIndices587227.certificate_1,
    `PV_B3P_RangeSlice587227.certificate,
    `PV_B3P_StepPanic587227.certificate,
    `PV_B3P_CaptureGuards587227.certificate_0,
    `PV_B3P_CaptureGuards587227.certificate_1,
    `PV_B3P_CaptureGuards587227.certificate_2,
    `PV_B3P_CaptureGuards587227.certificate_3,
    `PV_B3P_CaptureGuards587227.panic_428,
    `PV_B3P_CaptureGuards587227.panic_536,
    `PV_B3P_SharedScalarIndices587227.certificate_0,
    `PV_B3P_SharedScalarIndices587227.certificate_1,
    `PV_B3P_TrailingIndices587227.certificate_30838,
    `PV_B3P_TrailingIndices587227.certificate_30843,
    `PV_B3P_PositiveRange587227.certificate]
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
