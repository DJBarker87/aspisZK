import Lean
import PV_B3P_NEPWalker569227
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (_args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := "b3p6_cohort583"
  let modules := #[
    `PV_B3P_NormalizedIndices583227_00,
    `PV_B3P_NormalizedIndices583227_01,
    `PV_B3P_ArithmeticEvents583227,
    `PV_B3P_ComputedIndices583227,
    `PV_B3P_MetadataIndices584227,
    `PV_B3P_CallbackIndices584227]
  let roots := #[
    `PV_B3P_NormalizedIndices583227_00.certificate_0,
    `PV_B3P_NormalizedIndices583227_00.certificate_1,
    `PV_B3P_NormalizedIndices583227_00.certificate_2,
    `PV_B3P_NormalizedIndices583227_00.certificate_3,
    `PV_B3P_NormalizedIndices583227_00.certificate_4,
    `PV_B3P_NormalizedIndices583227_00.certificate_5,
    `PV_B3P_NormalizedIndices583227_00.certificate_6,
    `PV_B3P_NormalizedIndices583227_00.certificate_7,
    `PV_B3P_NormalizedIndices583227_00.certificate_8,
    `PV_B3P_NormalizedIndices583227_00.certificate_9,
    `PV_B3P_NormalizedIndices583227_00.certificate_10,
    `PV_B3P_NormalizedIndices583227_00.certificate_11,
    `PV_B3P_NormalizedIndices583227_00.certificate_12,
    `PV_B3P_NormalizedIndices583227_00.certificate_13,
    `PV_B3P_NormalizedIndices583227_00.certificate_14,
    `PV_B3P_NormalizedIndices583227_00.certificate_15,
    `PV_B3P_NormalizedIndices583227_00.certificate_16,
    `PV_B3P_NormalizedIndices583227_00.certificate_17,
    `PV_B3P_NormalizedIndices583227_00.certificate_18,
    `PV_B3P_NormalizedIndices583227_00.certificate_19,
    `PV_B3P_NormalizedIndices583227_00.certificate_20,
    `PV_B3P_NormalizedIndices583227_00.certificate_21,
    `PV_B3P_NormalizedIndices583227_00.certificate_22,
    `PV_B3P_NormalizedIndices583227_00.certificate_23,
    `PV_B3P_NormalizedIndices583227_01.certificate_24,
    `PV_B3P_NormalizedIndices583227_01.certificate_25,
    `PV_B3P_NormalizedIndices583227_01.certificate_26,
    `PV_B3P_NormalizedIndices583227_01.certificate_27,
    `PV_B3P_NormalizedIndices583227_01.certificate_28,
    `PV_B3P_NormalizedIndices583227_01.certificate_29,
    `PV_B3P_NormalizedIndices583227_01.certificate_30,
    `PV_B3P_NormalizedIndices583227_01.certificate_31,
    `PV_B3P_NormalizedIndices583227_01.certificate_32,
    `PV_B3P_NormalizedIndices583227_01.certificate_33,
    `PV_B3P_NormalizedIndices583227_01.certificate_34,
    `PV_B3P_NormalizedIndices583227_01.certificate_35,
    `PV_B3P_NormalizedIndices583227_01.certificate_36,
    `PV_B3P_NormalizedIndices583227_01.certificate_37,
    `PV_B3P_NormalizedIndices583227_01.certificate_38,
    `PV_B3P_NormalizedIndices583227_01.certificate_39,
    `PV_B3P_NormalizedIndices583227_01.certificate_40,
    `PV_B3P_NormalizedIndices583227_01.certificate_41,
    `PV_B3P_NormalizedIndices583227_01.certificate_42,
    `PV_B3P_NormalizedIndices583227_01.certificate_43,
    `PV_B3P_NormalizedIndices583227_01.certificate_44,
    `PV_B3P_NormalizedIndices583227_01.certificate_45,
    `PV_B3P_NormalizedIndices583227_01.certificate_46,
    `PV_B3P_NormalizedIndices583227_01.certificate_47,
    `PV_B3P_ArithmeticEvents583227.evaluate_bound,
    `PV_B3P_ArithmeticEvents583227.event_guard,
    `PV_B3P_ArithmeticEvents583227.event_certificate,
    `PV_B3P_ComputedIndices583227.certificate_0,
    `PV_B3P_ComputedIndices583227.certificate_1,
    `PV_B3P_ComputedIndices583227.certificate_2,
    `PV_B3P_ComputedIndices583227.certificate_3,
    `PV_B3P_ComputedIndices583227.certificate_4,
    `PV_B3P_ComputedIndices583227.certificate_5,
    `PV_B3P_ComputedIndices583227.certificate_6,
    `PV_B3P_ComputedIndices583227.certificate_7,
    `PV_B3P_ComputedIndices583227.certificate_8,
    `PV_B3P_ComputedIndices583227.certificate_9,
    `PV_B3P_ComputedIndices583227.certificate_10,
    `PV_B3P_ComputedIndices583227.certificate_11,
    `PV_B3P_ComputedIndices583227.certificate_12,
    `PV_B3P_ComputedIndices583227.certificate_13,
    `PV_B3P_ComputedIndices583227.certificate_14,
    `PV_B3P_ComputedIndices583227.certificate_15,
    `PV_B3P_ComputedIndices583227.certificate_16,
    `PV_B3P_ComputedIndices583227.certificate_17,
    `PV_B3P_ComputedIndices583227.certificate_18,
    `PV_B3P_ComputedIndices583227.certificate_19,
    `PV_B3P_MetadataIndices584227.certificate_0,
    `PV_B3P_MetadataIndices584227.certificate_1,
    `PV_B3P_MetadataIndices584227.certificate_2,
    `PV_B3P_MetadataIndices584227.certificate_3,
    `PV_B3P_CallbackIndices584227.certificate_0,
    `PV_B3P_CallbackIndices584227.certificate_1,
    `PV_B3P_CallbackIndices584227.certificate_2,
    `PV_B3P_CallbackIndices584227.certificate_3,
    `PV_B3P_CallbackIndices584227.certificate_4,
    `PV_B3P_CallbackIndices584227.certificate_5,
    `PV_B3P_CallbackIndices584227.certificate_6,
    `PV_B3P_CallbackIndices584227.certificate_7,
    `PV_B3P_CallbackIndices584227.certificate_8,
    `PV_B3P_CallbackIndices584227.certificate_9,
    `PV_B3P_CallbackIndices584227.certificate_10,
    `PV_B3P_CallbackIndices584227.certificate_11,
    `PV_B3P_CallbackIndices584227.certificate_12,
    `PV_B3P_CallbackIndices584227.certificate_13,
    `PV_B3P_CallbackIndices584227.certificate_14,
    `PV_B3P_CallbackIndices584227.certificate_15,
    `PV_B3P_CallbackIndices584227.certificate_16,
    `PV_B3P_CallbackIndices584227.certificate_17,
    `PV_B3P_CallbackIndices584227.certificate_18,
    `PV_B3P_CallbackIndices584227.certificate_19,
    `PV_B3P_CallbackIndices584227.certificate_20,
    `PV_B3P_CallbackIndices584227.certificate_21]
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
