import Lean
import PV_B3P_NEPWalker569227
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (_args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := "b3p6_cohort569"
  let modules := #[`PV_B3P_Dependency569227, `PV_B3P_InitializerFormatting569227,
    `PV_B3P_InclusiveFoldFormatting569227, `PV_B3P_IndexRangeFormatting569227,
    `PV_B3P_LiteralEvents569227, `PV_B3P_SourceCone557227]
  let roots := #[`PV_B3P_NextExtraction569227.source_binding,
    `PV_B3P_InclusiveFormatting569227.model_binding,
    `PV_B3P_InclusiveFoldFormatting569227.handler_independent,
    `PV_B3P_InitializerFormatting569227.initial_independent,
    `PV_B3P_IndexRangeFormatting569227.handler_independent,
    `PV_B3P_IndexRangeFormatting569227.shared_check,
    `PV_B3P_PreconditionFormatting569227.slice_subtraction_check,
    `PV_B3P_Dependency569227.partial_closure,
    `PV_B3P_Closure557227.selected_callback_residual557,
    `PV_B3P_Closure557227.source_cone_reference557]
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
