import Lean
import PV_B3P_NEPWalker569227
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (_args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := "b3p6_cohort571"
  let modules := #[
    `PV_B3P_PatternFamilies571227,
    `PV_B3P_CounterGuards571227,
    `PV_B3P_DisabledGate571227,
    `PV_B3P_StepExpect571227,
    `PV_B3P_ControlFlowAssertion571227,
    `PV_B3P_SourceCone557227]
  let roots := #[
    `PV_B3P_PanicPatterns571227.index_out_of_bounds,
    `PV_B3P_PanicPatterns571227.slice_range,
    `PV_B3P_PanicPatterns571227.arithmetic_overflow,
    `PV_B3P_PanicPatterns571227.unwrap_expect,
    `PV_B3P_PanicPatterns571227.explicit_panic,
    `PV_B3P_PanicPatterns571227.assertion,
    `PV_B3P_PatternFamilies571227.index_out_of_bounds_family,
    `PV_B3P_PatternFamilies571227.arithmetic_overflow_family,
    `PV_B3P_PatternFamilies571227.unwrap_expect_family,
    `PV_B3P_PatternFamilies571227.explicit_panic_family,
    `PV_B3P_PatternFamilies571227.assertion_family,
    `PV_B3P_CounterGuards571227.counter_guards,
    `PV_B3P_CounterGuards571227.initial_cursor_handler_independent,
    `PV_B3P_CounterGuards571227.subtraction_guard,
    `PV_B3P_DisabledGate571227.all_prior_states,
    `PV_B3P_DisabledGate571227.source_branch,
    `PV_B3P_StepExpect571227.checked_guard,
    `PV_B3P_StepExpect571227.all_states,
    `PV_B3P_StepExpect571227.handler_independent,
    `PV_B3P_ControlFlowAssertion571227.nested_break_payload,
    `PV_B3P_ControlFlowAssertion571227.constructed_assertion,
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
