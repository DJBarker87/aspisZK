import Lean
import PV_B3P_NEPWalker569227
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (_args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := "b3p6_cohort579"
  let modules := #[
    `PV_B3P_IndexCounter579227,
    `PV_B3P_IndexCursorFamily579227]
  let roots := #[
    `PV_B3P_IndexCounter579227.state_ordered,
    `PV_B3P_IndexCounter579227.ordered_guard,
    `PV_B3P_IndexCounter579227.index_guard,
    `PV_B3P_IndexCounter579227.add_guard,
    `PV_B3P_IndexCounter579227.ordered_certificate,
    `PV_B3P_IndexCounter579227.index_certificate,
    `PV_B3P_IndexCounter579227.callback_assertion_certificate,
    `PV_B3P_IndexCounter579227.add_certificate,
    `PV_B3P_IndexCursorFamily579227.certificate_207_9851,
    `PV_B3P_IndexCursorFamily579227.certificate_207_9856,
    `PV_B3P_IndexCursorFamily579227.certificate_207_9882,
    `PV_B3P_IndexCursorFamily579227.certificate_329_23398,
    `PV_B3P_IndexCursorFamily579227.certificate_329_30694,
    `PV_B3P_IndexCursorFamily579227.certificate_329_23409]
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
