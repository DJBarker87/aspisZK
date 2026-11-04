import Lean
import PV_STX_AuditWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_STX_Account, `PV_STX_Code, `PV_STX_Composition, `PV_STX_Controls, `PV_STX_Entropy, `PV_STX_Fixed, `PV_STX_Machine, `PV_STX_Map, `PV_STX_PrefixLaws],
     #[`PV_STX_Account.entropy_erases, `PV_STX_Account.callMut_erases, `PV_STX_Account.next_erases, `PV_STX_Code.start_denote, `PV_STX_Composition.two_calls, `PV_STX_Composition.first_fault, `PV_STX_Controls.reject_then_success, `PV_STX_Controls.step_phase0, `PV_STX_Controls.step_phase1, `PV_STX_Controls.forever_prefix, `PV_STX_Controls.forever_never_returns, `PV_STX_Entropy.nonzeroBody_erases, `PV_STX_Entropy.nonzeroLoop_erases, `PV_STX_Entropy.nonzero_erases, `PV_STX_Entropy.entropyBody_erases, `PV_STX_Entropy.entropyLoop_erases, `PV_STX_Entropy.generate_erases, `PV_STX_Fixed.kont_fail, `PV_STX_Fixed.kont_div, `PV_STX_Fixed.resumed_view, `PV_STX_Fixed.step_view, `PV_STX_Fixed.advance_view, `PV_STX_Fixed.run_view, `PV_STX_Fixed.returned_agrees, `PV_STX_Machine.zero_retains_continuation, `PV_STX_Machine.failed_call_bypasses, `PV_STX_Machine.pending_call_retains, `PV_STX_Map.denote_map, `PV_STX_PrefixLaws.returned_stable, `PV_STX_PrefixLaws.fault_stable, `PV_STX_PrefixLaws.advance_add, `PV_STX_PrefixLaws.events_retained, `PV_STX_PrefixLaws.longer_prefix])
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
