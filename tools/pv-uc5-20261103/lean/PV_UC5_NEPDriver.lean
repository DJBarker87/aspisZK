import Lean
import PV_UC5_NEPWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := "uc5"
  let modules := #[`PVUC5Entry.Funs]
  let roots := #[`PV_UC5_Entry.main, `PV_UC5_Entry.wallet.decode_wallet_record]
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
        NEP.audit root ("/home/dombarker/project-offloads/codex-pv-uc-20261029/final-gates/uc5/NEP_" ++ mode ++ "_" ++ root.toString)
        for ax in (← collectAxioms root) do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "unapproved axiom {ax}"
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
