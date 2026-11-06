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
      (#[`NLB_COMBINED_IMPORT], #[`NLB_Parent.C01_step, `NLB_Parent.C02_step, `NLB_Parent.C03_step, `NLB_Parent.C04_step, `NLB_Parent.C05_step, `NLB_Parent.C06_step, `NLB_Parent.C07_step, `NLB_Parent.C08_step, `NLB_Parent.C09_step, `NLB_ErrorTransport.common_transport, `NLB_ErrorTransport.bind_congr, `NLB_ErrorTransport.question_rel])
    else if mode == "proof1" then
      (#[`NLB_COMBINED_IMPORT], #[`NLB_ErrorTransport.error_not_equal, `NLB_Parent.events_from_cuts, `NLB_Parent.observed_steps, `NLB_Parent.semantic_fold, `NLB_Parent.query_step, `NLB_ErrorTransport.question_trace, `NLB_ErrorTransport.native_error_prefix, `NLB_ErrorTransport.source_abort_prefix, `NLB_ErrorTransport.divergence_prefix, `NLB_Parent.steps, `NLB_Parent.execution, `AspisR1.RPx_Deployed.deployed])
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
