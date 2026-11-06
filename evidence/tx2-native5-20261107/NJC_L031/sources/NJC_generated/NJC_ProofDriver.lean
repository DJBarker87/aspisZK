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
      (#[`NJC_COMBINED_IMPORT], #[`NJC_ClosedCalls.inactive_clause, `NJC_ClosedCalls.geometry_clause, `NJC_ClosedCalls.installed, `NJC_ClosedCalls.parent, `NJC_ClosedCalls.opening_clause, `NJC_ReaderResults.decodeK, `NJC_ReaderResults.k, `NJC_ReaderResults.boundedK, `NJC_EReaderResults.decodeE, `NJC_EReaderResults.e, `NJC_ReaderWindows.e, `NJC_ReaderWindows.k, `NJC_ReaderWindows.raw, `NJC_ResumeCalls.clause, `NJC_ResumeCalls.installed])
    else if mode == "proof1" then
      (#[`NJC_COMBINED_IMPORT], #[`NJC_ResumeCalls.parent, `NJC_Sections.child, `NJC_Sections.semantic, `NJC_Sections.weights, `NJC_Sections.induction, `NJC_QueryOccurrence.checkpoint_size, `NJC_QueryOccurrence.closed, `NJC_CutTypes.powers_array, `NJC_CutTypes.readerK, `NJC_CutTypes.powers, `NJC_CutTypes.weightStep, `AspisR1.RPx_Deployed.deployed])
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
