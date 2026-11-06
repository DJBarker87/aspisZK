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
      (#[`NJC_COMBINED_IMPORT], #[`NJC_ClosedCalls.inactive_clause, `NJC_ClosedCalls.geometry_clause, `NJC_ClosedCalls.installed, `NJC_ClosedCalls.parent, `NJC_ClosedCalls.opening_clause, `NJC_ReaderResults.decodeK, `NJC_ReaderResults.k, `NJC_ReaderResults.boundedK, `NJC_EReaderResults.decodeE, `NJC_EReaderResults.e, `NJC_ReaderWindows.e, `NJC_ReaderWindows.k, `NJC_ReaderWindows.raw, `NJC_Sections.child, `NJC_Sections.semantic])
    else if mode == "proof1" then
      (#[`NJC_COMBINED_IMPORT], #[`NJC_Sections.weights, `NJC_Sections.induction, `NJC_QueryOccurrence.checkpoint_size, `NJC_QueryOccurrence.closed, `NJC_CutTypes.powers_array, `NJC_CutTypes.readerK, `NJC_CutTypes.powers, `NJC_CutTypes.weightStep, `NJC_Contains.scalar, `NJC_Contains.list, `NJC_Contains.source, `NJC_ValidateArithmetic.shift, `NJC_ValidateArithmetic.increment, `NJC_ValidateStep.source, `NJC_ValidatePort.loop_exact])
    else if mode == "proof2" then
      (#[`NJC_COMBINED_IMPORT], #[`NJC_ValidatePort.source, `NJC_ValidatePort.frame, `NJC_ValidateCalls.clause, `NJC_ValidateCalls.reference, `NJC_ValidateCalls.source, `NJC_FilledClause.zero, `NJC_FilledClause.source, `NJC_RawPort.transport, `NJC_RawPort.bounded, `NJC_ScanPartition.thirty, `NJC_ScanPartition.blocks, `NJC_ScanPartition.opening, `NJC_ScanViews.query, `NJC_ScanViews.subwindow, `NJC_ScanViews.final])
    else if mode == "proof3" then
      (#[`NJC_COMBINED_IMPORT], #[`NJC_ResumeCalls.clause, `NJC_ResumeCalls.installed, `NJC_ResumeCalls.parent, `NJC_RawWindows.k, `NJC_RawWindows.e, `NJC_OrderedCalls.mark, `NJC_OrderedCalls.powers, `NJC_OrderedCalls.installed, `NJC_OrderedCalls.parent, `NJC_OptionClause.source, `NJC_OptionClause.frame, `NJC_ValidateResult.model, `NJC_ValidateResult.source, `NJC_CopyFrame.window, `NJC_CopyFrame.frame])
    else if mode == "proof4" then
      (#[`NJC_COMBINED_IMPORT], #[`NJC_CopyFrame.compose, `AspisR1.RPx_Deployed.deployed])
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
