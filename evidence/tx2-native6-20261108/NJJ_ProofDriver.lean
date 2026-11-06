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
      (#[`NJJ_COMBINED_IMPORT], #[`NJJ_Any.loop, `NJJ_Any.source, `NJJ_Any.next_frame, `NJJ_Any.frame, `NJJ_Any.installed, `NJJ_AnyExit.next_none, `NJJ_AnyExit.next_some, `NJJ_AnyExit.false_exit, `NJJ_AnyExit.exhausted, `NJJ_Chunks.step])
    else if mode == "proof1" then
      (#[`NJJ_COMBINED_IMPORT], #[`NJJ_Chunks.end_frame, `NJJ_Chunks.window, `NJJ_Chunks.frame, `NJJ_Chunks.final, `NJJ_ChunksRemainder.offset, `NJJ_ChunksRemainder.remainder_step, `NJJ_Cuts.pending_payload, `NJJ_Cuts.pending_constructor, `NJJ_RowWindow.cell, `NJJ_RowWindow.frame])
    else if mode == "proof2" then
      (#[`NJJ_COMBINED_IMPORT], #[`NJJ_RowWindow.other, `NJJ_RowWindow.composed, `NJJ_QueryOps.fields, `NJJ_Value.source, `NJJ_Value.projection, `NJJ_Projection.source, `NJJ_Common.source, `NJJ_DomainAudit.public_lengths, `NJJ_ResumeDomains.k_bound, `NJJ_ResumeDomains.e_bound])
    else if mode == "proof3" then
      (#[`NJJ_COMBINED_IMPORT], #[`NJJ_ResumeDomains.k, `NJJ_ResumeDomains.e, `NJJ_ResumeDomains.query_bound, `NJJ_ResumeDomains.root_bound, `NJJ_ResumeDomains.weights_end, `NJJ_Constructors.array_ext, `NJJ_Constructors.point_option, `NJJ_Constructors.prepared, `NJJ_Constructors.accumulator, `NJJ_Pending.windows])
    else if mode == "proof4" then
      (#[`NJJ_COMBINED_IMPORT], #[`NJJ_Pending.source, `NJJ_PendingStep.source, `NJJ_Flush.source, `NJJ_Flush.canonical, `AspisR1.RPx_Deployed.deployed])
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
