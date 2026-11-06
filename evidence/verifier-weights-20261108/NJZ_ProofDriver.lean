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
      (#[`NJZ_COMBINED_IMPORT], #[`NJZ_Readers.raw, `NJZ_Readers.raw_cut, `NJZ_Readers.k_window, `NJZ_Readers.e_window, `NJZ_Readers.k_source, `NJZ_Readers.e_source, `NJZ_Readers.k_reference, `NJZ_Readers.e_reference, `NJZ_Weights.new_source, `NJZ_Weights.value_source])
    else if mode == "proof1" then
      (#[`NJZ_COMBINED_IMPORT], #[`NJZ_Weights.finish_source, `NJZ_Validator.members, `NJZ_Validator.unique, `NJZ_Validator.source, `NJZ_CheckpointReaders.scalar, `NJZ_CheckpointReaders.semantic, `NJZ_CheckpointReaders.weights, `NJZ_EmptyTree.parent_canonical, `NJZ_EmptyTree.root_canonical, `NJZ_EmptyTree.frame])
    else if mode == "proof2" then
      (#[`NJZ_COMBINED_IMPORT], #[`NJZ_EmptyTree.roots, `NJZ_EmptyTree.entered_domain, `NJZ_EmptyTree.empty_source, `NJZ_EmptyTree.empty_root, `NJZ_TreeParent.source, `NJZ_Echeck.step_iff, `NJZ_Echeck.chunk_iff, `NJZ_Echeck.step_chunk, `NJZ_Echeck.at_window, `NJZ_Echeck.result])
    else if mode == "proof3" then
      (#[`NJZ_COMBINED_IMPORT], #[`AspisR1.RPx_Deployed.deployed])
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
