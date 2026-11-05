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
      (#[`NID_COMBINED_IMPORT], #[`NID_ResumeCanonical.sourceK_canonical, `NID_ResumeCanonical.sourceE_canonical, `NID_ResumeCanonical.k_at, `NID_ResumeCanonical.e_at, `NID_ResumeFields.returned, `NID_ResumeCallerDomain.power, `NID_ResumeCallerDomain.wide, `NID_ResumeCallerDomain.gamma, `NID_ResumeQuery.weights, `NID_ResumeQuery.domain, `NID_MerkleLeafPacket.selected, `NID_MerkleLeafPacket.fail_no_suffix, `NID_MerkleLeafPacket.div_no_suffix, `NID_BoundedReaders.k, `NID_BoundedReaders.e, `NID_BoundedReaders.weight, `NID_BoundedReaders.semantic, `NID_ReadListTransport.source, `NID_WeightReadsTransport.reads, `NID_WeightReadsTransport.weights])
    else if mode == "proof1" then
      (#[`NID_COMBINED_IMPORT], #[`NID_WeightReadsTransport.checkpoint, `NID_ReadStepFrame.next, `NID_ReadStepFrame.remaining, `NID_WithKTransport.source, `NID_SemanticTransport.sequence, `NID_SemanticTransport.source, `NID_RawOffsetCover.cover, `NID_RawOffsetCover.unique, `NID_TailView.produced, `NID_TailView.fields, `NID_TailView.widths, `NID_FinishAlpha.supplied, `NID_FinishAlpha.primitive, `NID_RawWindowFrame.row, `NID_RawWindowFrame.rows, `NID_RawWindowFrame.contiguous, `AspisR1.NCI_QueryInvariant.accepted_head, `AspisR1.NCI_QueryInvariant.accepted_bounds, `AspisR1.NCI_QueryInvariant.accepted_fresh, `AspisR1.NCI_QueryInvariant.accepted_unique])
    else if mode == "proof2" then
      (#[`NID_COMBINED_IMPORT], #[`NID_ResumeQueries.returned, `NID_KOffsetCover.rho, `NID_KOffsetCover.semantic, `NID_KOffsetCover.coordinates, `NID_KOffsetCover.power, `NID_KOffsetCover.weights, `NID_KOffsetCover.bounded, `NID_KmxComposition.copy_four_spec, `NID_KmxComposition.copy_four_frame, `NID_KmxComposition.rows_spec, `NID_KmxComposition.all64, `NID_KmxComposition.selected, `NID_ResumePrefix.size_error, `NID_ResumeEmission.verifier.resume, `NID_ResumeEmission.verifier.candidate.tx2_common, `AspisR1.RPx_Deployed.deployed])
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
