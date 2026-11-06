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
      (#[`NJR_COMBINED_IMPORT], #[`NJR_FinishWindows.word_window, `NJR_FinishWindows.windows, `NJR_FinishWindows.three, `NJR_Cuts.pending_store, `NJR_Cuts.query_reconstruct, `NJR_Cuts.flush_store, `NJR_FinishPrepared.returned, `NJR_ReservationSites.resume_filled, `NJR_ReservationSites.pending, `NJR_ReservationSites.pending_error])
    else if mode == "proof1" then
      (#[`NJR_COMBINED_IMPORT], #[`NJR_ReaderCut.error_prefix, `NJR_ReaderCut.backing, `NJR_FlushComposition.windows, `NJR_FlushComposition.source, `NJR_FinishDomain.reached, `NJR_HistoryFromScan.little_word, `NJR_HistoryFromScan.region, `NJR_HistoryFromScan.source, `NJR_ReservationRaw.zero, `NJR_ReservationRaw.pending])
    else if mode == "proof2" then
      (#[`NJR_COMBINED_IMPORT], #[`NJR_FinishFromScan.reached, `NJR_FinishInstall.at_call, `NJR_ViewFinish.ranges, `NJR_ViewFinish.windows, `NJR_FinishAtSourceView.at_source_view, `NJR_PayloadExt.injective, `NJR_PayloadExt.vector, `NJR_HistoryBinding.parsed, `NJR_HistoryBinding.current, `NJR_HistoryBinding.by_p2prime])
    else if mode == "proof3" then
      (#[`NJR_COMBINED_IMPORT], #[`NJR_HistoryBinding.matches_without_binding, `NJR_ChecksumDomain.public_length, `NJR_ChecksumDomain.of_header, `NJR_ChecksumDomain.of_source_cuts, `NJR_ChecksumAtHeadline.accepted_pair, `NJR_SuccessReads.horner, `NJR_SuccessReads.polynomial, `NJR_SuccessReads.round, `NJR_SuccessReads.dot, `NJR_SourceFinishReads.rounds])
    else if mode == "proof4" then
      (#[`NJR_COMBINED_IMPORT], #[`NJR_SourceFinishReads.source, `NJR_DecodedWords.decoded, `NJR_DecodedWords.window, `NJR_WindowsFromFinish.polynomial, `NJR_WindowsFromFinish.dot, `NJR_WindowsFromFinish.source, `NJR_AcceptedFinishDomain.lengths, `NJR_AcceptedFinishDomain.reached, `AspisR1.NJF_Root.finish, `AspisR1.RPx_Deployed.deployed])
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
