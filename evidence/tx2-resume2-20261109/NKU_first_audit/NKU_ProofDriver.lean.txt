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
      (#[`NKU_COMBINED_IMPORT], #[`NKU_AfterZ.source, `NKU_Allocation.rejected, `NKU_Allocation.frame, `NKU_Array22.source, `NKU_BodyJoin.source, `NKU_Chronology.next, `NKU_Chronology.reject, `NKU_Chronology.abort])
    else if mode == "proof1" then
      (#[`NKU_COMBINED_IMPORT], #[`NKU_Chronology.diverge, `NKU_DigestBody.source, `NKU_DigestCheckpoint.source_eq_run, `NKU_DigestJoin.source, `NKU_DigestProof.source_eq_run, `NKU_DigestProof.frame, `NKU_DigestPublic.source_eq_run, `NKU_DigestPublic.frame])
    else if mode == "proof2" then
      (#[`NKU_COMBINED_IMPORT], #[`NKU_EndArithmetic.wrap, `NKU_FineDigestJoin.installed, `NKU_FineFirstJoin.installed, `NKU_FineGamma.installed, `NKU_FineGammaJoin.installed, `NKU_FineLastJoin.installed, `NKU_FineMiddleJoin.installed, `NKU_FineQueryEnd.installed])
    else if mode == "proof3" then
      (#[`NKU_COMBINED_IMPORT], #[`NKU_FineQueryFirst.installed, `NKU_FineQueryMid.installed, `NKU_FineRead.e_bind, `NKU_FineRead.k_bind, `NKU_FineRead.raw_bind, `NKU_FineRoot.suffix, `NKU_FineRoot.installed, `NKU_FineRoot.source])
    else if mode == "proof4" then
      (#[`NKU_COMBINED_IMPORT], #[`NKU_FineRoot.cohort, `NKU_FineRoots.installed, `NKU_FineRootsJoin.installed, `NKU_FineSemanticJoin.installed, `NKU_FineWords.installed, `NKU_FineZ.installed, `NKU_FineZJoin.installed, `NKU_FinishFactor.source])
    else if mode == "proof5" then
      (#[`NKU_COMBINED_IMPORT], #[`NKU_FinishTransport.source, `NKU_Front.suffix_eq, `NKU_Front.source, `NKU_Gamma.source_eq_run, `NKU_Gamma.frame, `NKU_GammaJoin.source, `NKU_GammaPack.frame, `NKU_HeaderDomain.wrong_length])
    else if mode == "proof6" then
      (#[`NKU_COMBINED_IMPORT], #[`NKU_HeaderDomain.length, `NKU_HeaderEnd.fixed, `NKU_HeaderEnd.returned, `NKU_HeaderPrefix.source, `NKU_HeaderSize.size, `NKU_HeaderSlots.same, `NKU_HeaderStep.source, `NKU_HeaderTailEnd.fixed])
    else if mode == "proof7" then
      (#[`NKU_COMBINED_IMPORT], #[`NKU_HeaderValue.source, `NKU_MixedFrame.frame, `NKU_Offsets.gamma, `NKU_Offsets.z, `NKU_Offsets.semantic, `NKU_Offsets.weights, `NKU_Pack.frame, `NKU_QueryEnd.source_eq_run])
    else if mode == "proof8" then
      (#[`NKU_COMBINED_IMPORT], #[`NKU_QueryEnd.frame, `NKU_QueryFirst.source_eq_run, `NKU_QueryFirst.frame, `NKU_QueryFirstJoin.source, `NKU_QueryJoin.source, `NKU_QueryLastJoin.source, `NKU_QueryMid.source_eq_run, `NKU_QueryMid.frame])
    else if mode == "proof9" then
      (#[`NKU_COMBINED_IMPORT], #[`NKU_QueryMiddleJoin.source, `NKU_ResumeRoot.suffix_eq, `NKU_ResumeRoot.source, `NKU_ResumeRoot.clauses, `NKU_ResumeRoot.cohort, `NKU_RootPack.frame, `NKU_Roots.source_eq_run, `NKU_Roots.frame])
    else if mode == "proof10" then
      (#[`NKU_COMBINED_IMPORT], #[`NKU_Semantic.frame, `NKU_SemanticJoin.source, `NKU_SourceConstructors.point, `NKU_SourceConstructors.prepared, `NKU_SourceConstructors.accumulator, `NKU_SourceConstructors.pair, `NKU.header_frame, `NKU_Success.bind])
    else if mode == "proof11" then
      (#[`NKU_COMBINED_IMPORT], #[`NKU_Success.pure, `NKU_Success.reject, `NKU_Tail.guard_reject, `NKU_TailSource.source, `NKU_TerminalCut.pair, `NKU_Validator.frame, `NKU_Weights.frame, `NKU_ZClaim.source_eq_run])
    else if mode == "proof12" then
      (#[`NKU_COMBINED_IMPORT], #[`NKU_ZClaim.frame, `NKU_ZJoin.source, `AspisR1.RPx_Deployed.deployed])
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
