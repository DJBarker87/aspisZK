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
      (#[`NIY_COMBINED_IMPORT], #[`NIY_FirstRawCut.fresh_source, `NIY_FirstECut.source, `NIY_RawTransport.raw, `NIY_RawTransport.first3, `NIY_AfterKappa.source, `NIY_CohortRawCut.source, `NIY_AfterAlpha0.source, `NIY_AfterAlpha1.source, `NIY_AfterRho.source, `NIY_QueryRead.assoc, `NIY_QueryRead.prod_bind, `NIY_QueryRead.ok_bind, `NIY_QueryRead.continuation, `NIY_QueryCut.source, `NIY_ValidationCut.source, `NIY_SemanticCut.source, `NIY_AfterZ0x.source, `NIY_AfterZ0y.source, `NIY_AfterZ1x.source, `NIY_AfterZ1y.source])
    else if mode == "proof1" then
      (#[`NIY_COMBINED_IMPORT], #[`NIY_AfterClaim.source, `NIY_AfterRhs.source, `NIY_AfterPower.source, `NIY_AllocationCut.source, `NIY_FinalCut.source, `NIY_C_FirstECut.source, `NIY_C_AfterKappa.source, `NIY_C_AfterAlpha0.source, `NIY_C_AfterAlpha1.source, `NIY_C_AfterRho.source, `NIY_C_QueryCut.source, `NIY_C_ValidationCut.source, `NIY_C_SemanticCut.source, `NIY_C_AfterZ0x.source, `NIY_C_AfterZ0y.source, `NIY_C_AfterZ1x.source, `NIY_C_AfterZ1y.source, `NIY_C_AfterClaim.source, `NIY_C_AfterRhs.source, `NIY_C_AfterPower.source])
    else if mode == "proof2" then
      (#[`NIY_COMBINED_IMPORT], #[`NIY_C_AllocationCut.source, `NIY_C_FinalCut.source, `NIY_FinalPort.source, `NIY_SectionBind.sectionReply, `NIY_SectionBind.reverse_port, `NIY_SectionBind.forwardReply, `NIY_WeightsPort.source, `NIY_AllocationPort.source, `NIY_PowerReadPort.source, `NIY_RhsReadPort.source, `NIY_ClaimReadPort.source, `NIY_Z1yReadPort.source, `NIY_Z1xReadPort.source, `NIY_Z0yReadPort.source, `NIY_Z0xReadPort.source, `NIY_SemanticPort.source, `NIY_ValidationPort.source, `NIY_QueryTransport.continuation, `NIY_QueryPort.source, `NIY_RhoReadPort.source])
    else if mode == "proof3" then
      (#[`NIY_COMBINED_IMPORT], #[`NIY_Alpha1ReadPort.source, `NIY_Alpha0ReadPort.source, `NIY_KappaReadPort.source, `NIY_GammaReadPort.source, `NIY_TailPort.source, `NIY_ResumePort.source, `NIY_WeightFrame.scalar_ext, `NIY_WeightFrame.k_ext, `NIY_WeightFrame.payload, `NIY_WeightFrame.capacity_prefix, `NIY_WeightFrame.capacity_to_final, `NIY_ScanCuts.step_ok, `NIY_ScanCuts.prefix_ok, `NIY_ResumeFields.fields, `NIY_ResumeFields.reservation, `NIY_ReaderFrames.raw, `NIY_ReaderFrames.e, `NIY_EarlyDomains.first3, `NIY_EarlyDomains.typed, `NIY_NativeCuts.firstByte])
    else if mode == "proof4" then
      (#[`NIY_COMBINED_IMPORT], #[`NIY_NativeCuts.firstCursor, `NIY_NativeCuts.eReply, `NIY_NativeCuts.kReply, `NIY_NativeCuts.eValue, `NIY_NativeCuts.kValue, `NIY_NativeCuts.descriptor, `NIY_NativeCuts.eCursor, `NIY_NativeCuts.kCursor, `NIY_NativeFinalCuts.windowPre, `NIY_NativeFinalCuts.windowCut, `NIY_NativeFinalCuts.reserveCut, `NIY_NativeFinalCuts.weightPre, `NIY_NativeFinalCuts.weightCut, `NIY_ScanCuts.prefixCut, `NIY_ScanCuts.m31Cut, `NIY_ScanCuts.openingCut, `AspisR1.RPx_Deployed.deployed])
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
