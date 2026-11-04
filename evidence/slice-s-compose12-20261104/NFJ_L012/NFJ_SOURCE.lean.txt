import Lean
import NFJ_WALKER
import NFJ_MemoryLimit
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  NFJ_MemoryLimit.set
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) := if mode == "final" then
    (#[`NFD_FinalAudit, `NFH_FinalAudit, `NFJ_Scanner],
     #[`AspisR1.NCA_SerializerWindow.frame, `AspisR1.NCA_SerializerWindow.induction, `NEM_ValidatorComposed.result_state_effects, `NEQ_EncoderOracle.result_state_effects, `NEU_CallDomains.common_packet, `NEU_CallDomains.reached_domains, `NEU_CallDomains.transfer_packet, `NEU_CallDomains.transfer_reply_range, `NEU_CallDomains.withdrawal_packet, `NEU_CallDomains.withdrawal_reply_range, `NEU_CommonProjections.common_ext, `NEU_EqualityLoop.prefix_exact, `NEU_EqualityLoop.step_invariant, `NEU_ReconstructAdopted.result_state_effects, `NEU_ReconstructCore.common_result, `NEU_ReconstructCore.result_state_effects, `NEX_PublicModel.result_state_effects, `NEY_EmitComposed.encoder_bridge, `NEY_EmitComposed.reached_encoder, `NEY_EmitComposed.result_state_effects, `NFD_CommonField00.alignment, `NFD_CommonField01.alignment, `NFD_CommonField02.alignment, `NFD_CommonField03.alignment, `NFD_CommonField04.alignment, `NFD_CommonField05.alignment, `NFD_CommonField06.alignment, `NFD_CommonField07.alignment, `NFD_CommonField08.alignment, `NFD_CommonField09.alignment, `NFD_CommonField10.alignment, `NFD_CommonField11.alignment, `NFD_CommonField12.alignment, `NFD_CommonField13.alignment, `NFD_CommonField14.alignment, `NFD_EmitProjection.alignment0, `NFD_EmitProjection.alignment1, `NFD_EmitProjection.alignment2, `NFD_EmitProjection.alignment3, `NFD_EmitProjection.alignment4, `NFD_EmitProjection.alignment5, `NFD_EmitProjection.alignment6, `NFD_EmitProjection.alignment7, `NFD_EmitProjection.complete, `NFD_RawCarriers.limbs_result_state_effects, `NFD_RawCarriers.raw_roundtrip, `NFD_RawCarriers.tag_result_state_effects, `NFD_RawCarriers.tag_roundtrip, `NFD_RequestDomains.binding_fields, `NFD_RequestDomains.payment_length, `NFD_RequestDomains.payment_window, `NFD_RequestDomains.wrong_length, `NFD_RequestField00.alignment, `NFD_RequestField01.alignment, `NFD_RequestField02.alignment, `NFD_RequestField03.alignment, `NFD_RequestField04.alignment, `NFD_RequestField05.alignment, `NFD_RequestField06.alignment, `NFD_RequestField07.alignment, `NFD_RequestField08.alignment, `NFD_RequestField09.alignment, `NFD_RequestField10.alignment, `NFD_RequestField11.alignment, `NFD_RequestField12.alignment, `NFD_RequestField13.alignment, `NFD_RequestOracle.array_result_state_effects, `NFD_RequestOracle.result_state_effects, `NFD_RequestProjection.complete, `NFD_RequestProjection.transfer_roundtrip, `NFD_RequestProjection.withdrawal_roundtrip, `NFD_ScanConditional.result_state_effects, `NFD_WideSerialization.carrier_roundtrip, `NFD_WideSerialization.result_state_effects, `NFJ_Comparison.header_length, `NFJ_Comparison.same_buffer_lengths, `NFJ_Comparison.nativeEqualityBridge, `NFJ_Comparison.slot_zero_iff, `NFJ_Comparison.completion, `NFJ_Scanner.result_state_effects, `NFJ_Scanner.encode_domain, `NFJ_Scanner.decode_domain, `NFJ_Scanner.tag_domain, `NFH_ComparisonBoundary.reply_eq_loop, `NFH_ComparisonBoundary.zeroLaw_necessary, `NFH_ComparisonBoundary.opaque_reply_insufficient, `NFH_ComparisonDomain.complete688_on_domain, `NFH_ComparisonDomain.complete688_association])
    else if mode == "fixtures" then
    (#[`NEP_Planted, `NEP_Mutations],
     #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
       `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
       `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
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
