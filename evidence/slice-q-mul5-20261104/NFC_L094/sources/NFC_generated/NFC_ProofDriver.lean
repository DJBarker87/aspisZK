import Lean
import NFA_MemoryLimit
import NFA_WALKER
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  NFA_MemoryLimit.set
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    if mode == "proof0" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_AddDomain.cm, `AspisR1.NFC_LaterJoin.association])
    else if mode == "proof1" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_AddDomain.qm, `AspisR1.NFC_LaterSource.cut])
    else if mode == "proof2" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_AddDomain.total, `AspisR1.NFC_LaterSource.domains])
    else if mode == "proof3" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_AddDomain.canonical, `AspisR1.NFC_MainPacket.of_run])
    else if mode == "proof4" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_ArrayFour.shape, `AspisR1.NFC_MainPacket.replay])
    else if mode == "proof5" then
      (#[`NFC_FinalAudit], #[`NFC_CalleeDomains.private_canon, `AspisR1.NFC_MainPacket.domains])
    else if mode == "proof6" then
      (#[`NFC_FinalAudit], #[`NFC_CalleeDomains.from_wide, `NFC_OpeningFrame.geometry])
    else if mode == "proof7" then
      (#[`NFC_FinalAudit], #[`NFC_CalleeDomains.from_limbs, `NFC_OpeningFrame.frame])
    else if mode == "proof8" then
      (#[`NFC_FinalAudit], #[`NFC_CalleeDomains.checked, `AspisR1.NFC_PacketDomains.counts])
    else if mode == "proof9" then
      (#[`NFC_FinalAudit], #[`NFC_CalleeDomains.value, `AspisR1.NFC_PacketDomains.inputs])
    else if mode == "proof10" then
      (#[`NFC_FinalAudit], #[`NFC_CalleeDomains.scalar, `AspisR1.NFC_PacketDomains.finish])
    else if mode == "proof11" then
      (#[`NFC_FinalAudit], #[`NFC_CalleeDomains.total, `AspisR1.NFC_PacketDomains.native_counts])
    else if mode == "proof12" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_ChainAssociation.actual, `AspisR1.NFC_PushCut.actual])
    else if mode == "proof13" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_ChainAssociation.finish, `AspisR1.NFC_PushCut.count])
    else if mode == "proof14" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_ChainAssociation.zero, `AspisR1.NFC_RawAssociation.source_eq])
    else if mode == "proof15" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_CheckedArithmetic.add, `AspisR1.NFC_RawValues.source])
    else if mode == "proof16" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_CheckedArithmetic.mul, `AspisR1.NFC_ReceiverModel.roundtrip])
    else if mode == "proof17" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_DotDomain.accepted, `AspisR1.NFC_ReceiverModel.represents])
    else if mode == "proof18" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_DotPushCut.source, `AspisR1.NFC_ScalarAdd.total])
    else if mode == "proof19" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_DotPushFour.source, `AspisR1.NFC_StepAssociation.exact])
    else if mode == "proof20" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_DotPushStep.source, `AspisR1.NFC_StepAssociation.packet])
    else if mode == "proof21" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_DotPushTotal.source, `AspisR1.NFC_TailAssociation.source])
    else if mode == "proof22" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_DotWordStep.fold_bound, `AspisR1.NFC_TailPacket.of_run])
    else if mode == "proof23" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_DotWordStep.value, `AspisR1.NFC_TailPacket.replay])
    else if mode == "proof24" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_DotWordStep.reduced, `AspisR1.NFC_TailState.new_count])
    else if mode == "proof25" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_FinalCalls.finish, `AspisR1.NFC_TailState.finish_canonical])
    else if mode == "proof26" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_FinalCalls.add, `AspisR1.NFC_TailState.chain])
    else if mode == "proof27" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_FirstGeometry.accepted, `AspisR1.NFC_TailState.accepted])
    else if mode == "proof28" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_FirstJoin.association, `AspisR1.NFC_TailTrace.unwrap_unit])
    else if mode == "proof29" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_FirstSource.cut, `AspisR1.NFC_TailTrace.accepted])
    else if mode == "proof30" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_FirstSource.domains, `AspisR1.NFC_WideCanonical.from_limbs])
    else if mode == "proof31" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_FourDomain.accepted, `AspisR1.NFC_WrapperPacket.accepted])
    else if mode == "proof32" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_HeadDomain.canonical])
    else if mode == "proof33" then
      (#[`NFC_FinalAudit], #[`NFC_KmxFrames.final_region])
    else if mode == "proof34" then
      (#[`NFC_FinalAudit], #[`NFC_KmxFrames.frame])
    else if mode == "proof35" then
      (#[`NFC_FinalAudit], #[`NFC_KmxFrames.source_window])
    else if mode == "proof36" then
      (#[`NFC_FinalAudit], #[`NFC_KmxFrames.output_frame])
    else if mode == "proof37" then
      (#[`NFC_FinalAudit], #[`AspisR1.NFC_LaterGeometry.accepted])
    else if mode == "fixtures" then
      (#[`NEP_Planted, `NEP_Mutations],
       #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
         `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
         `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
    else if mode == "0" then
      (#[`NEV_PrefixAssembly], #[`NEV_PrefixAssembly.windows, `NEV_PrefixAssembly.active])
    else if mode == "1" then
      (#[`NEV_PrefixCapacity], #[`NEV_PrefixCapacity.representative, `NEV_PrefixCapacity.partition])
    else if mode == "2" then
      (#[`NEV_PrefixCallerDomain], #[`NEV_PrefixCallerDomain.gathered, `NEV_PrefixCallerDomain.capacities])
    else if mode == "3" then
      (#[`NEV_PrefixAudit], #[`NEV_PrefixCallerDomain.gathered, `NEV_PrefixCallerDomain.capacities, `NEV_PrefixAssembly.windows, `NEV_PrefixAssembly.active, `NEV_PrefixCapacity.representative, `NEV_PrefixCapacity.partition])
    else if mode == "4" then
      (#[`NEV_PrefixCalls], #[`NEV_PrefixCalls.m31_site, `NEV_PrefixCalls.member, `NEV_PrefixCalls.cases])
    else if mode == "5" then
      (#[`NEV_PrefixFinalAudit], #[`NEV_PrefixCallerDomain.gathered, `NEV_PrefixCallerDomain.capacities, `NEV_PrefixAssembly.windows, `NEV_PrefixAssembly.active, `NEV_PrefixCapacity.representative, `NEV_PrefixCapacity.partition, `NEV_PrefixCalls.m31_site, `NEV_PrefixCalls.member, `NEV_PrefixCalls.cases])
    else if mode == "6" then
      (#[`NEV_PrefixPacket], #[`NEV_PrefixPacket.result_state_effects])
    else if mode == "7" then
      (#[`NEV_CodeFieldBridge], #[`NEV_CodeFieldBridge.raw_roundtrip, `NEV_CodeFieldBridge.stage_roundtrip, `NEV_CodeFieldBridge.rem, `NEV_CodeFieldBridge.total, `NEV_CodeFieldBridge.cohort])
    else if mode == "8" then
      (#[`NEV_CodeFieldUse], #[`NEV_CodeFieldUse.basis_call])
    else if mode == "9" then
      (#[`NEV_CodeFieldPacket], #[`NEV_CodeFieldPacket.extracted_root, `NEV_CodeFieldUse.basis_call])
    else if mode == "10" then
      (#[`NEV_AccumulateCarriers], #[`NEV_AccumulateCarriers.array_inverse, `NEV_AccumulateCarriers.vector_inverse, `NEV_AccumulateCarriers.point_roundtrip, `NEV_AccumulateCarriers.point_reverse, `NEV_AccumulateCarriers.prepared_roundtrip, `NEV_AccumulateCarriers.prepared_reverse, `NEV_AccumulateCarriers.accumulator_roundtrip, `NEV_AccumulateCarriers.accumulator_reverse, `NEV_AccumulateCarriers.q_roundtrip, `NEV_AccumulateCarriers.q_reverse, `NEV_AccumulateCarriers.e_roundtrip, `NEV_AccumulateCarriers.e_reverse, `NEV_AccumulateCarriers.weights_roundtrip, `NEV_AccumulateCarriers.weights_reverse])
    else if mode == "11" then
      (#[`NEV_BasisRaw], #[`NEV_BasisRaw.inner_step, `NEV_BasisRaw.inner_stop, `NEV_BasisRaw.inner_loop])
    else if mode == "12" then
      (#[`NEV_BasisOuterStep], #[`NEV_BasisOuterStep.multiply, `NEV_BasisOuterStep.subtract, `NEV_BasisOuterStep.double, `NEV_BasisOuterStep.body])
    else if mode == "13" then
      (#[`NEV_AccumulateCallees], #[`NEV_AccumulateCallees.native_e_reverse, `NEV_AccumulateCallees.native_q_reverse, `NEV_AccumulateCallees.ctor_e_reverse, `NEV_AccumulateCallees.wide_add, `NEV_AccumulateCallees.wide_product, `NEV_AccumulateCallees.qm_product, `NEV_AccumulateCallees.from_qm, `NEV_AccumulateCallees.push, `NEV_AccumulateCallees.from_m31])
    else if mode == "14" then
      (#[`NEV_BasisOuterRaw], #[`NEV_BasisOuterRaw.levels_eq])
    else if mode == "15" then
      (#[`NEV_AccumulateTail], #[`NEV_AccumulateTail.source_cut, `NEV_AccumulateTail.successful_frame])
    else if mode == "16" then
      (#[`NEV_PushUse], #[`NEV_PushUse.association])
    else if mode == "17" then
      (#[`NEV_BorrowMaps], #[`NEV_BorrowMaps.vector_read, `NEV_BorrowMaps.weight_read])
    else if mode == "18" then
      (#[`NEV_CtorNormalization], #[`NEV_CtorNormalization.total, `NEV_CtorNormalization.reduce_identity, `NEV_CtorNormalization.identity, `NEV_CtorNormalization.cohort])
    else if mode == "19" then
      (#[`NEV_BasisProducer], #[`NEV_BasisProducer.association, `NEV_BasisProducer.total, `NEV_BasisProducer.read_canonical])
    else if mode == "20" then
      (#[`NEV_CtorResults], #[`NEV_CtorResults.m31, `NEV_CtorResults.qm])
    else if mode == "21" then
      (#[`NEV_RowStep], #[`NEV_RowStep.active, `NEV_RowStep.stop])
    else if mode == "22" then
      (#[`NEV_RowLoop], #[`NEV_RowLoop.association])
    else if mode == "23" then
      (#[`NEV_AccumulatePrefix], #[`NEV_AccumulatePrefix.installs_commute, `NEV_AccumulatePrefix.association])
    else if mode == "24" then
      (#[`NEV_MaskCarriers], #[`NEV_MaskCarriers.native_roundtrip, `NEV_MaskCarriers.mask_roundtrip, `NEV_MaskCarriers.canonical, `NEV_MaskCarriers.words, `NEV_MaskCarriers.product_words, `NEV_MaskCarriers.words_injective, `NEV_MaskCarriers.native_injective])
    else if mode == "25" then
      (#[`NEV_MaskQM], #[`NEV_MaskQM.add, `NEV_MaskQM.multiply, `NEV_MaskQM.normalization])
    else if mode == "26" then
      (#[`NEV_StageFields], #[`NEV_StageFields.native_q_roundtrip, `NEV_StageFields.stage_q_roundtrip, `NEV_StageFields.native_e_roundtrip, `NEV_StageFields.stage_e_roundtrip, `NEV_StageFields.canonical_q, `NEV_StageFields.canonical_e, `NEV_StageFields.power])
    else if mode == "27" then
      (#[`NEV_StageWideFields], #[`NEV_StageWideFields.add, `NEV_StageWideFields.product])
    else if mode == "28" then
      (#[`NEV_PrimitiveBindings], #[`NEV_PrimitiveBindings.power, `NEV_PrimitiveBindings.add, `NEV_PrimitiveBindings.product, `NEV_PrimitiveBindings.product_returns])
    else if mode == "29" then
      (#[`NEV_PrimitiveTotal], #[`NEV_PrimitiveTotal.add, `NEV_PrimitiveTotal.power])
    else if mode == "30" then
      (#[`NEV_TailModel], #[`NEV_TailModel.association])
    else if mode == "31" then
      (#[`NEV_AccumulateComplete], #[`NEV_AccumulateComplete.reference_split, `NEV_AccumulateComplete.reference, `NEV_AccumulateComplete.native])
    else if mode == "32" then
      (#[`NEV_PushDomains], #[`NEV_PushDomains.canonical_limb, `NEV_PushDomains.reached])
    else if mode == "33" then
      (#[`NEV_BasisCallDomains], #[`NEV_BasisCallDomains.scalar, `NEV_BasisCallDomains.active_level])
    else if mode == "34" then
      (#[`NEV_WeightDomains], #[`NEV_WeightDomains.read])
    else if mode == "35" then
      (#[`NEV_AccumPacket], #[`NEV_AccumPacket.raw_length, `NEV_AccumPacket.result_state_effects, `NEV_AccumPacket.no_base_dependency])
    else if mode == "36" then
      (#[`NEV_ReachedProgress], #[`NEV_ReachedProgress.next])
    else if mode == "37" then
      (#[`NEV_QRawMaps], #[`NEV_QRawMaps.left, `NEV_QRawMaps.right, `NEV_QRawMaps.shift, `NEV_QRawMaps.fold])
    else if mode == "38" then
      (#[`NEV_QRawAtoms], #[`NEV_QRawAtoms.modulus, `NEV_QRawAtoms.pp, `NEV_QRawAtoms.read0, `NEV_QRawAtoms.read1, `NEV_QRawAtoms.read2, `NEV_QRawAtoms.read3])
    else if mode == "39" then
      (#[`NEV_QRawAssociation], #[`NEV_QRawAssociation.actual, `NEV_QRawAssociation.cohort])
    else if mode == "40" then
      (#[`NEV_DotPush], #[`NEV_DotPush.association, `NEV_DotPush.complete])
    else if mode == "41" then
      (#[`NEV_EbyPushAssociation], #[`NEV_EbyPushAssociation.source])
    else if mode == "42" then
      (#[`NEV_DotScalar], #[`NEV_DotScalar.product])
    else if mode == "43" then
      (#[`NEV_DotResult], #[`NEV_DotResult.inner, `NEV_DotResult.source, `NEV_DotResult.result_state_effects])
    else if mode == "44" then
      (#[`NEV_DotFoldInvariant], #[`NEV_DotFoldInvariant.total, `NEV_DotFoldInvariant.native_domain])
    else if mode == "45" then
      (#[`NEV_ActualDotStep], #[`AspisR1.NEV_ActualDotStep.body])
    else if mode == "46" then
      (#[`NEV_DotCell], #[`NEV_DotCell.total])
    else if mode == "47" then
      (#[`NEV_DotEight], #[`NEV_DotEight.suffix])
    else if mode == "48" then
      (#[`NEV_DotSweep], #[`NEV_DotSweep.write, `NEV_DotSweep.current, `NEV_DotSweep.native_domain])
    else if mode == "49" then
      (#[`NEV_DotSweepStep], #[`NEV_DotSweepStep.step, `NEV_DotSweepStep.next_term])
    else if mode == "50" then
      (#[`NEV_DotReadDomain], #[`NEV_DotReadDomain.scalar, `NEV_DotReadDomain.reached])
    else if mode == "51" then
      (#[`NEV_DotInputs], #[`NEV_DotInputs.selected, `NEV_DotInputs.limbs, `NEV_DotInputs.tail_index])
    else if mode == "52" then
      (#[`NEV_DotEightTotal], #[`NEV_DotEightTotal.eight, `NEV_DotEightTotal.zero, `NEV_DotEightTotal.suffix])
    else if mode == "53" then
      (#[`NEV_DotSchedule], #[`NEV_DotSchedule.block, `NEV_DotSchedule.reached, `NEV_DotSchedule.unique_block, `NEV_DotSchedule.remaining, `NEV_DotSchedule.adjacent, `NEV_DotSchedule.advance_mathematics, `NEV_DotSchedule.finished])
    else if mode == "54" then
      (#[`NEV_FourResult], #[`NEV_FourResult.source, `NEV_FourResult.result_state_effects, `NEV_FourResult.calls])
    else if mode == "55" then
      (#[`NEV_DotResult], #[`NEV_DotResult.inner])
    else if mode == "56" then
      (#[`NEV_DotResult], #[`NEV_DotResult.source])
    else if mode == "57" then
      (#[`NEV_DotResult], #[`NEV_DotResult.result_state_effects])
    else (#[], #[])
  if modules.isEmpty then
    IO.eprintln "Unknown NFA audit mode"
    return 3
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
