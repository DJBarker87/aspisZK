import Lean
import NFA_WALKER
import NFA_MemoryLimit
open Lean Elab Command
namespace NER
/-- Include recursor reduction rules and constant-name metadata, not only values. -/
def referenceNames (c : ConstantInfo) : Array Name := Id.run do
 let mut refs := c.type.getUsedConstants ++ ((c.value? true).map Expr.getUsedConstants).getD #[]
 match c with
 | .defnInfo v => refs := refs ++ v.all.toArray
 | .thmInfo v => refs := refs ++ v.all.toArray
 | .opaqueInfo v => refs := refs ++ v.all.toArray
 | .inductInfo v => refs := refs ++ v.ctors.toArray ++ v.all.toArray
 | .ctorInfo v => refs := refs.push v.induct
 | .recInfo v =>
  refs := refs ++ v.all.toArray
  for rule in v.rules do refs := refs.push rule.ctor ++ rule.rhs.getUsedConstants
 | _ => pure ()
 return refs
/-- Same stable first-occurrence projection as NER_ModuleTables.inspect. -/
def canonicalImports (xs : Array String) : Array String := Id.run do
 let mut result := #[]
 for x in xs do
  if !result.contains x then result := result.push x
 return result
def importsMatch (actual expected : Array String) : Bool := canonicalImports actual == expected
/-- Inspect each module's own declarations against the checked private environment. -/
def loadedScan (env : Environment) (output : System.FilePath)
    (expected : Std.HashMap String (Array String)) : IO Bool := do
 let env := env.setExporting false
 let out ← IO.FS.Handle.mk output .write
 let mut failed := false
 for h : idx in [0:env.header.moduleNames.size] do
  let n := env.header.moduleNames[idx]
  let data := env.header.moduleData[idx]!
  let mut dangling : Array Json := #[]
  let mut edges := 0
  for declared in data.constants do
   let some c := env.checked.get.find? declared.name | do
    dangling := dangling.push (Json.mkObj [("parent",toJson declared.name.toString),("missing",toJson declared.name.toString),("phase",toJson "own_declaration")])
    continue
   let refs := referenceNames c
   for dep in refs do
    edges := edges + 1
    if (env.checked.get.find? dep).isNone then
     dangling := dangling.push (Json.mkObj [("parent",toJson c.name.toString),("missing",toJson dep.toString)])
  let loaderImports := data.imports.map (fun i => i.module.toString)
  let imports := canonicalImports loaderImports
  let importMatch := match expected[n.toString]? with
   | some baseline => imports == baseline
   | none => false
  if !dangling.isEmpty || !importMatch then failed := true
  out.putStrLn (Json.mkObj [("module",toJson n.toString), ("imports",toJson imports),
   ("loader_imports",toJson loaderImports), ("imports_match",toJson importMatch), ("dangling",toJson dangling),
   ("declarations",toJson data.constants.size), ("edges",toJson edges)]).compress
 return failed
end NER

/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  NFA_MemoryLimit.set
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    if mode == "proof0" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NCA_SerializerWindow.frame, `AspisR1.NCA_SerializerWindow.induction, `AspisR1.NFE_DotBridge.one, `AspisR1.NFE_WrapperBridge.four])
    else if mode == "proof1" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFF_BaseMultiply.product_bound, `AspisR1.NFF_BaseMultiply.source, `AspisR1.NFF_BaseMultiply.word_product, `AspisR1.NFF_Cell.primitive_reply])
    else if mode == "proof2" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFF_Cell.replay, `AspisR1.NFF_CoreReduction.same, `AspisR1.NFF_CoreReduction.source, `AspisR1.NFF_FullOne.replay])
    else if mode == "proof3" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFF_FullWrapper.headline, `AspisR1.NFF_FullWrapper.replay, `AspisR1.NFF_LoggedDomains.four, `AspisR1.NFF_LoggedDomains.one])
    else if mode == "proof4" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFF_LoggedEight.cell_replay, `AspisR1.NFF_LoggedEight.replay, `AspisR1.NFF_LoggedLoop.replay, `AspisR1.NFF_LoggedOne.replay])
    else if mode == "proof5" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFF_LoggedOuterLoop.replay, `AspisR1.NFF_LoggedOuterStep.active, `AspisR1.NFF_LoggedOuterStep.stopped, `AspisR1.NFF_LoggedPush.private_replay])
    else if mode == "proof6" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFF_LoggedPush.public_replay, `AspisR1.NFF_LoggedRaw.headline, `AspisR1.NFF_LoggedRaw.replay, `AspisR1.NFF_LoggedStep.active])
    else if mode == "proof7" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFF_LoggedStep.update_replay, `AspisR1.NFF_LoggedTail.replay, `AspisR1.NFF_LoggedWrapper.headline, `AspisR1.NFF_LoggedWrapper.replay])
    else if mode == "proof8" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFF_ProductCall.replay, `AspisR1.NFF_QueryProduct.emitted, `AspisR1.NFF_RawLog.natural, `AspisR1.NFF_RawLog.replay])
    else if mode == "proof9" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFF_RawLog.same_log, `AspisR1.NFF_RawTypedLog.canonical, `AspisR1.NFF_RawTypedLog.operands, `AspisR1.NFF_RawTypedLog.replay])
    else if mode == "proof10" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFF_ReadDomains.canonical, `AspisR1.NFF_ReadDomains.selected, `AspisR1.NFG_ProductOk.result, `AspisR1.NFG_PushRoot.private_domains])
    else if mode == "proof11" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFG_PushRoot.private_result, `AspisR1.NFG_PushRoot.public_result, `AspisR1.NFG_QueryLoopSource.complete, `AspisR1.NFG_SmallEffects.neg])
    else if mode == "proof12" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFG_SmallEffects.zero, `AspisR1.NFI_FailurePrefixes.rejected, `AspisR1.NFI_FailurePrefixes.trace_prefix, `AspisR1.NFI_InnerActual.borrowed_frame])
    else if mode == "proof13" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFI_InnerActual.canonical_at_cut, `AspisR1.NFI_InnerActual.emitted, `AspisR1.NFI_InnerCut.erased, `AspisR1.NFI_InnerCut.same_input])
    else if mode == "proof14" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFI_InnerTrace.frames, `AspisR1.NFI_InnerTrace.replay, `AspisR1.NFI_OpeningFrame.arbitrary_complement, `AspisR1.NFI_OpeningFrame.original_byte])
    else if mode == "proof15" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFI_OpeningFrame.receiver_and_return_frame, `AspisR1.NFI_OpeningFrame.same_heap_frame, `AspisR1.NFI_OuterActual.emitted, `AspisR1.NFI_OuterCut.erased])
    else if mode == "proof16" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFI_OuterCut.same_input, `AspisR1.NFI_OuterTrace.frames, `AspisR1.NFI_OuterTrace.replay, `AspisR1.NFI_PrivateCuts.installed])
    else if mode == "proof17" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFI_SingleDomains.reached, `AspisR1.NFI_SingleTrace.emitted, `AspisR1.NFI_SingleTrace.erased, `AspisR1.NFI_SingleTrace.main_erased])
    else if mode == "proof18" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFI_TailTrace.emitted, `AspisR1.NFI_TailTrace.erased, `AspisR1.NFI_TraceResult.div_prefix, `AspisR1.NFI_TraceResult.erase_bind])
    else if mode == "proof19" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFI_TraceResult.erase_lift, `AspisR1.NFI_TraceResult.erase_mark, `AspisR1.NFI_TraceResult.erase_pure, `AspisR1.NFI_TraceResult.fail_prefix])
    else if mode == "proof20" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFI_WrapperDomains.reached, `AspisR1.NFI_WrapperTrace.erased, `AspisR1.NFI_WrapperTrace.headline, `AspisR1.NFM_CallDomains.tail_counts])
    else if mode == "proof21" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFM_CallDomains.terminal, `AspisR1.NFM_Control.body_at, `AspisR1.NFM_Control.fixed_outer, `AspisR1.NFM_Control.fixed_terms])
    else if mode == "proof22" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFM_Control.next0, `AspisR1.NFM_Control.next1, `AspisR1.NFM_Control.next2, `AspisR1.NFM_Control.next3])
    else if mode == "proof23" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFM_Control.next4, `AspisR1.NFM_Control.next5, `AspisR1.NFM_Control.next6, `AspisR1.NFM_Control.next_at])
    else if mode == "proof24" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFM_Control.state_sequence, `AspisR1.NFM_Control.stopped, `AspisR1.NFM_Control.term_count, `AspisR1.NFM_Cuts.abort_prefix])
    else if mode == "proof25" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFM_Cuts.erased, `AspisR1.NFM_Cuts.main, `AspisR1.NFM_Cuts.window_erased, `AspisR1.NFM_Domains.limb_cap])
    else if mode == "proof26" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFM_Domains.slots, `AspisR1.NFM_Domains.sums_reset, `AspisR1.NFM_Frames.sequence, `AspisR1.NFM_Frames.window])
    else if mode == "proof27" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFM_InnerControl.active, `AspisR1.NFM_InnerControl.at_cut, `AspisR1.NFM_InnerControl.complete, `AspisR1.NFM_ProductInstance.installed])
    else if mode == "proof28" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFM_ProductInstance.main_law, `AspisR1.NFM_ProductInstance.tail_law, `AspisR1.NFM_ProductInstance.wrapper, `AspisR1.NFM_Single.domains])
    else if mode == "proof29" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFM_Single.emitted, `AspisR1.NFM_Single.main_same, `AspisR1.NFM_Single.same, `AspisR1.NFM_Span.scalar])
    else if mode == "proof30" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFM_Span.tail, `AspisR1.NFM_Span.window, `AspisR1.NFM_Thread.advance, `AspisR1.NFM_Thread.advance0])
    else if mode == "proof31" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFM_Thread.advance1, `AspisR1.NFM_Thread.advance2, `AspisR1.NFM_Thread.advance3, `AspisR1.NFM_Thread.advance4])
    else if mode == "proof32" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFM_Thread.advance5, `AspisR1.NFM_Thread.advance6, `AspisR1.NFM_Thread.body, `AspisR1.NFM_Thread.main])
    else if mode == "proof33" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFP_Advance.accepted, `AspisR1.NFP_Carrier.canonical, `AspisR1.NFP_Carrier.from_to, `AspisR1.NFP_Carrier.to_from])
    else if mode == "proof34" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFP_Carrier.words, `AspisR1.NFP_DotCaller.query, `AspisR1.NFP_DotCaller.tail, `AspisR1.NFP_DotDomains.returned])
    else if mode == "proof35" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFP_DotInstall.dot_result, `AspisR1.NFP_DotInstall.head, `AspisR1.NFP_FrameExt.raw, `AspisR1.NFP_GeometryDomains.reads])
    else if mode == "proof36" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFP_HeadDomain.reached, `AspisR1.NFP_LoopBudget.maximum, `AspisR1.NFP_LoopBudget.tx1, `AspisR1.NFP_LoopBudget.tx2])
    else if mode == "proof37" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFP_LoopTerminals.diverged, `AspisR1.NFP_LoopTerminals.error, `AspisR1.NFP_LoopTerminals.failed, `AspisR1.NFP_LoopTerminals.rejected])
    else if mode == "proof38" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFP_LoopTerminals.stopped, `AspisR1.NFP_LoopTransport.child, `AspisR1.NFP_LoopTransport.complete, `AspisR1.NFP_NatBase.add])
    else if mode == "proof39" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFP_NatBase.sub, `AspisR1.NFP_NatBase.sub_word, `AspisR1.NFP_NodeDictionary.add, `AspisR1.NFP_NodeDictionary.node])
    else if mode == "proof40" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFP_NodeDictionary.product, `AspisR1.NFP_NodeDictionary.sub, `AspisR1.NFP_ObserverErasure.phase, `AspisR1.NFP_ObserverErasure.query])
    else if mode == "proof41" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFP_ObserverErasure.trace, `AspisR1.NFP_ProductLaw.emitted, `AspisR1.NFP_ProductLaw.node, `AspisR1.NFP_QueryAdvance.accepted])
    else if mode == "proof42" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFP_QueryAdvance.offset, `AspisR1.NFP_QueryCuts.source, `AspisR1.NFP_QueryTrace.erased, `AspisR1.NFP_RejectionTrace.guard])
    else if mode == "proof43" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFP_RejectionTrace.rejected_prefix, `AspisR1.NFP_Resume.tx1, `AspisR1.NFP_Resume.tx2, `AspisR1.NFP_ReturnCuts.continuation])
    else if mode == "proof44" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFP_ReturnCuts.erased, `AspisR1.NFP_SuffixCuts.source, `AspisR1.NFP_TraceBack.erased, `AspisR1.NFP_TraceFront.erased])
    else if mode == "proof45" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFP_TraceHead.erased, `AspisR1.NFP_TraceTypes.pure_result, `AspisR1.NFS_AccumDomain.domain, `AspisR1.NFS_AccumDomain.line])
    else if mode == "proof46" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFS_AccumInstall.installed, `AspisR1.NFS_CallerDomains.array_property, `AspisR1.NFS_CallerDomains.dots, `AspisR1.NFS_CallerDomains.fields])
    else if mode == "proof47" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFS_CallerDomains.folds, `AspisR1.NFS_CallerDomains.loop_property, `AspisR1.NFS_CallerDomains.no_seed, `AspisR1.NFS_DotTrace.head])
    else if mode == "proof48" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFS_FoldInstall.circle, `AspisR1.NFS_FoldInstall.domains, `AspisR1.NFS_FoldInstall.line, `AspisR1.NFS_FoldInstall.map_map])
    else if mode == "proof49" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFS_FoldInstall.rows, `AspisR1.NFS_LoopTrace.erase_fixed, `AspisR1.NFS_LoopTrace.source, `AspisR1.NFS_LoopTraceDefs.bind_congr])
    else if mode == "proof50" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFS_LoopTraceDefs.compare, `AspisR1.NFS_LoopTraceDefs.erased, `AspisR1.NFS_PacketRoot.geometry, `AspisR1.NFS_PacketRoot.loop])
    else if mode == "proof51" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFS_PacketRoot.node, `AspisR1.NFS_PacketRoot.query, `AspisR1.NFS_QueryBack.installed, `AspisR1.NFS_QueryInvariant.active])
    else if mode == "proof52" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFS_QueryInvariant.form, `AspisR1.NFS_QueryInvariant.step, `AspisR1.NFS_QueryLoopRoot.finite, `AspisR1.NFS_QueryLoopRoot.root])
    else if mode == "proof53" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFS_QueryLoopRoot.tx1, `AspisR1.NFS_QueryLoopRoot.tx2, `AspisR1.NFS_QueryOps.accumulation, `AspisR1.NFS_QueryOps.line])
    else if mode == "proof54" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFS_QueryValuesPacket.result, `AspisR1.NFS_QueryValuesPacket.source, `AspisR1.NFS_ReadCanonical.bytes, `AspisR1.NFS_ReadCanonical.field])
    else if mode == "proof55" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFS_ReadCanonical.limbs, `AspisR1.NFS_ReadCanonical.read_canonical, `AspisR1.NFS_TraceBack.eval_bind, `AspisR1.NFS_TraceBack.installed])
    else if mode == "proof56" then
      (#[`NFX_COMBINED_IMPORT], #[`AspisR1.NFS_TraceBack.model_congr, `AspisR1.NFS_TraceBack.source, `AspisR1.RPx_Deployed.deployed, `NEM_ValidatorComposed.result_state_effects])
    else if mode == "proof57" then
      (#[`NFX_COMBINED_IMPORT], #[`NEQ_EncoderOracle.result_state_effects, `NEU_CallDomains.common_packet, `NEU_CallDomains.reached_domains, `NEU_CallDomains.transfer_packet])
    else if mode == "proof58" then
      (#[`NFX_COMBINED_IMPORT], #[`NEU_CallDomains.transfer_reply_range, `NEU_CallDomains.withdrawal_packet, `NEU_CallDomains.withdrawal_reply_range, `NEU_CommonProjections.common_ext])
    else if mode == "proof59" then
      (#[`NFX_COMBINED_IMPORT], #[`NEU_EqualityLoop.prefix_exact, `NEU_EqualityLoop.step_invariant, `NEU_ReconstructAdopted.result_state_effects, `NEU_ReconstructCore.common_result])
    else if mode == "proof60" then
      (#[`NFX_COMBINED_IMPORT], #[`NEU_ReconstructCore.result_state_effects, `NEX_PublicModel.result_state_effects, `NEY_EmitComposed.encoder_bridge, `NEY_EmitComposed.reached_encoder])
    else if mode == "proof61" then
      (#[`NFX_COMBINED_IMPORT], #[`NEY_EmitComposed.result_state_effects, `NFD_CommonField00.alignment, `NFD_CommonField01.alignment, `NFD_CommonField02.alignment])
    else if mode == "proof62" then
      (#[`NFX_COMBINED_IMPORT], #[`NFD_CommonField03.alignment, `NFD_CommonField04.alignment, `NFD_CommonField05.alignment, `NFD_CommonField06.alignment])
    else if mode == "proof63" then
      (#[`NFX_COMBINED_IMPORT], #[`NFD_CommonField07.alignment, `NFD_CommonField08.alignment, `NFD_CommonField09.alignment, `NFD_CommonField10.alignment])
    else if mode == "proof64" then
      (#[`NFX_COMBINED_IMPORT], #[`NFD_CommonField11.alignment, `NFD_CommonField12.alignment, `NFD_CommonField13.alignment, `NFD_CommonField14.alignment])
    else if mode == "proof65" then
      (#[`NFX_COMBINED_IMPORT], #[`NFD_EmitProjection.alignment0, `NFD_EmitProjection.alignment1, `NFD_EmitProjection.alignment2, `NFD_EmitProjection.alignment3])
    else if mode == "proof66" then
      (#[`NFX_COMBINED_IMPORT], #[`NFD_EmitProjection.alignment4, `NFD_EmitProjection.alignment5, `NFD_EmitProjection.alignment6, `NFD_EmitProjection.alignment7])
    else if mode == "proof67" then
      (#[`NFX_COMBINED_IMPORT], #[`NFD_EmitProjection.complete, `NFD_RawCarriers.limbs_result_state_effects, `NFD_RawCarriers.raw_roundtrip, `NFD_RawCarriers.tag_result_state_effects])
    else if mode == "proof68" then
      (#[`NFX_COMBINED_IMPORT], #[`NFD_RawCarriers.tag_roundtrip, `NFD_RequestDomains.binding_fields, `NFD_RequestDomains.payment_length, `NFD_RequestDomains.payment_window])
    else if mode == "proof69" then
      (#[`NFX_COMBINED_IMPORT], #[`NFD_RequestDomains.wrong_length, `NFD_RequestField00.alignment, `NFD_RequestField01.alignment, `NFD_RequestField02.alignment])
    else if mode == "proof70" then
      (#[`NFX_COMBINED_IMPORT], #[`NFD_RequestField03.alignment, `NFD_RequestField04.alignment, `NFD_RequestField05.alignment, `NFD_RequestField06.alignment])
    else if mode == "proof71" then
      (#[`NFX_COMBINED_IMPORT], #[`NFD_RequestField07.alignment, `NFD_RequestField08.alignment, `NFD_RequestField09.alignment, `NFD_RequestField10.alignment])
    else if mode == "proof72" then
      (#[`NFX_COMBINED_IMPORT], #[`NFD_RequestField11.alignment, `NFD_RequestField12.alignment, `NFD_RequestField13.alignment, `NFD_RequestOracle.array_result_state_effects])
    else if mode == "proof73" then
      (#[`NFX_COMBINED_IMPORT], #[`NFD_RequestOracle.result_state_effects, `NFD_RequestProjection.complete, `NFD_RequestProjection.transfer_roundtrip, `NFD_RequestProjection.withdrawal_roundtrip])
    else if mode == "proof74" then
      (#[`NFX_COMBINED_IMPORT], #[`NFD_ScanConditional.result_state_effects, `NFD_WideSerialization.carrier_roundtrip, `NFD_WideSerialization.result_state_effects, `NFG_InversePanic.zero])
    else if mode == "proof75" then
      (#[`NFX_COMBINED_IMPORT], #[`NFG_InverseZeroDomain.unique, `NFH_ComparisonBoundary.opaque_reply_insufficient, `NFH_ComparisonBoundary.reply_eq_loop, `NFH_ComparisonBoundary.zeroLaw_necessary])
    else if mode == "proof76" then
      (#[`NFX_COMBINED_IMPORT], #[`NFH_ComparisonDomain.complete688_association, `NFH_ComparisonDomain.complete688_on_domain, `NFJ_Comparison.completion, `NFJ_Comparison.header_length])
    else if mode == "proof77" then
      (#[`NFX_COMBINED_IMPORT], #[`NFJ_Comparison.nativeEqualityBridge, `NFJ_Comparison.same_buffer_lengths, `NFJ_Comparison.slot_zero_iff, `NFJ_Scanner.decode_domain])
    else if mode == "proof78" then
      (#[`NFX_COMBINED_IMPORT], #[`NFJ_Scanner.encode_domain, `NFJ_Scanner.result_state_effects, `NFJ_Scanner.tag_domain, `NFN_NEW_GeometryComplete.complete])
    else if mode == "proof79" then
      (#[`NFX_COMBINED_IMPORT], #[`NFN_NFB_GeometryComposed.accepted_physical, `NFN_NFB_GeometryComposed.result_state_effects, `NFN_NFB_GeometryInstall.loop, `NFN_NFB_GeometryInstall.standard])
    else if mode == "proof80" then
      (#[`NFX_COMBINED_IMPORT], #[`NFN_NFB_GeometryInstall.step, `NFN_PhaseTransport.legacy_roundtrip, `NFN_PhaseTransport.observer_none, `NFN_PhaseTransport.observer_some])
    else if mode == "proof81" then
      (#[`NFX_COMBINED_IMPORT], #[`NFN_PhaseTransport.owner_roundtrip, `NFN_ReserveOwner.error_owner, `NFQ_FieldLaws.cm_reference, `NFQ_FieldLaws.neg_value])
    else if mode == "proof82" then
      (#[`NFX_COMBINED_IMPORT], #[`NFQ_FieldLaws.qm_reference, `NFQ_PreparedMultiplier.source, `NFQ_Readonly.reference, `NFQ_Reduce.source])
    else if mode == "proof83" then
      (#[`NFX_COMBINED_IMPORT], #[`NFQ_RowShape.compact_reference, `NFQ_RowShape.reference, `NFQ_StatementLaws.copied_reference, `NFQ_StatementLaws.expected_reference])
    else if mode == "proof84" then
      (#[`NFX_COMBINED_IMPORT], #[`NFQ_StatementLaws.limbs_reference, `NFQ_Transport.checkpoint_size_reference, `NFQ_Transport.final_len_reference, `NFQ_Transport.folds_reference])
    else if mode == "proof85" then
      (#[`NFX_COMBINED_IMPORT], #[`NFQ_WideGetters.c0, `NFQ_WideGetters.c1, `NFS_NEV_AccumPacket.no_base_dependency, `NFS_NEV_AccumPacket.raw_length])
    else if mode == "proof86" then
      (#[`NFX_COMBINED_IMPORT], #[`NFS_NEV_AccumPacket.result_state_effects, `NFS_NEV_AccumulateComplete.native, `NFS_NEV_AccumulateComplete.reference])
    else if mode == "fixtures" then
      (#[`NEP_Planted, `NEP_Mutations],
       #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
         `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
         `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
    else (#[], #[])
  let env ← importModules (modules.map fun n => ({module := n, importAll := true} : Import))
    {} (loadExts := true) (level := .private)
  if mode == "scan" || mode == "queryscan" then
    let mut expected : Std.HashMap String (Array String) := {}
    for line in ← IO.FS.lines (if mode == "queryscan" then "NFN_QUERY_EXPECTED_IMPORTS.jsonl" else "NFN_EXPECTED_IMPORTS.jsonl") do
      let j ← IO.ofExcept (Json.parse line)
      expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
        (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
    let failed ← NER.loadedScan env (if mode == "queryscan" then "NFN_QUERY_LOADED_scan.jsonl" else "NFN_LOADED_scan.jsonl") expected
    IO.println (if failed then "NFN_SCAN_FAILED" else "NFN_SCAN_ZERO_DANGLING")
    return if failed then 1 else 0
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
