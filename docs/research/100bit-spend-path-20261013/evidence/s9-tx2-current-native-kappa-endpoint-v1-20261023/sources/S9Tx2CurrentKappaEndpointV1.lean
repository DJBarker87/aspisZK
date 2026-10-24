import S9Tx2SourceNativePairV1
import S9CurrentReaderConstructorInputsV1
import S9ConstructorNativeReceiverCanonicalV1
import S9ResumeKappaAlphaCanonicalV1
import S9ActualPairKappaPolynomialV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9Tx2CurrentKappaEndpointV1
open AspisR1Stage2
open AspisR1S9Stage2NativeFinishSlotsV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

def withCurrentReaders {H : Type} (ops : AspisR1S4Tx2FullSourceOwnedCutV1.Ops H) :
    AspisR1S4Tx2FullSourceOwnedCutV1.Ops H :=
  {ops with resumeOps:=AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders ops.resumeOps}

private theorem selected_native_length (a : Array SW 2#usize) (selected : Slice SW)
    (h : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice SW)) a {«end»:=2#usize}=.ok selected) :
    Slice.len (sourceSliceToNative selected)=2#usize := by
  rw [AspisR1S9ArrayTwoPrefixSourceV1.successful_array_two_prefix_eq a selected h]
  apply UScalar.eq_of_val_eq
  simpa [Slice.len,Slice.length,sourceSliceToNative,Array.to_slice] using a.property

private theorem final_span_wrapping_product : Usize.wrapping_mul 64#usize 32#usize=2048#usize := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_mul_val_eq]
  change 2048 % UScalar.size .Usize = 2048
  have hv : (2048#usize).val=2048 := rfl
  exact Nat.mod_eq_of_lt (by simpa only [UScalar.size,hv] using (2048#usize).hBounds)

/-- SAME source-created View, SAME source resume/finish, actual native Pair,
its own canonical-parts kappa polynomial and actual source comparisons. All
Pair caller canonicality/length guards are discharged internally. Remaining
Ops/comparator semantics, parts-to-spend-relation and runtime/security-event
transport are explicit boundaries; no independent Current finish is assumed. -/
theorem source_tx2_current_returns_native_kappa_polynomial {H : Type}
    (ops : AspisR1S4Tx2FullSourceOwnedCutV1.Ops H)
    (finishOps : Stage2Finish.FinishOps Weights)
    (call : AspisR1S4Tx2FullSourceOwnedCutV1.QueryCall)
    (inst : aspis_core.digest.Digest32 H)
    (publicBytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (h : AspisR1S4Tx2FullSourceOwnedCutV1.tx2CommonFullSourceCut
      (AspisR1S9Tx2SameFinalViewSpanV1.withSourceFinalConstants
        (AspisR1S9Tx2SourceNativePairV1.withNativeFinish (withCurrentReaders ops) finishOps))
      call inst publicBytes proof checkpoint hash obs=.ok (.Ok ())) :
    ∃ (v : verifier.View) (p : verifier.Prepared) (resumeAcc finalAcc : verifier.Accumulator)
      (final openings : Usize) (self : Weights) (selected : Slice SW) (nativeOut : NW)
      (parts : Array NW 7#usize) (alpha0 claim0 alpha1 claim1 actual : SW),
      verifier.resumeWithOps
        (AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders ops.resumeOps)
        inst checkpoint proof publicBytes transport.Variant.S2 hash=.ok (.Ok (p,resumeAcc)) ∧
      Stage2Finish.verifier.finishRelationWithOps (installNative finishOps) v p finalAcc obs=.ok (.Ok ()) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=final,«end»:=openings}=.ok v.final_message ∧
      v.final_message.val.length=2048 ∧
      AspisR1S9FinishActualConstructorSlotV1.actualNewWeightsSlot
        (stageVariant p.variant) (mapArray stageQM p.semantic_alpha) (mapArray stagePoint p.z)=.ok (.Ok self) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice SW)) p.alpha {«end»:=2#usize}=.ok selected ∧
      Array.index_usize p.alpha 0#usize=.ok alpha0 ∧
      Stage2Finish.verifier.finishRelationRoundWithOps (installNative finishOps)
        v.round0 alpha0 p.claim 0#usize=.ok (.Ok claim0) ∧
      Array.index_usize p.alpha 1#usize=.ok alpha1 ∧
      Stage2Finish.verifier.finishRelationRoundWithOps (installNative finishOps)
        v.round1 alpha1 claim0 1#usize=.ok (.Ok claim1) ∧
      sourcePair self selected v.final_message p.kappa=.ok (.Ok (nativeToSource nativeOut)) ∧
      finishOps.ne (nativeToSource nativeOut) claim1=.ok false ∧
      finishOps.dot v.final_message (alloc.vec.Vec.deref finalAcc.weights)=.ok (.Ok actual) ∧
      finalAcc.next=22#usize ∧ finishOps.ne actual finalAcc.rhs=.ok false ∧
      AspisR1S9ProductionPairCutV1.weights.Weights.pair self (sourceSliceToNative selected)
        v.final_message (sourceToNative p.kappa)=.ok (.Ok nativeOut) ∧
      AspisR1S9ActualFinalSumV1.Good parts ∧ AspisR1S9ActualPairWideCanonicalV1.Canonical nativeOut ∧
      AspisR1S9NativeWideDecodedArithmeticV1.decode nativeOut=
        AspisR1S9ActualKappaFinalSumV1.kappaPolynomial parts (sourceToNative p.kappa) := by
  obtain ⟨v,p,resumeAcc,finalAcc,final,openings,hresume,hfinish,hfinal,hopenings,hrange,hlen,hsize⟩ :=
    AspisR1S9Tx2SameFinalViewSpanV1.source_tx2_success_same_final_view
      (AspisR1S9Tx2SourceNativePairV1.withNativeFinish (withCurrentReaders ops) finishOps)
      call inst publicBytes proof checkpoint hash obs h
  change verifier.resumeWithOps
    (AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders ops.resumeOps)
    inst checkpoint proof publicBytes transport.Variant.S2 hash=.ok (.Ok (p,resumeAcc)) at hresume
  change Stage2Finish.verifier.finishRelationWithOps (installNative finishOps) v p finalAcc obs=.ok (.Ok ()) at hfinish
  obtain ⟨fields⟩ := AspisR1.OraclePortCkptAbiSourceFields.successful_fields
    (AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders ops.resumeOps)
    inst checkpoint proof publicBytes transport.Variant.S2 hash p resumeAcc hresume
  have hs2 : p.variant=transport.Variant.S2 := fields.variant
  have htwo : (installNative finishOps).folds p.variant=.ok (2#usize) := by
    rw [hs2]
    norm_num [installNative,stageVariant,AspisR1S9ResumeFinishNativePairBindingV1.stageVariant,
      AspisR1FinishRelationCurrent.transport.Variant.folds,
      AspisR1FinishRelationCurrent.transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
      read_discriminant,AspisR1FinishRelationCurrent.transport.Variant.read_discriminant]
  obtain ⟨alpha0,claim0,alpha1,claim1,self,selected,pairValue,actual,
    ha0,hr0,ha1,hr1,hnew,hselected,hpair,hcompare,hdot,hnext,hfinalCompare⟩ :=
    Stage2Finish.finish_success (installNative finishOps) v p finalAcc obs htwo hfinish
  have hcnew := source_new_success p.variant p.semantic_alpha p.z self hnew
  obtain ⟨nativeOut,hnative,hvalue⟩ := source_pair_success self selected v.final_message p.kappa pairValue hpair
  have hself := AspisR1S9FinishActualConstructorSlotV1.actualNewWeightsSlot_success_variant
    (stageVariant p.variant) (mapArray stageQM p.semantic_alpha) (mapArray stagePoint p.z) self hcnew
  rw [hs2] at hself
  obtain ⟨halpha,hz⟩ :=
    AspisR1S9CurrentReaderConstructorInputsV1.current_resume_constructor_inputs_canonical
      ops.resumeOps inst checkpoint proof publicBytes transport.Variant.S2 hash p resumeAcc hresume
  obtain ⟨hf,hp,he⟩ :=
    AspisR1S9ConstructorNativeReceiverCanonicalV1.actual_constructor_slot_success_receiver_canonical
      (stageVariant p.variant) (mapArray stageQM p.semantic_alpha) (mapArray stagePoint p.z)
      self halpha hz hcnew
  let baseReaders : ResumeOps := {ops.resumeOps with
    readK:=AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1.readerKCurrent ops.resumeOps.raw
    readSemanticAlpha:=AspisR1S9CheckpointSemanticAlphaSourceV1.source
      (AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1.readerKCurrent ops.resumeOps.raw)}
  have hresumeE : verifier.resumeWithOps
      (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE baseReaders)
      inst checkpoint proof publicBytes transport.Variant.S2 hash=.ok (.Ok (p,resumeAcc)) := hresume
  obtain ⟨hkappa,_⟩ := AspisR1S9ResumeKappaAlphaCanonicalV1.resume_kappa_alpha_canonical
    baseReaders inst checkpoint proof publicBytes transport.Variant.S2 hash p resumeAcc hresumeE
  have hknative : AspisR1S9ActualPairWideCanonicalV1.Canonical (sourceToNative p.kappa) :=
    AspisR1S9ResumeAlphaPairInputV1.toNative_canonical p.kappa hkappa
  have hcanalpha : ∀ i value,Slice.index_usize (sourceSliceToNative selected) i=.ok value →
      AspisR1S9ActualPairWideCanonicalV1.Canonical value :=
    AspisR1S9ResumeAlphaPairInputV1.resume_finish_prefix_native_alpha_canonical
      baseReaders inst checkpoint proof publicBytes transport.Variant.S2 hash p resumeAcc selected hresumeE hselected
  have hfold := selected_native_length p.alpha selected hselected
  have hspan : Slice.len v.final_message=Usize.wrapping_mul 64#usize 32#usize :=
    hsize.trans final_span_wrapping_product.symm
  obtain ⟨parts,hparts,hout,hpoly⟩ :=
    AspisR1S9ActualPairKappaPolynomialV1.actual_pair_returns_own_kappa_polynomial
      self (sourceSliceToNative selected) v.final_message (sourceToNative p.kappa) nativeOut
      hself hf he hcanalpha hfold hspan hnative hknative
  have hsource : sourcePair self selected v.final_message p.kappa=.ok (.Ok (nativeToSource nativeOut)) := by
    rw [hvalue] at hpair
    exact hpair
  rw [hvalue] at hcompare
  exact ⟨v,p,resumeAcc,finalAcc,final,openings,self,selected,nativeOut,parts,
    alpha0,claim0,alpha1,claim1,actual,hresume,hfinish,hrange,hlen,hcnew,hselected,
    ha0,hr0,ha1,hr1,hsource,hcompare,hdot,hnext,hfinalCompare,hnative,hparts,hout,hpoly⟩

#print axioms source_tx2_current_returns_native_kappa_polynomial
end AspisR1S9Tx2CurrentKappaEndpointV1
