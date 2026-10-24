import S9SourceStoredRowGuardsV1
import S9Tx2CurrentTracedKappaEndpointV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9Tx2CurrentStoredRowsV1
open AspisR1Stage2
open AspisR1S9Stage2NativeFinishSlotsV1
open AspisR1S9Tx2CurrentTracedKappaEndpointV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- One accepted actual owned tx2 source event supplies the SAME View,
resume, constructor, selected alpha, final parts/k, comparisons and both
stored row0/4 values. All S2/alphaCan/extraCan/fspan guards are discharged;
Ops/runtime/carrier security transport remain explicit external boundaries. -/
theorem source_tx2_current_returns_stored_rows_zero_four {H : Type}
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
      (parts : Array NW 7#usize) (k : Array NW 7#usize) (alpha0 claim0 alpha1 claim1 actual : SW)
      (hspan : Slice.len v.final_message=Usize.wrapping_mul 64#usize 32#usize),
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
      AspisR1S9FinalPartsSourceTraceV1.Trace self (sourceSliceToNative selected)
        v.final_message (sourceToNative p.kappa) nativeOut parts k ∧
      AspisR1S9ActualFinalSumV1.Good parts ∧ AspisR1S9ActualPairWideCanonicalV1.Canonical nativeOut ∧
      AspisR1S9NativeWideDecodedArithmeticV1.decode nativeOut=
        AspisR1S9ActualKappaFinalSumV1.kappaPolynomial parts (sourceToNative p.kappa) ∧
      AspisR1S9SourceStoredRowGuardsV1.StoredRows self selected v.final_message
        (sourceToNative p.kappa) nativeOut parts k hspan := by
  obtain ⟨v,p,resumeAcc,finalAcc,final,openings,self,selected,nativeOut,parts,k,
    alpha0,claim0,alpha1,claim1,actual,hresume,hfinish,hrange,hlen,hnew,hselected,
    ha0,hr0,ha1,hr1,hsource,hcompare,hdot,hnext,hfinalCompare,hnative,htrace,hparts,hout,hpoly⟩ :=
    AspisR1S9Tx2CurrentTracedKappaEndpointV1.source_tx2_current_returns_traced_native_kappa_polynomial
      ops finishOps call inst publicBytes proof checkpoint hash obs h
  have hsize : Slice.len v.final_message=2048#usize := by
    apply UScalar.eq_of_val_eq
    change v.final_message.val.length=2048
    exact hlen
  have hspan : Slice.len v.final_message=Usize.wrapping_mul 64#usize 32#usize :=
    hsize.trans AspisR1S9InactiveFinalZeroCellV1.final_span_wrapping_product.symm
  have hrows := AspisR1S9SourceStoredRowGuardsV1.source_resume_traced_final_rows
    ops.resumeOps inst checkpoint proof publicBytes hash p resumeAcc self selected v.final_message nativeOut parts k
    hresume hnew hselected hspan htrace
  exact ⟨v,p,resumeAcc,finalAcc,final,openings,self,selected,nativeOut,parts,k,
    alpha0,claim0,alpha1,claim1,actual,hspan,hresume,hfinish,hrange,hlen,hnew,hselected,
    ha0,hr0,ha1,hr1,hsource,hcompare,hdot,hnext,hfinalCompare,hnative,htrace,hparts,hout,hpoly,hrows⟩

#print axioms source_tx2_current_returns_stored_rows_zero_four
end AspisR1S9Tx2CurrentStoredRowsV1
