import S9Tx2AllFinalPartsV1
import S9SevenSourceRowValuesV1
import S9SourceStoredRowsSameAlphaV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9Tx2FoldedPartsV1
open AspisR1Stage2
open AspisR1S9Stage2NativeFinishSlotsV1
open AspisR1S9Stage2WideComparatorV1 (installComparator)
open AspisR1S9Tx2ComparedTracedKappaEndpointV1 (decodeSource)
open AspisR1S9ResumeConstructorInputsCanonicalV1 (inputZ inputAlpha)
open AspisR1S9FinishActualConstructorSlotV1 (fromCtorWeights)
open AspisR1S9FactorTableSemanticsV1 (Table Meaning)
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

open AspisR1S9Tx2AllFinalPartsV1 (PointModel)

/-- One actual constructor model, actual alpha and seed reads, and all seven
folded row values on the SAME final array. No arbitrary raw table is substituted. -/
def FoldedParts (p : verifier.Prepared) (self : Weights) (selected : Slice SW)
    (f : Slice U8) (parts : Array NW 7#usize) : Prop :=
  ∃ (w : AspisR1S9ActualWeightsNewBoxNewV3.Weights) (model : Table),
    self=fromCtorWeights w ∧ Meaning w.factors model ∧
    AspisR1S9StatementFactorOuterSemanticsV1.RowsPrefix w.points model 3 ∧
    AspisR1S9ConstructorV3CompleteFactorSemanticsV1.CircleRows (inputZ p) model ∧
    AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.r0.statement_points (inputAlpha p)=.ok w.points ∧
    ∃ (a0 a1 : NW) (q0 q1 : AspisR1S9ActiveOriginalCoefficientsV1.Q),
      Slice.index_usize (sourceSliceToNative selected) 0#usize=.ok a0 ∧
      Slice.index_usize (sourceSliceToNative selected) 1#usize=.ok a1 ∧
      Array.index_usize self.extra 0#usize=.ok q0 ∧
      Array.index_usize self.extra 1#usize=.ok q1 ∧
      ∀ i : Fin 7,
        AspisR1S9NativeWideDecodedArithmeticV1.decode (AspisR1S9KappaFinSevenV1.partAt parts i)=
          AspisR1.RoundPairing.dot (AspisR1S9StoredZeroFourSameAlphaV1.input f)
            (AspisR1.RoundPairing.dualFold (decodeNative a1)
              (AspisR1.RoundPairing.dualFold (decodeNative a0)
                (AspisR1S9SevenSourceRowValuesV1.rows model q0 q1 i)))

theorem source_tx2_compared_claim_has_folded_same_parts {H : Type}
    (ops : AspisR1S4Tx2FullSourceOwnedCutV1.Ops H)
    (finishOps : Stage2Finish.FinishOps Weights)
    (call : AspisR1S4Tx2FullSourceOwnedCutV1.QueryCall)
    (inst : aspis_core.digest.Digest32 H)
    (publicBytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (h : AspisR1S4Tx2FullSourceOwnedCutV1.tx2CommonFullSourceCut
      (AspisR1S9Tx2SameFinalViewSpanV1.withSourceFinalConstants
        (AspisR1S9Tx2SourceNativePairV1.withNativeFinish (AspisR1S9Tx2CurrentTracedKappaEndpointV1.withCurrentReaders ops) (installComparator finishOps)))
      call inst publicBytes proof checkpoint hash obs=.ok (.Ok ())) :
    ∃ (v : verifier.View) (p : verifier.Prepared) (resumeAcc finalAcc : verifier.Accumulator)
      (final openings : Usize) (self : Weights) (selected : Slice SW) (nativeOut : NW)
      (parts : Array NW 7#usize) (k : Array NW 7#usize) (alpha0 claim0 alpha1 claim1 actual : SW)
      (hspan : Slice.len v.final_message=Usize.wrapping_mul 64#usize 32#usize),
      verifier.resumeWithOps
        (AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders ops.resumeOps)
        inst checkpoint proof publicBytes transport.Variant.S2 hash=.ok (.Ok (p,resumeAcc)) ∧
      Stage2Finish.verifier.finishRelationWithOps (installNative (installComparator finishOps)) v p finalAcc obs=.ok (.Ok ()) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=final,«end»:=openings}=.ok v.final_message ∧
      v.final_message.val.length=2048 ∧
      AspisR1S9FinishActualConstructorSlotV1.actualNewWeightsSlot
        (stageVariant p.variant) (mapArray stageQM p.semantic_alpha) (mapArray stagePoint p.z)=.ok (.Ok self) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice SW)) p.alpha {«end»:=2#usize}=.ok selected ∧
      Array.index_usize p.alpha 0#usize=.ok alpha0 ∧
      Stage2Finish.verifier.finishRelationRoundWithOps (installNative (installComparator finishOps))
        v.round0 alpha0 p.claim 0#usize=.ok (.Ok claim0) ∧
      Array.index_usize p.alpha 1#usize=.ok alpha1 ∧
      Stage2Finish.verifier.finishRelationRoundWithOps (installNative (installComparator finishOps))
        v.round1 alpha1 claim0 1#usize=.ok (.Ok claim1) ∧
      sourcePair self selected v.final_message p.kappa=.ok (.Ok (nativeToSource nativeOut)) ∧
      nativeToSource nativeOut=claim1 ∧
      finishOps.dot v.final_message (alloc.vec.Vec.deref finalAcc.weights)=.ok (.Ok actual) ∧
      finalAcc.next=22#usize ∧ actual=finalAcc.rhs ∧
      AspisR1S9ProductionPairCutV1.weights.Weights.pair self (sourceSliceToNative selected)
        v.final_message (sourceToNative p.kappa)=.ok (.Ok nativeOut) ∧
      AspisR1S9FinalPartsSourceTraceV1.Trace self (sourceSliceToNative selected)
        v.final_message (sourceToNative p.kappa) nativeOut parts k ∧
      AspisR1S9ActualFinalSumV1.Good parts ∧ AspisR1S9ActualPairWideCanonicalV1.Canonical nativeOut ∧
      AspisR1S9NativeWideDecodedArithmeticV1.decode nativeOut=
        AspisR1S9ActualKappaFinalSumV1.kappaPolynomial parts (sourceToNative p.kappa) ∧
      decodeSource claim1=
        AspisR1S9ActualKappaFinalSumV1.kappaPolynomial parts (sourceToNative p.kappa) ∧
      AspisR1S9SourceStoredRowGuardsV1.StoredRows self selected v.final_message
        (sourceToNative p.kappa) nativeOut parts k hspan ∧
      PointModel p self selected v.final_message parts ∧
      FoldedParts p self selected v.final_message parts := by
  obtain ⟨v,p,resumeAcc,finalAcc,final,openings,self,selected,nativeOut,parts,k,
    alpha0,claim0,alpha1,claim1,actual,hspan,hresume,hfinish,hrange,hlen,hnew,hselected,
    ha0,hr0,ha1,hr1,hsource,hpairEq,hdot,hnext,hdotEq,hnative,htrace,hparts,hout,hpoly,hclaim,hstored,hpoint⟩ :=
    AspisR1S9Tx2AllFinalPartsV1.source_tx2_compared_claim_has_all_same_final_parts
      ops finishOps call inst publicBytes proof checkpoint hash obs h
  have hfolded : FoldedParts p self selected v.final_message parts := by
    obtain ⟨w,model,hself,hm,hrows,hcircle,hproducer,a0,a1,hread0,hread1,h1,h2,h3,h5,h6⟩ := hpoint
    have hz := AspisR1S9SourceStoredRowsSameAlphaV1.source_resume_stored_rows_same_alpha
      ops.resumeOps inst checkpoint proof publicBytes hash p resumeAcc self selected
      v.final_message nativeOut parts k a0 a1 hresume hnew hselected hspan hstored hread0 hread1
    have hp := AspisR1S9PointPartsFoldValuesV1.five_means_folds model
      (decodeNative a0) (decodeNative a1) v.final_message parts
      (by decide) (by decide) (by decide) (by decide) (by decide) h1 h2 h3 h5 h6
    obtain ⟨q0,q1,hq0,hq1,hvalues⟩ := AspisR1S9SevenSourceRowValuesV1.all_values
      self model a0 a1 v.final_message parts hz hp
    exact ⟨w,model,hself,hm,hrows,hcircle,hproducer,a0,a1,q0,q1,hread0,hread1,hq0,hq1,hvalues⟩
  exact ⟨v,p,resumeAcc,finalAcc,final,openings,self,selected,nativeOut,parts,k,
    alpha0,claim0,alpha1,claim1,actual,hspan,hresume,hfinish,hrange,hlen,hnew,hselected,
    ha0,hr0,ha1,hr1,hsource,hpairEq,hdot,hnext,hdotEq,hnative,htrace,hparts,hout,hpoly,hclaim,hstored,hpoint,hfolded⟩

#print axioms source_tx2_compared_claim_has_folded_same_parts
end AspisR1S9Tx2FoldedPartsV1
