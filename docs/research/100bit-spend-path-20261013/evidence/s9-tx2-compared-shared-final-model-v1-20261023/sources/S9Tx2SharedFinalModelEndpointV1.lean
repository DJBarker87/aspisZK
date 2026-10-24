import S9Tx2ComparedTracedKappaEndpointV1
import S9ResumeSharedFinalModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9Tx2SharedFinalModelEndpointV1
open AspisR1Stage2
open AspisR1S9Stage2NativeFinishSlotsV1
open AspisR1S9Stage2WideComparatorV1 (installComparator)
open AspisR1S9Tx2ComparedTracedKappaEndpointV1 (decodeSource)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- One accepted concrete source-cut event retains its actual compared claim,
View, resume, receiver, selected alpha, output and operational parts/k Trace.
On that SAME Trace's shared branch, its final cells1/3 have the SAME constructor
model meanings. Other source operation slots, full relation and security/runtime
transport remain explicit; this is no independent Current finish event. -/
theorem source_tx2_compared_claim_and_shared_final_model {H : Type}
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
      (parts : Array NW 7#usize) (k : Array NW 7#usize) (alpha0 claim0 alpha1 claim1 actual : SW),
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
      (AspisR1S9FinalPartsSourceTraceV1.SharedTrace self (sourceSliceToNative selected)
        v.final_message (sourceToNative p.kappa) nativeOut parts k →
        ∃ (w : AspisR1S9ActualWeightsNewBoxNewV3.Weights)
          (model : AspisR1S9FactorTableSemanticsV1.Table),
          self=AspisR1S9FinishActualConstructorSlotV1.fromCtorWeights w ∧
          AspisR1S9FactorTableSemanticsV1.Meaning w.factors model ∧
          AspisR1S9StatementFactorOuterSemanticsV1.RowsPrefix w.points model 3 ∧
          AspisR1S9ConstructorV3CompleteFactorSemanticsV1.CircleRows
            (AspisR1S9ResumeConstructorInputsCanonicalV1.inputZ p) model ∧
          AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.r0.statement_points
            (AspisR1S9ResumeConstructorInputsCanonicalV1.inputAlpha p)=.ok w.points ∧
          ∃ a0 a1 : NW,
            Slice.index_usize (sourceSliceToNative selected) 0#usize=.ok a0 ∧
            Slice.index_usize (sourceSliceToNative selected) 1#usize=.ok a1 ∧
            AspisR1S9NativeDecodedScalarProductV1.decodeNative
              (AspisR1S9FactorArrayEntryV1.atN parts 1#usize (by decide))=
              AspisR1S9SharedHighConstructorModelV1.rowValue model
                (AspisR1S9NativeDecodedScalarProductV1.decodeNative a0)
                (AspisR1S9NativeDecodedScalarProductV1.decodeNative a1) v.final_message 0 ∧
            AspisR1S9NativeDecodedScalarProductV1.decodeNative
              (AspisR1S9FactorArrayEntryV1.atN parts 3#usize (by decide))=
              AspisR1S9SharedHighConstructorModelV1.rowValue model
                (AspisR1S9NativeDecodedScalarProductV1.decodeNative a0)
                (AspisR1S9NativeDecodedScalarProductV1.decodeNative a1) v.final_message 2) := by
  obtain ⟨v,p,resumeAcc,finalAcc,final,openings,self,selected,nativeOut,parts,k,
    alpha0,claim0,alpha1,claim1,actual,hresume,hfinish,hrange,hlen,hnew,hselected,
    ha0,hr0,ha1,hr1,hsource,hpairEq,hdot,hnext,hdotEq,hnative,htrace,hparts,hout,hpoly,hclaim⟩ :=
    AspisR1S9Tx2ComparedTracedKappaEndpointV1.source_tx2_compared_claim_has_traced_kappa_polynomial
      ops finishOps call inst publicBytes proof checkpoint hash obs h
  refine ⟨v,p,resumeAcc,finalAcc,final,openings,self,selected,nativeOut,parts,k,
    alpha0,claim0,alpha1,claim1,actual,hresume,hfinish,hrange,hlen,hnew,hselected,
    ha0,hr0,ha1,hr1,hsource,hpairEq,hdot,hnext,hdotEq,hnative,htrace,hparts,hout,hpoly,hclaim,?_⟩
  intro hshared
  exact AspisR1S9ResumeSharedFinalModelV1.source_resume_shared_final_point_model
    ops.resumeOps inst checkpoint proof publicBytes hash p resumeAcc self selected v.final_message
      nativeOut parts k hresume hnew hselected hshared

#print axioms source_tx2_compared_claim_and_shared_final_model
end AspisR1S9Tx2SharedFinalModelEndpointV1
