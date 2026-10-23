import S9Tx2CurrentKappaEndpointV1
import S9Stage2DerivedEqBodyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9Tx2ComparedKappaEndpointV1
open AspisR1Stage2
open AspisR1S9Stage2NativeFinishSlotsV1
open AspisR1S9Stage2WideComparatorV1 (installComparator)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
def decodeSource (x : SW) := AspisR1S9NativeWideDecodedArithmeticV1.decode (sourceToNative x)
theorem native_source_roundtrip (x : NW) : sourceToNative (nativeToSource x)=x := by rfl
/-- The SAME accepted source-created View/resume/native Pair now gives
structural equality to the real second-round claim and actual dot/rhs equality
under the concrete unchanged derived-field/default-ne comparator. Kappa
meaning is transported to that same source claim. Other operation semantics,
parts-to-spend-relation and complete runtime/security ports remain open. -/
theorem source_tx2_compared_claim_is_own_kappa_polynomial {H : Type}
    (ops : AspisR1S4Tx2FullSourceOwnedCutV1.Ops H)
    (finishOps : Stage2Finish.FinishOps Weights)
    (call : AspisR1S4Tx2FullSourceOwnedCutV1.QueryCall)
    (inst : aspis_core.digest.Digest32 H)
    (publicBytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (h : AspisR1S4Tx2FullSourceOwnedCutV1.tx2CommonFullSourceCut
      (AspisR1S9Tx2SameFinalViewSpanV1.withSourceFinalConstants
        (AspisR1S9Tx2SourceNativePairV1.withNativeFinish (AspisR1S9Tx2CurrentKappaEndpointV1.withCurrentReaders ops) (installComparator finishOps)))
      call inst publicBytes proof checkpoint hash obs=.ok (.Ok ())) :
    ∃ (v : verifier.View) (p : verifier.Prepared) (resumeAcc finalAcc : verifier.Accumulator)
      (final openings : Usize) (self : Weights) (selected : Slice SW) (nativeOut : NW)
      (parts : Array NW 7#usize) (alpha0 claim0 alpha1 claim1 actual : SW),
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
      AspisR1S9ActualFinalSumV1.Good parts ∧ AspisR1S9ActualPairWideCanonicalV1.Canonical nativeOut ∧
      AspisR1S9NativeWideDecodedArithmeticV1.decode nativeOut=
        AspisR1S9ActualKappaFinalSumV1.kappaPolynomial parts (sourceToNative p.kappa) ∧
      decodeSource claim1=
        AspisR1S9ActualKappaFinalSumV1.kappaPolynomial parts (sourceToNative p.kappa) := by
  obtain ⟨v,p,resumeAcc,finalAcc,final,openings,self,selected,nativeOut,parts,
    alpha0,claim0,alpha1,claim1,actual,hresume,hfinish,hrange,hlen,hnew,hselected,
    ha0,hr0,ha1,hr1,hsource,hcompare,hdot,hnext,hfinalCompare,hnative,hparts,hout,hpoly⟩ :=
    AspisR1S9Tx2CurrentKappaEndpointV1.source_tx2_current_returns_native_kappa_polynomial
      ops (installComparator finishOps) call inst publicBytes proof checkpoint hash obs h
  have hpairEq : nativeToSource nativeOut=claim1 :=
    AspisR1S9Stage2DerivedEqBodyV1.default_ne_false_eq _ _
      ((AspisR1S9Stage2DerivedEqBodyV1.default_ne_full_result _ _).trans hcompare)
  have hdotEq : actual=finalAcc.rhs :=
    AspisR1S9Stage2DerivedEqBodyV1.default_ne_false_eq _ _
      ((AspisR1S9Stage2DerivedEqBodyV1.default_ne_full_result _ _).trans hfinalCompare)
  have hdecode := congrArg decodeSource hpairEq
  have hdecodeOut : decodeSource (nativeToSource nativeOut)=
      AspisR1S9NativeWideDecodedArithmeticV1.decode nativeOut := by
    unfold decodeSource
    rw [native_source_roundtrip]
  rw [hdecodeOut] at hdecode
  have hclaim := hdecode.symm.trans hpoly
  exact ⟨v,p,resumeAcc,finalAcc,final,openings,self,selected,nativeOut,parts,
    alpha0,claim0,alpha1,claim1,actual,hresume,hfinish,hrange,hlen,hnew,hselected,
    ha0,hr0,ha1,hr1,hsource,hpairEq,hdot,hnext,hdotEq,hnative,hparts,hout,hpoly,hclaim⟩
#print axioms native_source_roundtrip
#print axioms source_tx2_compared_claim_is_own_kappa_polynomial
end AspisR1S9Tx2ComparedKappaEndpointV1
