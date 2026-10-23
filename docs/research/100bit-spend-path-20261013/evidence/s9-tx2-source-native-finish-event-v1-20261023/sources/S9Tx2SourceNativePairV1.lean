import S9Tx2SameFinalViewSpanV1
import S9Stage2NativeFinishSlotsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9Tx2SourceNativePairV1
open AspisR1Stage2
open AspisR1S9Stage2NativeFinishSlotsV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

def withNativeFinish {H : Type} (ops : AspisR1S4Tx2FullSourceOwnedCutV1.Ops H)
    (finishOps : Stage2Finish.FinishOps Weights) : AspisR1S4Tx2FullSourceOwnedCutV1.Ops H :=
  {ops with finishRelation:=Stage2Finish.verifier.finishRelationWithOps (installNative finishOps)}

/-- Source-indexed accepted execution: the actual tx2 source cut creates this
View from this proof slice and calls the installed native constructor and Pair.
No arbitrary Current View or independent Current finish acceptance is assumed.
Remaining tx2/finish slots, raw runtime and release correspondence are explicit. -/
theorem source_tx2_success_same_native_pair {H : Type}
    (ops : AspisR1S4Tx2FullSourceOwnedCutV1.Ops H)
    (finishOps : Stage2Finish.FinishOps Weights)
    (call : AspisR1S4Tx2FullSourceOwnedCutV1.QueryCall)
    (inst : aspis_core.digest.Digest32 H)
    (publicBytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (h : AspisR1S4Tx2FullSourceOwnedCutV1.tx2CommonFullSourceCut
      (AspisR1S9Tx2SameFinalViewSpanV1.withSourceFinalConstants (withNativeFinish ops finishOps))
      call inst publicBytes proof checkpoint hash obs=.ok (.Ok ())) :
    ∃ (v : verifier.View) (p : verifier.Prepared)
      (resumeAcc finalAcc : verifier.Accumulator) (final openings : Usize)
      (self : Weights) (selected : Slice SW) (nativeOut : NW),
      verifier.resumeWithOps ops.resumeOps inst checkpoint proof publicBytes
        transport.Variant.S2 hash=.ok (.Ok (p,resumeAcc)) ∧
      Stage2Finish.verifier.finishRelationWithOps (installNative finishOps) v p finalAcc obs=.ok (.Ok ()) ∧
      p.variant=transport.Variant.S2 ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=final,«end»:=openings}=.ok v.final_message ∧
      v.final_message.val.length=2048 ∧ Slice.len v.final_message=2048#usize ∧
      AspisR1S9FinishActualConstructorSlotV1.actualNewWeightsSlot
        (stageVariant p.variant) (mapArray stageQM p.semantic_alpha) (mapArray stagePoint p.z)=.ok (.Ok self) ∧
      self.variant=AspisR1S9ProductionPairCutV1.transport.Variant.S2 ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice SW)) p.alpha {«end»:=2#usize}=.ok selected ∧
      AspisR1S9ProductionPairCutV1.weights.Weights.pair self (sourceSliceToNative selected)
        v.final_message (sourceToNative p.kappa)=.ok (.Ok nativeOut) := by
  obtain ⟨v,p,resumeAcc,finalAcc,final,openings,hresume,hfinish,hfinal,hopenings,hrange,hlen,hsize⟩ :=
    AspisR1S9Tx2SameFinalViewSpanV1.source_tx2_success_same_final_view
      (withNativeFinish ops finishOps) call inst publicBytes proof checkpoint hash obs h
  change verifier.resumeWithOps ops.resumeOps inst checkpoint proof publicBytes
    transport.Variant.S2 hash=.ok (.Ok (p,resumeAcc)) at hresume
  change Stage2Finish.verifier.finishRelationWithOps (installNative finishOps) v p finalAcc obs=.ok (.Ok ()) at hfinish
  obtain ⟨fields⟩ := AspisR1.OraclePortCkptAbiSourceFields.successful_fields
    ops.resumeOps inst checkpoint proof publicBytes transport.Variant.S2 hash p resumeAcc hresume
  have hs2 : p.variant=transport.Variant.S2 := fields.variant
  obtain ⟨self,selected,nativeOut,hnew,hself,hselected,hpair⟩ :=
    source_finish_s2_success_native_calls finishOps v p finalAcc obs hs2 hfinish
  exact ⟨v,p,resumeAcc,finalAcc,final,openings,self,selected,nativeOut,
    hresume,hfinish,hs2,hrange,hlen,hsize,hnew,hself,hselected,hpair⟩

#print axioms source_tx2_success_same_native_pair
end AspisR1S9Tx2SourceNativePairV1
