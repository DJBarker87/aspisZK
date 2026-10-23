import S9SourceResumeConstructorModelV1
import S9SharedTracePointPartsV1
import S9RegularTraceFinalModelV1
import S9Tx2CurrentTracedKappaEndpointV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ResumeFinalFiveModelV1
open AspisR1Stage2
open AspisR1S9Stage2NativeFinishSlotsV1
open AspisR1S9ResumeConstructorInputsCanonicalV1
open AspisR1S9FinishActualConstructorSlotV1
open AspisR1S9FactorTableSemanticsV1
open AspisR1S9FactorArrayEntryV1 (atN)
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)
open AspisR1S9SharedHighConstructorModelV1 (rowValue)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- Strict source resume and the SAME actual constructor/selected-alpha/Trace
discharge table, receiver, variant and alpha premises of all five final point rows.
No independent Current View, finish, model or canonicality is assumed. This
source-event join is consumed by the actual caller; it is not a runtime or
complete soundness theorem. -/
theorem source_resume_final_five_point_model {H : Type}
    (ops : ResumeOps) (inst : aspis_core.digest.Digest32 H)
    (checkpoint proof publicBytes : Slice U8) (hash : H)
    (p : verifier.Prepared) (resumeAcc : verifier.Accumulator)
    (self : AspisR1S9Stage2NativeFinishSlotsV1.Weights) (selected : Slice SW) (f : Slice U8) (nativeOut : NW)
    (parts : Array NW 7#usize) (k : Array NW 7#usize)
    (hresume : verifier.resumeWithOps
      (AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders ops)
      inst checkpoint proof publicBytes transport.Variant.S2 hash=.ok (.Ok (p,resumeAcc)))
    (hnew : actualNewWeightsSlot (stageVariant p.variant)
      (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stageQM p.semantic_alpha) (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stagePoint p.z)=.ok (.Ok self))
    (hselected : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice SW)) p.alpha {«end»:=2#usize}=.ok selected)
    (htrace : AspisR1S9FinalPartsSourceTraceV1.Trace self (sourceSliceToNative selected)
      f (sourceToNative p.kappa) nativeOut parts k) :
    ∃ (w : AspisR1S9ActualWeightsNewBoxNewV3.Weights) (model : Table),
      self=fromCtorWeights w ∧ Meaning w.factors model ∧
      AspisR1S9StatementFactorOuterSemanticsV1.RowsPrefix w.points model 3 ∧
      AspisR1S9ConstructorV3CompleteFactorSemanticsV1.CircleRows (inputZ p) model ∧
      AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.r0.statement_points (inputAlpha p)=.ok w.points ∧
      ∃ a0 a1 : NW,
        Slice.index_usize (sourceSliceToNative selected) 0#usize=.ok a0 ∧
        Slice.index_usize (sourceSliceToNative selected) 1#usize=.ok a1 ∧
        AspisR1S9RegularPhaseConstructorModelV1.Means model (decodeNative a0) (decodeNative a1) f parts 1#usize (by decide) 0 ∧
        AspisR1S9RegularPhaseConstructorModelV1.Means model (decodeNative a0) (decodeNative a1) f parts 2#usize (by decide) 1 ∧
        AspisR1S9RegularPhaseConstructorModelV1.Means model (decodeNative a0) (decodeNative a1) f parts 3#usize (by decide) 2 ∧
        AspisR1S9RegularPhaseConstructorModelV1.Means model (decodeNative a0) (decodeNative a1) f parts 5#usize (by decide) 3 ∧
        AspisR1S9RegularPhaseConstructorModelV1.Means model (decodeNative a0) (decodeNative a1) f parts 6#usize (by decide) 4 := by
  obtain ⟨w,model,hsource,hself,hm,hrows,hcircle,hpoints,hvariant,hextra⟩ :=
    AspisR1S9SourceResumeConstructorModelV1.source_resume_same_constructor_complete_model
      ops inst checkpoint proof publicBytes transport.Variant.S2 hash p resumeAcc self hresume hnew
  obtain ⟨halpha,hz⟩ :=
    AspisR1S9CurrentReaderConstructorInputsV1.current_resume_constructor_inputs_canonical
      ops inst checkpoint proof publicBytes transport.Variant.S2 hash p resumeAcc hresume
  obtain ⟨hf,hp,he⟩ :=
    AspisR1S9ConstructorNativeReceiverCanonicalV1.actual_constructor_slot_success_receiver_canonical
      (stageVariant p.variant) (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stageQM p.semantic_alpha) (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stagePoint p.z)
      self halpha hz hnew
  obtain ⟨fields⟩ := AspisR1.OraclePortCkptAbiSourceFields.successful_fields
    (AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders ops)
    inst checkpoint proof publicBytes transport.Variant.S2 hash p resumeAcc hresume
  have hs2 : p.variant=transport.Variant.S2 := fields.variant
  have hv := actualNewWeightsSlot_success_variant
    (stageVariant p.variant) (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stageQM p.semantic_alpha) (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stagePoint p.z) self hnew
  rw [hs2] at hv
  let baseReaders : ResumeOps := {ops with
    readK:=AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1.readerKCurrent ops.raw
    readSemanticAlpha:=AspisR1S9CheckpointSemanticAlphaSourceV1.source
      (AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1.readerKCurrent ops.raw)}
  have hresumeE : verifier.resumeWithOps (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE baseReaders)
    inst checkpoint proof publicBytes transport.Variant.S2 hash=.ok (.Ok (p,resumeAcc)) := hresume
  have hca := AspisR1S9ResumeAlphaPairInputV1.resume_finish_prefix_native_alpha_canonical
    baseReaders inst checkpoint proof publicBytes transport.Variant.S2 hash p resumeAcc selected hresumeE hselected
  have hf' := hf
  have hv' := hv
  have ht := htrace
  rw [hself] at hf' hv' ht
  rcases ht with hshared | hunshared
  · obtain ⟨a0,a1,ha0,ha1,hv0,hv2⟩ :=
      AspisR1S9SharedTracePointPartsV1.shared_trace_final_point_parts
        w model hm hf' hv' (sourceSliceToNative selected) f (sourceToNative p.kappa) nativeOut parts k hca hshared
    obtain ⟨b0,b1,hb0,hb1,hv1,hv3,hv4⟩ :=
      AspisR1S9RegularTraceFinalModelV1.shared_trace_final_regular_parts
        w model hm hf' hv' (sourceSliceToNative selected) f (sourceToNative p.kappa) nativeOut parts k hca hshared
    have he0 : b0=a0 := Result.ok.inj (hb0.symm.trans ha0)
    have he1 : b1=a1 := Result.ok.inj (hb1.symm.trans ha1)
    subst b0; subst b1
    exact ⟨w,model,hself,hm,hrows,hcircle,hpoints,a0,a1,ha0,ha1,hv0,hv1,hv2,hv3,hv4⟩
  · obtain ⟨a0,a1,ha0,ha1,hv0,hv1,hv2,hv3,hv4⟩ :=
      AspisR1S9RegularTraceFinalModelV1.unshared_trace_final_regular_parts
        w model hm hf' hv' (sourceSliceToNative selected) f (sourceToNative p.kappa) nativeOut parts k hca hunshared
    exact ⟨w,model,hself,hm,hrows,hcircle,hpoints,a0,a1,ha0,ha1,hv0,hv1,hv2,hv3,hv4⟩

#print axioms source_resume_final_five_point_model
end AspisR1S9ResumeFinalFiveModelV1
