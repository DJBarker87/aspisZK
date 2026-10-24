import S9SourceResumeConstructorModelV1
import S9FinalPartsInactiveRowV1
import S9FinalPartsActiveRowV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9SourceStoredRowGuardsV1
open AspisR1Stage2
open AspisR1S9Stage2NativeFinishSlotsV1
open AspisR1S9ResumeConstructorInputsCanonicalV1
open AspisR1S9FinishActualConstructorSlotV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- The SAME strict source resume, actual constructor and selected-alpha
source event discharge every data/canonical caller guard used by final0/4.
No model meaning, independent Current View/finish or desired value is assumed. -/
theorem strict_source_stored_row_guards {H : Type}
    (ops : ResumeOps) (inst : aspis_core.digest.Digest32 H)
    (checkpoint proof publicBytes : Slice U8) (hash : H)
    (p : verifier.Prepared) (resumeAcc : verifier.Accumulator)
    (self : AspisR1S9Stage2NativeFinishSlotsV1.Weights) (selected : Slice SW)
    (hresume : verifier.resumeWithOps
      (AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders ops)
      inst checkpoint proof publicBytes transport.Variant.S2 hash=.ok (.Ok (p,resumeAcc)))
    (hnew : actualNewWeightsSlot (stageVariant p.variant)
      (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stageQM p.semantic_alpha)
      (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stagePoint p.z)=.ok (.Ok self))
    (hselected : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice SW)) p.alpha {«end»:=2#usize}=.ok selected) :
    self.variant=AspisR1S9ProductionPairCutV1.transport.Variant.S2 ∧
    (∀ i q,Array.index_usize self.extra i=.ok q → AspisR1S9ActualPairQMHelperTransportV1.Canonical q) ∧
    (∀ i x,Slice.index_usize (sourceSliceToNative selected) i=.ok x →
      AspisR1S9ActualPairWideCanonicalV1.Canonical x) := by
  obtain ⟨halpha,hz⟩ :=
    AspisR1S9CurrentReaderConstructorInputsV1.current_resume_constructor_inputs_canonical
      ops inst checkpoint proof publicBytes transport.Variant.S2 hash p resumeAcc hresume
  obtain ⟨hf,hp,he⟩ :=
    AspisR1S9ConstructorNativeReceiverCanonicalV1.actual_constructor_slot_success_receiver_canonical
      (stageVariant p.variant) (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stageQM p.semantic_alpha)
      (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stagePoint p.z) self halpha hz hnew
  obtain ⟨fields⟩ := AspisR1.OraclePortCkptAbiSourceFields.successful_fields
    (AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders ops)
    inst checkpoint proof publicBytes transport.Variant.S2 hash p resumeAcc hresume
  have hs2 : p.variant=transport.Variant.S2 := fields.variant
  have hv := actualNewWeightsSlot_success_variant
    (stageVariant p.variant) (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stageQM p.semantic_alpha)
    (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stagePoint p.z) self hnew
  rw [hs2] at hv
  let baseReaders : ResumeOps := {ops with
    readK:=AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1.readerKCurrent ops.raw
    readSemanticAlpha:=AspisR1S9CheckpointSemanticAlphaSourceV1.source
      (AspisR1S9CurrentCheckpointKDecoderReaderAcceptedV1.readerKCurrent ops.raw)}
  have hresumeE : verifier.resumeWithOps (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE baseReaders)
    inst checkpoint proof publicBytes transport.Variant.S2 hash=.ok (.Ok (p,resumeAcc)) := hresume
  have hca := AspisR1S9ResumeAlphaPairInputV1.resume_finish_prefix_native_alpha_canonical
    baseReaders inst checkpoint proof publicBytes transport.Variant.S2 hash p resumeAcc selected hresumeE hselected
  exact ⟨hv,he,hca⟩

/-- OUTPUT values for the explicit SAME operational final parts. Actual span
is a source-event boundary here; the accepted tx2 caller discharges it. -/
def StoredRows (self : AspisR1S9Stage2NativeFinishSlotsV1.Weights) (selected : Slice SW) (f : Slice U8)
    (kappa nativeOut : NW) (parts : Array NW 7#usize) (k : Array NW 7#usize)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize) : Prop :=
  (AspisR1S9FinalPartsSourceTraceV1.SharedTrace self (sourceSliceToNative selected) f kappa nativeOut parts k ∧
    AspisR1S9FinalPartsInactiveRowV1.InactiveRowStored true self (sourceSliceToNative selected) f parts hspan ∧
    AspisR1S9FinalPartsActiveRowV1.ActiveRowStored true self (sourceSliceToNative selected) f parts hspan) ∨
  (AspisR1S9FinalPartsSourceTraceV1.UnsharedTrace self (sourceSliceToNative selected) f kappa nativeOut parts k ∧
    AspisR1S9FinalPartsInactiveRowV1.InactiveRowStored false self (sourceSliceToNative selected) f parts hspan ∧
    AspisR1S9FinalPartsActiveRowV1.ActiveRowStored false self (sourceSliceToNative selected) f parts hspan)

theorem source_resume_traced_final_rows {H : Type}
    (ops : ResumeOps) (inst : aspis_core.digest.Digest32 H)
    (checkpoint proof publicBytes : Slice U8) (hash : H)
    (p : verifier.Prepared) (resumeAcc : verifier.Accumulator)
    (self : AspisR1S9Stage2NativeFinishSlotsV1.Weights) (selected : Slice SW) (f : Slice U8) (nativeOut : NW)
    (parts : Array NW 7#usize) (k : Array NW 7#usize)
    (hresume : verifier.resumeWithOps
      (AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders ops)
      inst checkpoint proof publicBytes transport.Variant.S2 hash=.ok (.Ok (p,resumeAcc)))
    (hnew : actualNewWeightsSlot (stageVariant p.variant)
      (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stageQM p.semantic_alpha)
      (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stagePoint p.z)=.ok (.Ok self))
    (hselected : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice SW)) p.alpha {«end»:=2#usize}=.ok selected)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (htrace : AspisR1S9FinalPartsSourceTraceV1.Trace self (sourceSliceToNative selected)
      f (sourceToNative p.kappa) nativeOut parts k) :
    StoredRows self selected f (sourceToNative p.kappa) nativeOut parts k hspan := by
  obtain ⟨hs2,he,ha⟩ := strict_source_stored_row_guards
    ops inst checkpoint proof publicBytes hash p resumeAcc self selected hresume hnew hselected
  cases htrace with
  | inl ht =>
    exact Or.inl ⟨ht,
      AspisR1S9FinalPartsInactiveRowV1.shared_trace_stored_inactive_row
        self (sourceSliceToNative selected) f (sourceToNative p.kappa) nativeOut parts k hs2 ha hspan ht,
      AspisR1S9FinalPartsActiveRowV1.shared_trace_stored_active_row
        self (sourceSliceToNative selected) f (sourceToNative p.kappa) nativeOut parts k hs2 ha he hspan ht⟩
  | inr ht =>
    exact Or.inr ⟨ht,
      AspisR1S9FinalPartsInactiveRowV1.unshared_trace_stored_inactive_row
        self (sourceSliceToNative selected) f (sourceToNative p.kappa) nativeOut parts k hs2 ha hspan ht,
      AspisR1S9FinalPartsActiveRowV1.unshared_trace_stored_active_row
        self (sourceSliceToNative selected) f (sourceToNative p.kappa) nativeOut parts k hs2 ha he hspan ht⟩

#print axioms strict_source_stored_row_guards
#print axioms source_resume_traced_final_rows
end AspisR1S9SourceStoredRowGuardsV1
