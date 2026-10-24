import S9StoredZeroFourSameAlphaV1
import S9SourceStoredRowGuardsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9SourceStoredRowsSameAlphaV1
open AspisR1Stage2
open AspisR1S9Stage2NativeFinishSlotsV1
open AspisR1S9ResumeConstructorInputsCanonicalV1
open AspisR1S9FinishActualConstructorSlotV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- Both stored outputs are taken from the SAME supplied StoredRows and parts.
The one supplied actual alpha pair is used for both meanings. -/
theorem stored_rows_same_alpha
    (self : AspisR1S9Stage2NativeFinishSlotsV1.Weights) (selected : Slice SW) (f : Slice U8)
    (kappa nativeOut : NW) (parts k : Array NW 7#usize) (a0 a1 : NW)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (halpha : ∀ i x,Slice.index_usize (sourceSliceToNative selected) i=.ok x →
      AspisR1S9ActualPairWideCanonicalV1.Canonical x)
    (hrows : AspisR1S9SourceStoredRowGuardsV1.StoredRows self selected f kappa nativeOut parts k hspan)
    (ha0 : Slice.index_usize (sourceSliceToNative selected) 0#usize=.ok a0)
    (ha1 : Slice.index_usize (sourceSliceToNative selected) 1#usize=.ok a1) :
    AspisR1S9StoredZeroFourSameAlphaV1.Meanings self f parts a0 a1 := by
  rcases hrows with ⟨htrace,hzero,hfour⟩ | ⟨htrace,hzero,hfour⟩
  · exact AspisR1S9StoredZeroFourSameAlphaV1.paired_stored_rows_same_alpha true
      self (sourceSliceToNative selected) f parts a0 a1 hspan halpha hzero hfour ha0 ha1
  · exact AspisR1S9StoredZeroFourSameAlphaV1.paired_stored_rows_same_alpha false
      self (sourceSliceToNative selected) f parts a0 a1 hspan halpha hzero hfour ha0 ha1

/-- The existing strict-source reader/constructor/selection theorem supplies
canonicality internally. No independent canonical/model/input-stream premise
is added to the actual source event. -/
theorem source_resume_stored_rows_same_alpha {H : Type}
    (ops : ResumeOps) (inst : aspis_core.digest.Digest32 H)
    (checkpoint proof publicBytes : Slice U8) (hash : H)
    (p : verifier.Prepared) (resumeAcc : verifier.Accumulator)
    (self : AspisR1S9Stage2NativeFinishSlotsV1.Weights) (selected : Slice SW) (f : Slice U8)
    (nativeOut : NW) (parts k : Array NW 7#usize) (a0 a1 : NW)
    (hresume : verifier.resumeWithOps
      (AspisR1S9CurrentReaderCheckpointAdoptionV1.withCurrentCheckpointReaders ops)
      inst checkpoint proof publicBytes transport.Variant.S2 hash=.ok (.Ok (p,resumeAcc)))
    (hnew : actualNewWeightsSlot (stageVariant p.variant)
      (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stageQM p.semantic_alpha)
      (AspisR1S9Stage2NativeFinishSlotsV1.mapArray stagePoint p.z)=.ok (.Ok self))
    (hselected : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice SW)) p.alpha {«end»:=2#usize}=.ok selected)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (hrows : AspisR1S9SourceStoredRowGuardsV1.StoredRows self selected f
      (sourceToNative p.kappa) nativeOut parts k hspan)
    (ha0 : Slice.index_usize (sourceSliceToNative selected) 0#usize=.ok a0)
    (ha1 : Slice.index_usize (sourceSliceToNative selected) 1#usize=.ok a1) :
    AspisR1S9StoredZeroFourSameAlphaV1.Meanings self f parts a0 a1 := by
  obtain ⟨hs2,he,halpha⟩ := AspisR1S9SourceStoredRowGuardsV1.strict_source_stored_row_guards
    ops inst checkpoint proof publicBytes hash p resumeAcc self selected hresume hnew hselected
  exact stored_rows_same_alpha self selected f (sourceToNative p.kappa) nativeOut
    parts k a0 a1 hspan halpha hrows ha0 ha1

#print axioms stored_rows_same_alpha
#print axioms source_resume_stored_rows_same_alpha
end AspisR1S9SourceStoredRowsSameAlphaV1
