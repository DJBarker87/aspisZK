import S9OwnedFieldReaderReadbackV1
import FinishFieldSelectorAdapterV2
import ExtractedRecordByteCanonicality

set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide.Proof AspisR1S9OwnedFromLimbsMapV1

namespace AspisR1S9OwnedFieldCanonicalV1

open AspisR1S9OwnedFieldReaderReadbackV1

theorem reader_packed_record_canonical (arr : Array U8 32#usize)
    (hc : ∀ i : Fin 8,
      (AspisR1.ExtractedRecordByteCanonicality.wordLE arr i).val < 2147483647) :
    CanonicalFinish (recordWideToFinish
      (AspisR1.ExtractedRecordLimbCanonicality.packed
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 0)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 1)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 2)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 3)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 4)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 5)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 6)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 7))) := by
  unfold CanonicalFinish CanonicalWide CanonicalQM
  constructor
  · constructor
    · constructor
      · exact by simpa [AspisR1.ExtractedRecordLimbCanonicality.packed,
          recordWideToFinish, recordQMToFinish, recordCMToFinish,
          recordMToFinish, ofFinishE, ofFinishQM, ofFinishCM,
          AspisR1CurrentWide.Proof.toQM, AspisR1CurrentWide.Proof.toCM,
          AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
          AspisR1.ExtractedCurrentTowerAdd.P] using hc ⟨0, by omega⟩
      · exact by simpa [AspisR1.ExtractedRecordLimbCanonicality.packed,
          recordWideToFinish, recordQMToFinish, recordCMToFinish,
          recordMToFinish, ofFinishE, ofFinishQM, ofFinishCM,
          AspisR1CurrentWide.Proof.toQM, AspisR1CurrentWide.Proof.toCM,
          AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
          AspisR1.ExtractedCurrentTowerAdd.P] using hc ⟨1, by omega⟩
    · constructor
      · exact by simpa [AspisR1.ExtractedRecordLimbCanonicality.packed,
          recordWideToFinish, recordQMToFinish, recordCMToFinish,
          recordMToFinish, ofFinishE, ofFinishQM, ofFinishCM,
          AspisR1CurrentWide.Proof.toQM, AspisR1CurrentWide.Proof.toCM,
          AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
          AspisR1.ExtractedCurrentTowerAdd.P] using hc ⟨2, by omega⟩
      · exact by simpa [AspisR1.ExtractedRecordLimbCanonicality.packed,
          recordWideToFinish, recordQMToFinish, recordCMToFinish,
          recordMToFinish, ofFinishE, ofFinishQM, ofFinishCM,
          AspisR1CurrentWide.Proof.toQM, AspisR1CurrentWide.Proof.toCM,
          AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
          AspisR1.ExtractedCurrentTowerAdd.P] using hc ⟨3, by omega⟩
  · constructor
    · constructor
      · exact by simpa [AspisR1.ExtractedRecordLimbCanonicality.packed,
          recordWideToFinish, recordQMToFinish, recordCMToFinish,
          recordMToFinish, ofFinishE, ofFinishQM, ofFinishCM,
          AspisR1CurrentWide.Proof.toQM, AspisR1CurrentWide.Proof.toCM,
          AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
          AspisR1.ExtractedCurrentTowerAdd.P] using hc ⟨4, by omega⟩
      · exact by simpa [AspisR1.ExtractedRecordLimbCanonicality.packed,
          recordWideToFinish, recordQMToFinish, recordCMToFinish,
          recordMToFinish, ofFinishE, ofFinishQM, ofFinishCM,
          AspisR1CurrentWide.Proof.toQM, AspisR1CurrentWide.Proof.toCM,
          AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
          AspisR1.ExtractedCurrentTowerAdd.P] using hc ⟨5, by omega⟩
    · constructor
      · exact by simpa [AspisR1.ExtractedRecordLimbCanonicality.packed,
          recordWideToFinish, recordQMToFinish, recordCMToFinish,
          recordMToFinish, ofFinishE, ofFinishQM, ofFinishCM,
          AspisR1CurrentWide.Proof.toQM, AspisR1CurrentWide.Proof.toCM,
          AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
          AspisR1.ExtractedCurrentTowerAdd.P] using hc ⟨6, by omega⟩
      · exact by simpa [AspisR1.ExtractedRecordLimbCanonicality.packed,
          recordWideToFinish, recordQMToFinish, recordCMToFinish,
          recordMToFinish, ofFinishE, ofFinishQM, ofFinishCM,
          AspisR1CurrentWide.Proof.toQM, AspisR1CurrentWide.Proof.toCM,
          AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
          AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
          AspisR1.ExtractedCurrentTowerAdd.P] using hc ⟨7, by omega⟩

/-- The successful exact owned field reader returns a value that is canonical
in the retained current-finish/current-wide carrier. This uses the exact
selected slice's eight byte-decoded limb bounds and unchanged parser packing. -/
theorem selected_field_success_canonical
    (bytes : Slice U8) (i : Usize) (out : AspisR1S9OwnedFromLimbsMapV1.C)
    (h : AspisR1S9FieldOwnedV1.weights.field bytes i = .ok out) :
    AspisR1CurrentWide.Proof.CanonicalFinish
      (AspisR1CurrentWide.Proof.recordWideToFinish (wideToParser out)) := by
  obtain ⟨selected, arr, hlen, hslice, hc, hpack⟩ :=
    selected_field_success_limb_readback bytes i out h
  rw [hpack]
  exact reader_packed_record_canonical arr hc

#print axioms reader_packed_record_canonical
#print axioms selected_field_success_canonical

end AspisR1S9OwnedFieldCanonicalV1
