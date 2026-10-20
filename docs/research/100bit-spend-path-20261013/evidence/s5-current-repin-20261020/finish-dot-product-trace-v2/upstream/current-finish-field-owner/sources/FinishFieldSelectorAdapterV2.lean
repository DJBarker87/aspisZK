import CurrentFinishArithmetic
import WeightsFieldSuccess
import ExtractedRecordByteCanonicality

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CurrentWide.Proof

abbrev RecordWide := AspisR1RecordParser.field.wide_exact.WideExact
abbrev RecordQM := AspisR1RecordParser.field.QM31
abbrev RecordCM := AspisR1RecordParser.field.CM31
abbrev RecordM := AspisR1RecordParser.field.M31

def recordMToFinish (x : RecordM) : AspisR1FinishRelationCurrent.aspis_core.field.M31 := x

def recordCMToFinish (x : RecordCM) : FinishCM :=
  ⟨recordMToFinish x.a, recordMToFinish x.b⟩

def recordQMToFinish (x : RecordQM) : FinishQM :=
  ⟨recordCMToFinish x.c0, recordCMToFinish x.c1⟩

def recordWideToFinish (x : RecordWide) : FinishE :=
  ⟨recordQMToFinish x.c0, recordQMToFinish x.c1⟩

private theorem packed_record_canonical (arr : Array U8 32#usize)
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

theorem record_field_finish_canonical (bytes : Slice U8) (i : Usize)
    (value : RecordWide)
    (h : AspisR1WeightsFieldCurrent.weights.field
      AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes i = .ok value) :
    CanonicalFinish (recordWideToFinish value) := by
  obtain ⟨_, _, _, selected, _, _, _, _, hdecode⟩ :=
    AspisR1WeightsFieldCurrent.WeightsFieldSuccess.checked_slice_decode
      AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes i value h
  obtain ⟨_, arr, _, hc, hpack⟩ :=
    AspisR1.ExtractedRecordByteCanonicality.slice_success selected value hdecode
  rw [hpack]
  exact packed_record_canonical arr hc

#print axioms packed_record_canonical
#print axioms record_field_finish_canonical

end AspisR1CurrentWide.Proof
