import PAln_SequenceRead
import PAln_SubSlice
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_OpeningDecode
open AspisV8R19.DuplexFrames OraclePortCompactDraft
open PAln_RowBounds PAln_SubSlice

theorem framed_eq (b : Bytes) : framed b=LengthFrameCodec.frame b := by
  simp only [framed,LengthFrameCodec.frame,PSem_Validation.length_encoding]

theorem gamma (p : Parsed) (length : p.wire.length=57607) (scan : scan p.wire) :
    ∃ value, OpeningRecordCodec.decode .gamma (rowBytes p 27)=some value := by
  have len : (slice p.wire 7031 464).length=16*29 := slice_length _ _ _ (by omega)
  obtain ⟨values,encoded⟩ := PAln_SequenceRead.low_encode_exists 29 _ len scan.1
  refine ⟨values,?_⟩
  have row : rowBytes p 27=framed (expand 29 (slice p.wire 7031 464)) := by simp [rowBytes]
  rw [row,framed_eq,← encoded]
  exact OpeningRecordCodec.decode_encode values

theorem kappa (p : Parsed) (length : p.wire.length=57607) (scan : scan p.wire) :
    ∃ value, OpeningRecordCodec.decode .kappa (rowBytes p 28)=some value := by
  have region : (slice p.wire 7495 256).length=256 := slice_length _ _ _ (by omega)
  have checked := canonical_slice (slice p.wire 7495 256) 0 32 scan.2.1
    (by decide) (by decide) (by omega)
  rw [nested _ _ _ _ _ (by decide)] at checked
  have len : (slice p.wire 7495 32).length=32 := slice_length _ _ _ (by omega)
  obtain ⟨value,decoded⟩ := PAln_FieldRead.wide_exists _ len checked
  have encoded := FoldedLeafCodec.encodeWide_of_decode _ value decoded
  refine ⟨value,?_⟩
  have row : rowBytes p 28=framed (slice p.wire 7495 32) := by simp [rowBytes]
  rw [row,framed_eq,← encoded]
  exact OpeningRecordCodec.decode_encode value

theorem first (p : Parsed) (length : p.wire.length=57607) (scan : scan p.wire) :
    ∃ value, OpeningRecordCodec.decode .first (rowBytes p 29)=some value := by
  have region : (slice p.wire 7495 256).length=256 := slice_length _ _ _ (by omega)
  have checked := canonical_slice (slice p.wire 7495 256) 32 224 scan.2.1
    (by decide) (by decide) (by omega)
  rw [nested _ _ _ _ _ (by decide)] at checked
  have len : (slice p.wire 7527 224).length=32*7 := slice_length _ _ _ (by omega)
  obtain ⟨values,encoded⟩ := PAln_SequenceRead.wide_encode_exists 7 _ len checked
  refine ⟨values,?_⟩
  have row : rowBytes p 29=framed (slice p.wire 7527 224) := by simp [rowBytes]
  rw [row,framed_eq,← encoded]
  exact OpeningRecordCodec.decode_encode values

#print axioms framed_eq
#print axioms gamma
#print axioms kappa
#print axioms first
end AspisR1.PAln_OpeningDecode
end
