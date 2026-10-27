import RPz7_PAln_SequenceRead
import RPz7_PAln_SubSlice
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
  exact OpeningRecordCodec.decode_encode (row := .gamma) values

#print axioms framed_eq
#print axioms gamma
end AspisR1.PAln_OpeningDecode
end
