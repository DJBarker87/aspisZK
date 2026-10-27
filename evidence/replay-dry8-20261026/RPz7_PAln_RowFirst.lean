import RPz7_PAln_OpeningDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_RowFirst
open AspisV8R19.DuplexFrames OraclePortCompactDraft
open PAln_RowBounds PAln_SubSlice PAln_OpeningDecode
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
  exact OpeningRecordCodec.decode_encode (row := .first) values


#print axioms first
end AspisR1.PAln_RowFirst
end
