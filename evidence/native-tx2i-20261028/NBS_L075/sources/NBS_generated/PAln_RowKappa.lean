import PAln_OpeningDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_RowKappa
open AspisV8R19.DuplexFrames OraclePortCompactDraft
open PAln_RowBounds PAln_SubSlice PAln_OpeningDecode
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
  exact OpeningRecordCodec.decode_encode (row := .kappa) value


#print axioms kappa
end AspisR1.PAln_RowKappa
end
