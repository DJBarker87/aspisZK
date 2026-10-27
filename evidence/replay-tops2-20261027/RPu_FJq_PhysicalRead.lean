import RPz7_PAln_AlignedRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_PhysicalRead
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun
/-- Invert the reader on the SAME aligned physical message; no second literal
payload success or arbitrary byte equality is supplied. -/
theorem value {A : Type} (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (aligned : Aligned p tr) (row : Nat) (positive : 0<row) (below : row<33)
    (decode : Bytes → Option A) (out : A)
    (run : LiteralOpeningStages.readAt (typedRows p q tr) row decode=some out) :
    decode (rowBytes p row)=some out := by
  obtain ⟨b,c,slot,same⟩:=aligned.2.2.2.2 row positive below
  have valid:=PAln_AlignedRead.payload_valid (words p q) row b positive below
  simp only [LiteralOpeningStages.readAt,typedRows,List.getElem?_mapIdx,slot,
    Option.map_some,Option.bind_some,if_pos valid,restore_erases] at run
  rw [same] at run
  exact run
#print axioms value
end AspisR1.FJq_PhysicalRead
end
