import PAln_AlignedRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_AlignedRow
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun

theorem read_iff {A : Type} (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (aligned : Aligned p tr) (row : Nat) (positive : 0<row) (below : row<33)
    (decode : AspisV8R19.DuplexFrames.Bytes → Option A) (value : A) :
    LiteralOpeningStages.readAt (typedRows p q tr) row decode=some value ↔
      decode (rowBytes p row)=some value := by
  obtain ⟨b,c,slot,same⟩ := aligned.2.2.2.2 row positive below
  have valid := PAln_AlignedRead.payload_valid (words p q) row b positive below
  simp only [LiteralOpeningStages.readAt,typedRows,List.getElem?_mapIdx,slot,
    Option.map_some,Option.bind_some,if_pos valid,restore_erases,same]

#print axioms read_iff
end AspisR1.F3P_AlignedRow
end
