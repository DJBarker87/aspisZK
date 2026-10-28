import PAln_TypedRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_AlignedRead
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun

theorem payload_valid (w : CanonicalCutEnrichedTranscript.Words) (row : Nat)
    (b : SelectedTranscriptParams.Message) (positive : 0<row) (below : row<33) :
    LiteralTranscript.valid row (restore w row (.payload b)) := by
  by_cases two : row=2
  · subst row; simp [restore,LiteralTranscript.valid]
  · by_cases thirty : row=30
    · subst row; simp [restore,LiteralTranscript.valid]
    · simp [restore,LiteralTranscript.valid,two,thirty,below,show row≠0 by omega]

theorem readAt {A : Type} (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (aligned : Aligned p tr) (row : Nat) (positive : 0<row) (below : row<33)
    (decode : Bytes → Option A) (value : A) (decoded : decode (rowBytes p row)=some value) :
    LiteralOpeningStages.readAt (typedRows p q tr) row decode=some value := by
  obtain ⟨b,c,slot,same⟩ := aligned.2.2.2.2 row positive below
  have valid := payload_valid (words p q) row b positive below
  simp only [LiteralOpeningStages.readAt,typedRows,List.getElem?_mapIdx,slot,
    Option.map_some,Option.bind_some,if_pos valid,restore_erases]
  rw [same]
  exact decoded

theorem words_read (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (aligned : Aligned p tr) :
    LiteralTranscript.c1At (typedRows p q tr)=some (words p q).c1 ∧
    LiteralTranscript.c2At (typedRows p q tr)=some (words p q).c2 ∧
    LiteralTranscript.vAt (typedRows p q tr)=some (words p q).final := by
  obtain ⟨root,c,initial,rootBytes⟩ := aligned.2.2.2.1
  obtain ⟨b2,c2,slot2,_⟩ := aligned.2.2.2.2 2 (by decide) (by decide)
  obtain ⟨b30,c30,slot30,_⟩ := aligned.2.2.2.2 30 (by decide) (by decide)
  simp [LiteralTranscript.c1At,LiteralTranscript.c2At,LiteralTranscript.vAt,
    typedRows,List.getElem?_mapIdx,initial,slot2,slot30,Option.map_some,Option.bind_some,
    restore,if_pos rfl,if_neg (by decide : (30:Nat)≠2)]

#print axioms payload_valid
#print axioms readAt
#print axioms words_read
end AspisR1.PAln_AlignedRead
end
