import RPz7_F3L_EraseIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_AlignedPrefix
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft
attribute [local irreducible] F3J_InputRows.proof

theorem aligned (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (Q : LiteralTranscript.Prefix)
    (tag : Q.statement.tag=p.wire[8]?.getD 0)
    (parsedPublic : ∃ decoded,SemanticPublicWire.parsePublic Q.statement.pubBytes=some decoded)
    (length : Q.rounds.length=33) (rootBytes : bytes root=root0 p)
    (messages : ∀ row,row<33 → ∃ c,Q.rounds[row]?=some (F3J_InputRows.proof p root w bound row,c)) :
    Aligned p (LiteralTranscript.erasePrefix Q) := by
  refine ⟨tag,parsedPublic,?_,?_,?_⟩
  · simpa only [LiteralTranscript.erasePrefix,List.length_map] using length
  · obtain ⟨c,entry⟩ := messages 0 (by decide)
    refine ⟨root,c,?_,rootBytes⟩
    have erased := F3L_EraseIndex.entry Q 0 _ c entry
    rw [F3J_InputRows.erased,if_pos rfl] at erased
    exact erased
  · intro row positive below
    obtain ⟨c,entry⟩ := messages row below
    refine ⟨⟨rowBytes p row,bound row⟩,c,?_,rfl⟩
    have erased := F3L_EraseIndex.entry Q row _ c entry
    rw [F3J_InputRows.erased,if_neg (by omega)] at erased
    exact erased

#print axioms aligned
end AspisR1.F3L_AlignedPrefix
end
