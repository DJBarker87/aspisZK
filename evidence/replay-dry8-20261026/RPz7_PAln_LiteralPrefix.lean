import RPz7_PAln_Records
import RPz7_PAln_Ready
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_LiteralPrefix
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.TranscriptView OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun

theorem semantic_read (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (aligned : Aligned p tr)
    (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic)
    (typed : ∃ decoded,SemanticPrefixCodec.decodeFrom 0 (p.semantic.take 25)=some decoded)
    (ordinary : ∀ i,i<31 → ∃ value,LiteralChallengeRead.ordinaryAt (typedRows p q tr) i=some value) :
    ∃ semantic, LiteralSemanticPrefix.read LiteralOpeningView.eK 0
      ((typedRows p q tr).take 25)=some semantic := by
  have ready : PAln_SemanticRead.Ready 0 ((typedRows p q tr).take 25) := by
    apply PAln_Ready.of_slots
    · intro i entry slot
      have bound := (List.getElem?_eq_some_iff.mp slot).choose
      have below : i<25 := by simp only [List.length_take] at bound;omega
      have source : (typedRows p q tr)[i]?=some entry := by
        simpa only [List.getElem?_take,if_pos below] using slot
      simpa only [Nat.zero_add] using PAln_Ready.restored_valid p q tr aligned i (by omega) entry source
    · intro i entry slot
      have bound := (List.getElem?_eq_some_iff.mp slot).choose
      have below : i<25 := by simp only [List.length_take] at bound;omega
      have source : (typedRows p q tr)[i]?=some entry := by
        simpa only [List.getElem?_take,if_pos below] using slot
      obtain ⟨value,read⟩ := ordinary i (by omega)
      obtain ⟨m,state,actual⟩ := LiteralChallengeRead.ordinaryAt_success _ i value read
      have same := Option.some.inj (source.symm.trans actual)
      exact ⟨value,congrArg (fun entry => entry.2.1) same⟩
  obtain ⟨decoded,decode⟩ := typed
  have records := PAln_Records.records_take p q tr aligned rows
  rw [← records] at decode
  exact PAln_SemanticRead.read_of_decode _ _ _ ready decoded decode

#print axioms semantic_read
end AspisR1.PAln_LiteralPrefix
end
