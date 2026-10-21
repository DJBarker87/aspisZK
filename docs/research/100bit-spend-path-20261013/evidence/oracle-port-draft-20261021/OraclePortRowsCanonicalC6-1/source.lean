import OraclePortObservationTransportC6

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRowsCanonicalC6
open LiteralAcceptanceTerminal CanonicalCutEnrichedTranscript
open OraclePortStoredDecisionDraftC4 OraclePortReaderPlumbingC6

theorem enrich_restore (w v : Words) (row : Nat) (m : RawCutTranscriptRun.ErasedMessage) :
    enrichMessage w (restore v row m) = restore w row m := by
  cases m with
  | initial root => rfl
  | payload b => by_cases h2 : row = 2 <;> by_cases h30 : row = 30 <;>
      simp only [restore,h2,h30,ite_true,ite_false,enrichMessage]

theorem restore_valid (w : Words) (row : Nat) (m : LiteralTranscript.Message)
    (valid : LiteralTranscript.valid row m) : restore w row (LiteralTranscript.erase m) = enrichMessage w m := by
  cases m with
  | initial root word => rfl
  | payload b =>
    by_cases h2 : row = 2
    · subst row; simp only [LiteralTranscript.valid] at valid
    · by_cases h30 : row = 30
      · subst row; simp only [LiteralTranscript.valid] at valid
      · simp only [LiteralTranscript.erase,restore,if_neg h2,if_neg h30,enrichMessage]
  | c2 b word =>
    have eq := LiteralSemanticPayloadBridge.valid_c2_row row b word valid
    subst row
    rfl
  | second b word =>
    by_cases eq : row = 30
    · subst row; rfl
    · simp [LiteralTranscript.valid,eq] at valid

/-- The required row identity is restoration followed by enrichment, never
an assertion that candidate and recovered whole words are equal. -/
theorem rows (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (w : Words) (P : LiteralTranscript.Prefix)
    (valid : ∀ n (bound : n < P.rounds.length), LiteralTranscript.valid n (P.rounds[n]'bound).1) :
    reword w (typedRows p q (LiteralTranscript.erasePrefix P)) = enrichRounds w P.rounds := by
  apply List.ext_getElem
  · simp only [reword,typedRows,LiteralTranscript.erasePrefix,enrichRounds,List.length_map,List.length_mapIdx]
  · intro n hn hm
    simp only [reword,typedRows,LiteralTranscript.erasePrefix,enrichRounds,List.getElem_map,List.getElem_mapIdx]
    apply Prod.ext
    · rw [enrich_restore]
      exact restore_valid w n _ (valid n (by simpa only [reword,typedRows,LiteralTranscript.erasePrefix,
        List.length_map,List.length_mapIdx] using hn))
    · rfl

#print axioms enrich_restore
#print axioms restore_valid
#print axioms rows
end AspisR1.OraclePortRowsCanonicalC6
end
