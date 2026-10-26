import F3L_MatchingChallenges
import F3L_EraseIndex
import F3L_RestoreChallenge
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_MatchingFromEntries
open AspisV8R19.SourceDuplexStep

theorem fields (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (Q : LiteralTranscript.Prefix) (d : MatchingSupport.Data LiteralTranscript.E)
    (messages : Fin 4 → LiteralTranscript.Message) (values : Fin 4 → LiteralTranscript.E)
    (states : Fin 4 → State)
    (entries : ∀ j : Fin 4,Q.rounds[27+j.val]?=some
      (messages j,(TranscriptView.Value.ordinary (values j),states j)))
    (read : LiteralMatchingData.read (OraclePortStoredDecisionDraftC4.typedRows p q
      (LiteralTranscript.erasePrefix Q))=some d) :
    d.gamma=values 0 ∧ d.kappa=values 1 ∧ d.alpha0=values 2 ∧ d.alpha1=values 3 := by
  have source (j : Fin 4) := F3L_RestoreChallenge.ordinary p q (LiteralTranscript.erasePrefix Q)
    (27+j.val) _ (values j) (states j) (F3L_EraseIndex.entry Q _ _ _ (entries j))
  have model := F3L_MatchingChallenges.fields _ d read
  exact ⟨Option.some.inj (model.1.symm.trans (source 0)),
    Option.some.inj (model.2.1.symm.trans (source 1)),
    Option.some.inj (model.2.2.1.symm.trans (source 2)),
    Option.some.inj (model.2.2.2.symm.trans (source 3))⟩

#print axioms fields
end AspisR1.F3L_MatchingFromEntries
end
