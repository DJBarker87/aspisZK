import F3M_OpeningReader
import F3L_EraseIndex
import F3L_RestoreChallenge
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_CircleReader
open AspisV8R19.SourceDuplexStep

theorem first (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (Q : LiteralTranscript.Prefix) (v : LiteralOpeningView.View)
    (m : LiteralTranscript.Message) (value : LiteralTranscript.E) (state : State)
    (entry : Q.rounds[25]?=some (m,(TranscriptView.Value.ordinary value,state)))
    (read : LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q
      (LiteralTranscript.erasePrefix Q))=some v) : v.challenge25=value := by
  have source := F3L_RestoreChallenge.ordinary p q (LiteralTranscript.erasePrefix Q) 25 _ value state
    (F3L_EraseIndex.entry Q 25 m _ entry)
  exact Option.some.inj ((F3M_OpeningReader.components _ v read).2.1.symm.trans source)

theorem second (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (Q : LiteralTranscript.Prefix) (v : LiteralOpeningView.View)
    (m : LiteralTranscript.Message) (value : LiteralTranscript.E) (state : State)
    (entry : Q.rounds[26]?=some (m,(TranscriptView.Value.ordinary value,state)))
    (read : LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q
      (LiteralTranscript.erasePrefix Q))=some v) : v.challenge26=value := by
  have source := F3L_RestoreChallenge.ordinary p q (LiteralTranscript.erasePrefix Q) 26 _ value state
    (F3L_EraseIndex.entry Q 26 m _ entry)
  exact Option.some.inj ((F3M_OpeningReader.components _ v read).2.2.1.symm.trans source)

#print axioms first
#print axioms second
end AspisR1.F3M_CircleReader
end
