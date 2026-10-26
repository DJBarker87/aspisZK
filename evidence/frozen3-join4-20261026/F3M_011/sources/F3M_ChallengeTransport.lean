import F3M_ReaderChallenges
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_ChallengeTransport

theorem restored (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (P : LiteralTranscript.Prefix) :
    F3M_ReaderChallenges.ordinaryValues (OraclePortStoredDecisionDraftC4.typedRows p q
      (LiteralTranscript.erasePrefix P))=F3M_ReaderChallenges.ordinaryValues P.rounds := by
  apply List.ext_getElem
  · simp only [F3M_ReaderChallenges.ordinaryValues,List.length_map,
      OraclePortStoredDecisionDraftC4.typedRows,List.length_mapIdx,LiteralTranscript.erasePrefix,List.length_map]
  · intro j hj hk
    simp only [F3M_ReaderChallenges.ordinaryValues,List.getElem_map,
      OraclePortStoredDecisionDraftC4.typedRows,List.getElem_mapIdx,LiteralTranscript.erasePrefix,List.getElem_map]

#print axioms restored
end AspisR1.F3M_ChallengeTransport
end
