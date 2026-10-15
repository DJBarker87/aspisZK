import R1LiteralReadStability

/-! The row-31 query sampler cannot change the matching support it is testing:
the data reader uses that row's message, but not that row's challenge. This is
prefix coherence only, separate from acceptance and query-sampler validity. -/
set_option autoImplicit false
namespace AspisR1.LiteralQueryContext

open LiteralTranscript

theorem current_readAt_challenge_independent {A : Type}
    (rs : List (Message × Challenge)) (m : Message) (c c' : Challenge)
    (decode : AspisV8R19.DuplexFrames.Bytes → Option A) :
    LiteralOpeningStages.readAt (rs ++ [(m, c)]) rs.length decode =
      LiteralOpeningStages.readAt (rs ++ [(m, c')]) rs.length decode := by
  simp only [LiteralOpeningStages.readAt, List.getElem?_append,
    Nat.lt_irrefl, if_false, Nat.sub_self, List.getElem?_cons_zero, Option.bind_some]

theorem matchingData_challenge_independent
    (rs : List (Message × Challenge)) (m : Message) (c c' : Challenge)
    (hlen : rs.length = 31) :
    LiteralMatchingData.read (rs ++ [(m, c)]) =
      LiteralMatchingData.read (rs ++ [(m, c')]) := by
  have hlast := current_readAt_challenge_independent rs m c c'
    (OpeningRecordCodec.decode .final)
  rw [hlen] at hlast
  unfold LiteralMatchingData.read
  rw [LiteralReadStability.openingView_append_stable rs _ (by omega),
    LiteralReadStability.openingView_append_stable rs _ (by omega),
    LiteralOpeningStages.readSecond_append_stable rs _ (by omega),
    LiteralOpeningStages.readSecond_append_stable rs _ (by omega), hlast,
    LiteralTranscript.vAt_append rs _ (by omega),
    LiteralTranscript.vAt_append rs _ (by omega),
    LiteralChallengeRead.ordinaryAt_append rs _ 27 (by omega),
    LiteralChallengeRead.ordinaryAt_append rs _ 27 (by omega),
    LiteralChallengeRead.ordinaryAt_append rs _ 28 (by omega),
    LiteralChallengeRead.ordinaryAt_append rs _ 28 (by omega),
    LiteralChallengeRead.ordinaryAt_append rs _ 29 (by omega),
    LiteralChallengeRead.ordinaryAt_append rs _ 29 (by omega),
    LiteralChallengeRead.ordinaryAt_append rs _ 30 (by omega),
    LiteralChallengeRead.ordinaryAt_append rs _ 30 (by omega)]

theorem beforeRho_ext_eq_atQuery (P : Prefix) (m : Message) (c : Challenge)
    (hround : P.round = 31) :
    LiteralMatchingData.beforeRho (P.ext m c) = LiteralMatchingData.atQuery P m := by
  exact matchingData_challenge_independent P.rounds m c _ hround

#print axioms current_readAt_challenge_independent
#print axioms matchingData_challenge_independent
#print axioms beforeRho_ext_eq_atQuery

end AspisR1.LiteralQueryContext
