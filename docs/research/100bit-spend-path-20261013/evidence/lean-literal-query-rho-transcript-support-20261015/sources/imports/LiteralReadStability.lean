import R1LiteralMatchingData
import R1LiteralChallengeRead

/-! Appending entries after the last inspected index preserves the existing
literal opening/matching readers. These are list-coherence facts only. -/
set_option autoImplicit false

namespace AspisR1.LiteralReadStability

open AspisR1.LiteralTranscript

theorem openingView_append_stable
    (rs tail : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (h : 26 < rs.length) :
    LiteralOpeningView.read (rs ++ tail) = LiteralOpeningView.read rs := by
  have htake : (rs ++ tail).take 25 = rs.take 25 := by
    simp only [List.take_append, Nat.sub_eq_zero_of_le (show 25 ≤ rs.length by omega),
      List.take_zero, List.append_nil]
  have hlen : (rs.take 25).length = 25 := by
    simp only [List.length_take, Nat.min_eq_left (show 25 ≤ rs.length by omega)]
  cases hc1 : LiteralTranscript.c1At rs <;>
    cases hc2 : LiteralTranscript.c2At rs
  all_goals
    simp only [LiteralOpeningView.read, htake, hlen, dif_pos,
      LiteralTranscript.c1At_append rs tail (by omega),
      LiteralTranscript.c2At_append rs tail (by omega),
      LiteralChallengeRead.ordinaryAt_append rs tail 25 (by omega),
      LiteralChallengeRead.ordinaryAt_append rs tail 26 h,
      hc1, hc2, Option.bind_eq_bind, Option.bind_none, Option.bind_some]
  split
  · rename_i ha
    split
    · rfl
    · rename_i b hb
      have hfalse : some b = none := hb.symm.trans
        ((congrArg (LiteralSemanticPrefix.read LiteralOpeningView.eK 0) htake).symm.trans ha)
      contradiction
  · rename_i a ha
    split
    · rename_i hb
      have hfalse : some a = none := ha.symm.trans
        ((congrArg (LiteralSemanticPrefix.read LiteralOpeningView.eK 0) htake).trans hb)
      contradiction
    · rename_i b hb
      have hab : a = b := Option.some.inj (ha.symm.trans
        ((congrArg (LiteralSemanticPrefix.read LiteralOpeningView.eK 0) htake).trans hb))
      subst b
      rfl

theorem matchingData_append_stable
    (rs tail : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (h : 31 < rs.length) :
    LiteralMatchingData.read (rs ++ tail) = LiteralMatchingData.read rs := by
  unfold LiteralMatchingData.read
  rw [openingView_append_stable rs tail (by omega),
    LiteralOpeningStages.readSecond_append_stable rs tail (by omega),
    LiteralOpeningStages.readAt_append_stable rs tail 31 _ (by omega),
    LiteralTranscript.vAt_append rs tail (by omega),
    LiteralChallengeRead.ordinaryAt_append rs tail 27 (by omega),
    LiteralChallengeRead.ordinaryAt_append rs tail 28 (by omega),
    LiteralChallengeRead.ordinaryAt_append rs tail 29 (by omega),
    LiteralChallengeRead.ordinaryAt_append rs tail 30 (by omega)]

#print axioms openingView_append_stable
#print axioms matchingData_append_stable

end AspisR1.LiteralReadStability
