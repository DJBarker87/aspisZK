import R1LiteralOpeningCoherence
import R1LiteralReadAtFacts

/-! Deterministic indexing facts for a literal transcript list. These lemmas
only reconstruct its selected prefix/current row/suffix and expose the
constructor/value shape of successful indexed readers. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralIndexedPrefix

open AspisR1.LiteralTranscript
open AspisR1.LiteralOpeningCoherence

theorem take_prefix_round (pub : Public) (rs : List (Message × Challenge))
    (i : Nat) (hi : i < rs.length) :
    (⟨pub, rs.take i⟩ : Prefix).round = i := by
  simp [FS.Prefix.round, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]

theorem full_take_index_drop (pub : Public) (rs : List (Message × Challenge))
    (i : Nat) (hi : i < rs.length) :
    LiteralOpeningCoherence.full (⟨pub, rs.take i⟩ : Prefix)
      (rs[i].1) (rs[i].2) (rs.drop (i + 1)) = rs := by
  unfold LiteralOpeningCoherence.full
  calc
    rs.take i ++ ((rs[i].1, rs[i].2) :: rs.drop (i + 1)) =
        rs.take (i + 1) ++ rs.drop (i + 1) := by
          rw [List.take_succ_eq_append_getElem hi]
          simp [List.append_assoc]
    _ = rs := List.take_append_drop (i + 1) rs

theorem readAt_success_index_valid {A : Type}
    (rs : List (Message × Challenge)) (i : Nat) (hi : i < rs.length)
    (decode : AspisV8R19.DuplexFrames.Bytes → Option A) (value : A)
    (h : LiteralOpeningStages.readAt rs i decode = some value) :
    LiteralTranscript.valid i (rs[i].1) := by
  obtain ⟨m, c, hget, hv⟩ := LiteralReadAtFacts.readAt_success rs i decode value h
  have hm : (rs[i]).1 = m := by
    have hget' := hget
    rw [List.getElem?_eq_getElem hi] at hget'
    exact congrArg Prod.fst (Option.some.inj hget')
  rw [hm]
  exact hv

theorem ordinaryAt_success_index_value
    (rs : List (Message × Challenge)) (i : Nat) (hi : i < rs.length)
    (value : E)
    (h : LiteralChallengeRead.ordinaryAt rs i = some value) :
    (rs[i]).2.1 = TranscriptView.Value.ordinary value := by
  obtain ⟨message, state, hget⟩ := LiteralChallengeRead.ordinaryAt_success rs i value h
  have hentry : rs[i] = (message, (TranscriptView.Value.ordinary value, state)) := by
    have hget' := hget
    rw [List.getElem?_eq_getElem hi] at hget'
    exact Option.some.inj hget'
  rw [hentry]

#print axioms take_prefix_round
#print axioms full_take_index_drop
#print axioms readAt_success_index_valid
#print axioms ordinaryAt_success_index_value

end AspisR1.LiteralIndexedPrefix
end
