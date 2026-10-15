import R1LiteralTranscript

/-! An index-level view of ordinary literal challenges. This is list plumbing
for later prefix arguments; it makes no cryptographic or source claim. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralChallengeRead

open AspisR1.LiteralTranscript
open AspisR1.TranscriptView

abbrev E := LiteralTranscript.E

/-- The ordinary challenge value at an index, if the indexed transcript
entry carries an ordinary challenge. -/
def ordinaryAt (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (i : Nat) : Option E :=
  rs[i]?.bind fun mc =>
    match mc.2.1 with
    | Value.ordinary value => some value
    | Value.queries _ => none

theorem ordinaryAt_append (rs tail : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (i : Nat) (hi : i < rs.length) :
    ordinaryAt (rs ++ tail) i = ordinaryAt rs i := by
  simp only [ordinaryAt, List.getElem?_append_left hi]

theorem ordinaryAt_success
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (i : Nat) (value : E) (h : ordinaryAt rs i = some value) :
    ∃ message state,
      rs[i]? = some (message, (Value.ordinary value, state)) := by
  unfold ordinaryAt at h
  cases hget : rs[i]? with
  | none => simp [hget] at h
  | some entry =>
      rcases entry with ⟨message, challenge⟩
      rcases challenge with ⟨tag, state⟩
      cases tag with
      | ordinary actual =>
          simp [hget] at h
          subst value
          exact ⟨message, state, hget⟩
      | queries result =>
          simp [hget] at h

#print axioms ordinaryAt_append
#print axioms ordinaryAt_success

end AspisR1.LiteralChallengeRead
end
