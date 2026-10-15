import R1SelectedSemanticPrefix

/-! Challenge-list consequences of successful selected semantic-prefix
decoding. These are list-view equalities only. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedSemanticPrefixFacts

open R0P.Mask
open AspisR1.SemanticPayloadView
open AspisR1.SelectedSemanticPrefix

abbrev E := SelectedSemanticPrefix.E
abbrev State := SelectedSemanticPrefix.State
abbrev Message := SelectedSemanticPrefix.Message

theorem read_challenges (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (offset : Nat) (xs : List (Message × E)) (out : List (SemMsgZ E × E))
    (h : SelectedSemanticPrefix.read recoverC2 offset xs = some out) :
    out.map Prod.snd = xs.map Prod.snd := by
  induction xs generalizing offset out with
  | nil =>
      simp [SelectedSemanticPrefix.read] at h
      subst out
      rfl
  | cons item rest ih =>
      rcases item with ⟨message, challenge⟩
      by_cases hoff : offset < 25
      · cases hdecode : SemanticRecordCodec.decode ⟨offset, hoff⟩ message.val with
        | none => simp [SelectedSemanticPrefix.read, hoff, hdecode] at h
        | some payload =>
          cases htail : SelectedSemanticPrefix.read recoverC2 (offset + 1) rest with
          | none => simp [SelectedSemanticPrefix.read, hoff, hdecode, htail] at h
          | some tail =>
              have hout :
                  (SemanticPayloadView.toMessage recoverC2 payload.val, challenge) :: tail = out := by
                simpa [SelectedSemanticPrefix.read, hoff, hdecode, htail] using h
              cases hout
              have hrest := ih (offset + 1) tail htail
              simpa using congrArg (List.cons challenge) hrest
      · simp [SelectedSemanticPrefix.read, hoff] at h

def lift (pairs : List (SemMsgZ E × E)) : List (MsgZ E × ChalZ E) :=
  pairs.map fun pair => (R0C.SemStatement.Msg.semantic pair.1, R0C.SemStatement.Chal.semantic pair.2)

theorem semChalsZ_lift (pairs : List (SemMsgZ E × E)) :
    semChalsZ (lift pairs) = some (pairs.map Prod.snd) := by
  simpa [lift] using (R0P.Mask.semChalsZ_of_pairs pairs)

theorem semChalsZ_read (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (offset : Nat) (xs : List (Message × E)) (out : List (SemMsgZ E × E))
    (h : SelectedSemanticPrefix.read recoverC2 offset xs = some out) :
    semChalsZ (lift out) = some (xs.map Prod.snd) := by
  rw [semChalsZ_lift]
  rw [read_challenges recoverC2 offset xs out h]

#print axioms read_challenges
#print axioms semChalsZ_lift
#print axioms semChalsZ_read

end AspisR1.SelectedSemanticPrefixFacts
end
