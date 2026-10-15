import R1LiteralOpeningStages

/-! The staged payload and committed-word readers depend on each transcript
entry's message component, not its challenge component. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralStageMessageCongr

open AspisR1.LiteralTranscript
open AspisR1.LiteralOpeningStages
open AspisR1.InitialWalk
open AspisR1.OpeningRecordCodec

private theorem getElem_message_eq
    (rs rs' : List (Message × Challenge)) (i : Nat)
    (h : rs.map Prod.fst = rs'.map Prod.fst) :
    (rs[i]?).map Prod.fst = (rs'[i]?).map Prod.fst := by
  have hget := congrArg (fun xs : List Message => xs[i]?) h
  simpa only [List.getElem?_map] using hget

theorem readAt_congr_messages {A : Type}
    (rs rs' : List (Message × Challenge)) (i : Nat)
    (decode : Bytes → Option A)
    (h : rs.map Prod.fst = rs'.map Prod.fst) :
    readAt rs i decode = readAt rs' i decode := by
  have hm := getElem_message_eq rs rs' i h
  cases hleft : rs[i]? with
  | none =>
      have hright : rs'[i]? = none := by
        cases hcase : rs'[i]? with
        | none => rfl
        | some q => simp [hleft, hcase] at hm
      simp [readAt, hleft, hright]
  | some q =>
      cases hright : rs'[i]? with
      | none => simp [hleft, hright] at hm
      | some q' =>
          rcases q with ⟨m, c⟩
          rcases q' with ⟨m', c'⟩
          have hmsg : m = m' := by simpa [hleft, hright] using hm
          subst m'
          simp [readAt, hleft, hright]

theorem readGamma_congr_messages
    (rs rs' : List (Message × Challenge))
    (h : rs.map Prod.fst = rs'.map Prod.fst) :
    readGamma rs = readGamma rs' := by
  unfold readGamma
  rw [readAt_congr_messages rs rs' 25 _ h,
    readAt_congr_messages rs rs' 26 _ h,
    readAt_congr_messages rs rs' 27 _ h]

theorem readKappa_congr_messages
    (rs rs' : List (Message × Challenge))
    (h : rs.map Prod.fst = rs'.map Prod.fst) :
    readKappa rs = readKappa rs' := by
  unfold readKappa
  rw [readGamma_congr_messages rs rs' h,
    readAt_congr_messages rs rs' 28 _ h]

theorem readFirst_congr_messages
    (rs rs' : List (Message × Challenge))
    (h : rs.map Prod.fst = rs'.map Prod.fst) :
    readFirst rs = readFirst rs' := by
  unfold readFirst
  rw [readKappa_congr_messages rs rs' h,
    readAt_congr_messages rs rs' 29 _ h]

theorem readSecond_congr_messages
    (rs rs' : List (Message × Challenge))
    (h : rs.map Prod.fst = rs'.map Prod.fst) :
    readSecond rs = readSecond rs' := by
  unfold readSecond
  rw [readFirst_congr_messages rs rs' h,
    readAt_congr_messages rs rs' 30 _ h]

theorem vAt_congr_messages
    (rs rs' : List (Message × Challenge))
    (h : rs.map Prod.fst = rs'.map Prod.fst) :
    LiteralTranscript.vAt rs = LiteralTranscript.vAt rs' := by
  unfold LiteralTranscript.vAt
  have hm := getElem_message_eq rs rs' 30 h
  cases hleft : rs[30]? with
  | none =>
      have hright : rs'[30]? = none := by
        cases hcase : rs'[30]? with
        | none => rfl
        | some q => simp [hleft, hcase] at hm
      simp [hleft, hright]
  | some q =>
      cases hright : rs'[30]? with
      | none => simp [hleft, hright] at hm
      | some q' =>
          rcases q with ⟨m, c⟩
          rcases q' with ⟨m', c'⟩
          have hmsg : m = m' := by simpa [hleft, hright] using hm
          subst m'
          simp [hleft, hright]

#print axioms readAt_congr_messages
#print axioms readGamma_congr_messages
#print axioms readKappa_congr_messages
#print axioms readFirst_congr_messages
#print axioms readSecond_congr_messages
#print axioms vAt_congr_messages

end AspisR1.LiteralStageMessageCongr
end
