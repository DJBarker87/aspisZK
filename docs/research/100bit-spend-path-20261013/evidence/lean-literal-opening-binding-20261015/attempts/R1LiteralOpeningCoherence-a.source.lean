import R1LiteralStageMessageCongr
import R1LiteralReadStability

/-! Earlier opening-event readers agree with the corresponding views of a
completed literal transcript. Only suffix extension and message-only reading
are used; no acceptance or cryptographic premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralOpeningCoherence

open LiteralTranscript

abbrev full (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) := P.rounds ++ ((m,c) :: tail)

theorem openingView_before (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (h : 26 < P.round) :
    LiteralOpeningView.read P.rounds = LiteralOpeningView.read (full P m c tail) :=
  (LiteralReadStability.openingView_append_stable P.rounds ((m,c) :: tail) h).symm

theorem ordinary_before (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (i : Nat) (h : i < P.round) :
    LiteralChallengeRead.ordinaryAt P.rounds i =
      LiteralChallengeRead.ordinaryAt (full P m c tail) i :=
  (LiteralChallengeRead.ordinaryAt_append P.rounds ((m,c) :: tail) i h).symm

theorem gamma_withMessage (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (h : 27 ≤ P.round) :
    LiteralOpeningStages.readGamma (LiteralOpeningEvents.withMessage P m) =
      LiteralOpeningStages.readGamma (full P m c tail) := by
  calc
    _ = LiteralOpeningStages.readGamma (P.rounds ++ [(m,c)]) :=
      LiteralStageMessageCongr.readGamma_congr_messages _ _ (by
        simp [LiteralOpeningEvents.withMessage])
    _ = _ := by
      have hlen : 27 < (P.rounds ++ [(m,c)]).length := by
        change 27 ≤ P.rounds.length at h
        simp only [List.length_append, List.length_singleton]
        omega
      simpa only [full, List.append_assoc, List.singleton_append] using
        (LiteralOpeningStages.readGamma_append_stable (P.rounds ++ [(m,c)]) tail hlen).symm

theorem kappa_withMessage (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (h : 28 ≤ P.round) :
    LiteralOpeningStages.readKappa (LiteralOpeningEvents.withMessage P m) =
      LiteralOpeningStages.readKappa (full P m c tail) := by
  calc
    _ = LiteralOpeningStages.readKappa (P.rounds ++ [(m,c)]) :=
      LiteralStageMessageCongr.readKappa_congr_messages _ _ (by
        simp [LiteralOpeningEvents.withMessage])
    _ = _ := by
      have hlen : 28 < (P.rounds ++ [(m,c)]).length := by
        change 28 ≤ P.rounds.length at h
        simp only [List.length_append, List.length_singleton]
        omega
      simpa only [full, List.append_assoc, List.singleton_append] using
        (LiteralOpeningStages.readKappa_append_stable (P.rounds ++ [(m,c)]) tail hlen).symm

theorem first_withMessage (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (h : 29 ≤ P.round) :
    LiteralOpeningStages.readFirst (LiteralOpeningEvents.withMessage P m) =
      LiteralOpeningStages.readFirst (full P m c tail) := by
  calc
    _ = LiteralOpeningStages.readFirst (P.rounds ++ [(m,c)]) :=
      LiteralStageMessageCongr.readFirst_congr_messages _ _ (by
        simp [LiteralOpeningEvents.withMessage])
    _ = _ := by
      have hlen : 29 < (P.rounds ++ [(m,c)]).length := by
        change 29 ≤ P.rounds.length at h
        simp only [List.length_append, List.length_singleton]
        omega
      simpa only [full, List.append_assoc, List.singleton_append] using
        (LiteralOpeningStages.readFirst_append_stable (P.rounds ++ [(m,c)]) tail hlen).symm

theorem second_withMessage (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (h : 30 ≤ P.round) :
    LiteralOpeningStages.readSecond (LiteralOpeningEvents.withMessage P m) =
      LiteralOpeningStages.readSecond (full P m c tail) := by
  calc
    _ = LiteralOpeningStages.readSecond (P.rounds ++ [(m,c)]) :=
      LiteralStageMessageCongr.readSecond_congr_messages _ _ (by
        simp [LiteralOpeningEvents.withMessage])
    _ = _ := by
      have hlen : 30 < (P.rounds ++ [(m,c)]).length := by
        change 30 ≤ P.rounds.length at h
        simp only [List.length_append, List.length_singleton]
        omega
      simpa only [full, List.append_assoc, List.singleton_append] using
        (LiteralOpeningStages.readSecond_append_stable (P.rounds ++ [(m,c)]) tail hlen).symm

theorem word_withMessage (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (h : 30 ≤ P.round) :
    LiteralTranscript.vAt (LiteralOpeningEvents.withMessage P m) =
      LiteralTranscript.vAt (full P m c tail) := by
  calc
    _ = LiteralTranscript.vAt (P.rounds ++ [(m,c)]) :=
      LiteralStageMessageCongr.vAt_congr_messages _ _ (by
        simp [LiteralOpeningEvents.withMessage])
    _ = _ := by
      have hlen : 30 < (P.rounds ++ [(m,c)]).length := by
        change 30 ≤ P.rounds.length at h
        simp only [List.length_append, List.length_singleton]
        omega
      simpa only [full, List.append_assoc, List.singleton_append] using
        (LiteralTranscript.vAt_append (P.rounds ++ [(m,c)]) tail hlen).symm

theorem readGamma_full (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (h : P.round = 27) :
    LiteralOpeningEvents.readGamma P m = (do
      let context ← LiteralOpeningView.read (full P m c tail)
      let payload ← LiteralOpeningStages.readGamma (full P m c tail)
      pure (⟨context, payload⟩ : LiteralOpeningEvents.Gamma)) := by
  unfold LiteralOpeningEvents.readGamma
  rw [openingView_before P m c tail (by omega), gamma_withMessage P m c tail (by omega)]

theorem readKappa_full (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (h : P.round = 28) :
    LiteralOpeningEvents.readKappa P m = (do
      let context ← LiteralOpeningView.read (full P m c tail)
      let payload ← LiteralOpeningStages.readKappa (full P m c tail)
      let gamma ← LiteralChallengeRead.ordinaryAt (full P m c tail) 27
      pure (⟨⟨context, payload.toGamma⟩, payload, gamma⟩ : LiteralOpeningEvents.Kappa)) := by
  unfold LiteralOpeningEvents.readKappa
  rw [openingView_before P m c tail (by omega), kappa_withMessage P m c tail (by omega), ordinary_before P m c tail 27 (by omega)]

theorem readFirst_full (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (h : P.round = 29) :
    LiteralOpeningEvents.readFirst P m = (do
      let context ← LiteralOpeningView.read (full P m c tail)
      let payload ← LiteralOpeningStages.readFirst (full P m c tail)
      let gamma ← LiteralChallengeRead.ordinaryAt (full P m c tail) 27
      let kappa ← LiteralChallengeRead.ordinaryAt (full P m c tail) 28
      pure (⟨context, payload, gamma, kappa⟩ : LiteralOpeningEvents.First)) := by
  unfold LiteralOpeningEvents.readFirst
  rw [openingView_before P m c tail (by omega), first_withMessage P m c tail (by omega), ordinary_before P m c tail 27 (by omega), ordinary_before P m c tail 28 (by omega)]

theorem readSecond_full (P : Prefix) (m : Message) (c : Challenge)
    (tail : List (Message × Challenge)) (h : P.round = 30) :
    LiteralOpeningEvents.readSecond P m = (do
      let context ← LiteralOpeningView.read (full P m c tail)
      let payload ← LiteralOpeningStages.readSecond (full P m c tail)
      let word ← LiteralTranscript.vAt (full P m c tail)
      let gamma ← LiteralChallengeRead.ordinaryAt (full P m c tail) 27
      let kappa ← LiteralChallengeRead.ordinaryAt (full P m c tail) 28
      let alpha0 ← LiteralChallengeRead.ordinaryAt (full P m c tail) 29
      pure (⟨context, payload, word, gamma, kappa, alpha0⟩ : LiteralOpeningEvents.Second)) := by
  unfold LiteralOpeningEvents.readSecond
  rw [openingView_before P m c tail (by omega), second_withMessage P m c tail (by omega), word_withMessage P m c tail (by omega), ordinary_before P m c tail 27 (by omega), ordinary_before P m c tail 28 (by omega), ordinary_before P m c tail 29 (by omega)]

#print axioms openingView_before
#print axioms ordinary_before
#print axioms gamma_withMessage
#print axioms kappa_withMessage
#print axioms first_withMessage
#print axioms second_withMessage
#print axioms word_withMessage
#print axioms readGamma_full
#print axioms readKappa_full
#print axioms readFirst_full
#print axioms readSecond_full

end AspisR1.LiteralOpeningCoherence
end
