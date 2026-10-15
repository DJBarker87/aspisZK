import R1LiteralStageFacts

/-! Successful literal staged reads expose the indexed entry and its current
payload read. These facts do not assert acceptance or transcript provenance. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralReadAtFacts

open AspisR1.LiteralTranscript
open AspisR1.LiteralOpeningStages
open AspisR1.CircleRecordCodec
open AspisR1.OpeningRecordCodec

theorem readAt_success {A : Type}
    (rs : List (Message × Challenge)) (i : Nat) (decode : AspisV8R19.DuplexFrames.Bytes → Option A)
    (value : A) (h : readAt rs i decode = some value) :
    ∃ m c, rs[i]? = some (m, c) ∧ LiteralTranscript.valid i m := by
  unfold readAt at h
  cases hi : rs[i]? with
  | none => simp [hi] at h
  | some entry =>
    rcases entry with ⟨m, c⟩
    by_cases hv : LiteralTranscript.valid i m
    · exact ⟨m, c, rfl, hv⟩
    · simp [hi, hv] at h

theorem readGamma_current (rs : List (Message × Challenge)) (p : Gamma)
    (h : readGamma rs = some p) :
    readAt rs 25 (CircleRecordCodec.decode 0) = some p.row25 ∧
    readAt rs 26 (CircleRecordCodec.decode 1) = some p.row26 ∧
    readAt rs 27 (OpeningRecordCodec.decode .gamma) = some p.row27 := by
  unfold readGamma at h
  cases h25 : readAt rs 25 (CircleRecordCodec.decode 0) with
  | none => simp [h25] at h
  | some r25 =>
    cases h26 : readAt rs 26 (CircleRecordCodec.decode 1) with
    | none => simp [h25, h26] at h
    | some r26 =>
      cases h27 : readAt rs 27 (OpeningRecordCodec.decode .gamma) with
      | none => simp [h25, h26, h27] at h
      | some r27 =>
        have heq : (⟨r25, r26, r27⟩ : Gamma) = p := by
          apply Option.some.inj
          simpa [h25, h26, h27] using h
        subst p
        exact ⟨rfl, rfl, rfl⟩

theorem readKappa_current (rs : List (Message × Challenge)) (p : Kappa)
    (h : readKappa rs = some p) :
    readAt rs 28 (OpeningRecordCodec.decode .kappa) = some p.row28 := by
  unfold readKappa at h
  cases hg : readGamma rs with
  | none => simp [hg] at h
  | some g =>
    cases h28 : readAt rs 28 (OpeningRecordCodec.decode .kappa) with
    | none => simp [hg, h28] at h
    | some r28 =>
      have heq : (⟨g, r28⟩ : Kappa) = p := by
        apply Option.some.inj
        simpa [hg, h28] using h
      subst p
      rfl

theorem readFirst_current (rs : List (Message × Challenge)) (p : First)
    (h : readFirst rs = some p) :
    readAt rs 29 (OpeningRecordCodec.decode .first) = some p.row29 := by
  unfold readFirst at h
  cases hk : readKappa rs with
  | none => simp [hk] at h
  | some k =>
    cases h29 : readAt rs 29 (OpeningRecordCodec.decode .first) with
    | none => simp [hk, h29] at h
    | some r29 =>
      have heq : (⟨k, r29⟩ : First) = p := by
        apply Option.some.inj
        simpa [hk, h29] using h
      subst p
      rfl

theorem readSecond_current (rs : List (Message × Challenge)) (p : Second)
    (h : readSecond rs = some p) :
    readAt rs 30 (OpeningRecordCodec.decode .second) = some p.row30 := by
  unfold readSecond at h
  cases hf : readFirst rs with
  | none => simp [hf] at h
  | some f =>
    cases h30 : readAt rs 30 (OpeningRecordCodec.decode .second) with
    | none => simp [hf, h30] at h
    | some r30 =>
      have heq : (⟨f, r30⟩ : Second) = p := by
        apply Option.some.inj
        simpa [hf, h30] using h
      subst p
      rfl

#print axioms readAt_success
#print axioms readGamma_current
#print axioms readKappa_current
#print axioms readFirst_current
#print axioms readSecond_current

end AspisR1.LiteralReadAtFacts
end
