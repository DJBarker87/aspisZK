import R1LiteralOpeningStages

/-! Successful later opening-stage reads expose their successful earlier
stages. These are Option plumbing facts only. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralStageFacts

open AspisR1.LiteralOpeningStages
open AspisR1.OpeningRecordCodec

theorem readKappa_gamma (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) (p : Kappa)
    (h : readKappa rs = some p) : readGamma rs = some p.toGamma := by
  unfold readKappa at h
  cases hg : readGamma rs with
  | none => simp [hg] at h
  | some g =>
    cases hr : readAt rs 28 (decode .kappa) with
    | none => simp [hg, hr] at h
    | some r =>
      have heq : (⟨g, r⟩ : Kappa) = p := by
        apply Option.some.inj
        simpa [hg, hr] using h
      exact congrArg some (congrArg (fun q : SelectedOpeningStages.Kappa => q.toGamma) heq)

theorem readFirst_kappa (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) (p : First)
    (h : readFirst rs = some p) : readKappa rs = some p.toKappa := by
  unfold readFirst at h
  cases hk : readKappa rs with
  | none => simp [hk] at h
  | some k =>
    cases hr : readAt rs 29 (decode .first) with
    | none => simp [hk, hr] at h
    | some r =>
      have heq : (⟨k, r⟩ : First) = p := by
        apply Option.some.inj
        simpa [hk, hr] using h
      exact congrArg some (congrArg (fun q : SelectedOpeningStages.First => q.toKappa) heq)

theorem readSecond_first (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) (p : Second)
    (h : readSecond rs = some p) : readFirst rs = some p.toFirst := by
  unfold readSecond at h
  cases hf : readFirst rs with
  | none => simp [hf] at h
  | some f =>
    cases hr : readAt rs 30 (decode .second) with
    | none => simp [hf, hr] at h
    | some r =>
      have heq : (⟨f, r⟩ : Second) = p := by
        apply Option.some.inj
        simpa [hf, hr] using h
      exact congrArg some (congrArg (fun q : SelectedOpeningStages.Second => q.toFirst) heq)

theorem readSecond_kappa (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) (p : Second)
    (h : readSecond rs = some p) : readKappa rs = some p.toKappa := by
  have hf := readSecond_first rs p h
  have hk := readFirst_kappa rs p.toFirst hf
  simpa using hk

theorem readSecond_gamma (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) (p : Second)
    (h : readSecond rs = some p) : readGamma rs = some p.toGamma := by
  have hk := readSecond_kappa rs p h
  have hg := readKappa_gamma rs p.toKappa hk
  simpa using hg

#print axioms readKappa_gamma
#print axioms readFirst_kappa
#print axioms readSecond_first
#print axioms readSecond_kappa
#print axioms readSecond_gamma

end AspisR1.LiteralStageFacts
end
