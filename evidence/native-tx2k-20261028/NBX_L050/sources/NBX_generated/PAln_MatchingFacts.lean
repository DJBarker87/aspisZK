import R1LiteralMatchingData

/-! Deterministic decomposition of a successful literal matching-data read.
This exposes the component reads already required by the reader; it adds no
acceptance, source-refinement, or security claim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_MatchingFacts

open AspisR1.LiteralTranscript
open AspisR1.LiteralOpeningView
open AspisR1.LiteralOpeningStages
open AspisR1.LiteralChallengeRead
open AspisR1.OpeningRecordCodec
open AspisR1.SelectedOpeningData
open AspisR1.MatchingSupport

abbrev E := AspisR1.LiteralMatchingData.E

/-- The strict opening payloads assembled by `LiteralMatchingData.read` from
its staged rows and the separately read final row. -/
def payloads (staged : LiteralOpeningStages.Second)
    (row31 : OpeningRecordCodec.Payload .final) : SelectedOpeningData.Payloads :=
  { row25 := staged.toFirst.toKappa.toGamma.row25
    row26 := staged.toFirst.toKappa.toGamma.row26
    row27 := staged.toFirst.toKappa.toGamma.row27
    row28 := staged.toFirst.toKappa.row28
    row29 := staged.toFirst.row29
    row30 := staged.row30
    row31 := row31 }

theorem read_success_components
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (d : MatchingSupport.Data E)
    (h : LiteralMatchingData.read rs = some d) :
    ∃ (common : LiteralOpeningView.View)
      (staged : LiteralOpeningStages.Second)
      (row31 : OpeningRecordCodec.Payload .final)
      (word : LiteralTranscript.VWord)
      (gamma kappa alpha0 alpha1 : E),
      LiteralOpeningView.read rs = some common ∧
      LiteralOpeningStages.readSecond rs = some staged ∧
      LiteralOpeningStages.readAt rs 31 (OpeningRecordCodec.decode .final) = some row31 ∧
      LiteralTranscript.vAt rs = some word ∧
      LiteralChallengeRead.ordinaryAt rs 27 = some gamma ∧
      LiteralChallengeRead.ordinaryAt rs 28 = some kappa ∧
      LiteralChallengeRead.ordinaryAt rs 29 = some alpha0 ∧
      LiteralChallengeRead.ordinaryAt rs 30 = some alpha1 ∧
      d = SelectedOpeningData.data (payloads staged row31) common.word word
        common.functionals common.baseFunctional gamma kappa alpha0 alpha1 := by
  unfold LiteralMatchingData.read at h
  cases hcommon : LiteralOpeningView.read rs with
  | none => simp [hcommon] at h
  | some common =>
    cases hstaged : LiteralOpeningStages.readSecond rs with
    | none => simp [hcommon, hstaged] at h
    | some staged =>
      cases hrow31 : LiteralOpeningStages.readAt rs 31 (OpeningRecordCodec.decode .final) with
      | none => simp [hcommon, hstaged, hrow31] at h
      | some row31 =>
        cases hword : LiteralTranscript.vAt rs with
        | none => simp [hcommon, hstaged, hrow31, hword] at h
        | some word =>
          cases hgamma : LiteralChallengeRead.ordinaryAt rs 27 with
          | none => simp [hcommon, hstaged, hrow31, hword, hgamma] at h
          | some gamma =>
            cases hkappa : LiteralChallengeRead.ordinaryAt rs 28 with
            | none => simp [hcommon, hstaged, hrow31, hword, hgamma, hkappa] at h
            | some kappa =>
              cases halpha0 : LiteralChallengeRead.ordinaryAt rs 29 with
              | none => simp [hcommon, hstaged, hrow31, hword, hgamma, hkappa, halpha0] at h
              | some alpha0 =>
                cases halpha1 : LiteralChallengeRead.ordinaryAt rs 30 with
                | none => simp [hcommon, hstaged, hrow31, hword, hgamma, hkappa, halpha0, halpha1] at h
                | some alpha1 =>
                  simp [hcommon, hstaged, hrow31, hword, hgamma, hkappa, halpha0, halpha1] at h
                  refine ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
                    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
                  exact h.symm

#print axioms read_success_components

end AspisR1.PAln_MatchingFacts
end
