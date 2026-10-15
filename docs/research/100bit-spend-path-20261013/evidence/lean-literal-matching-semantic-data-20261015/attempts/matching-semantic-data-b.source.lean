import R1LiteralMatchingFacts
import R1LiteralOpeningFunctionalFacts
import R1LiteralOpeningDataRows

/-! Successful literal matching-data reads agree with the common opening
view and its selected raw-row functionals. This is deterministic model
composition; it makes no source-correspondence or acceptance claim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralMatchingSemanticData

open AspisR1.LiteralTranscript
open AspisR1.LiteralOpeningView
open AspisR1.SelectedOpeningFunctionals
open AspisR1.MatchingSupport

abbrev E := AspisR1.LiteralMatchingData.E

-- Keep the already-proved functional model symbolic during this projection.
attribute [local irreducible] SelectedOpeningFunctionals.functionals
  SelectedOpeningFunctionals.rawBase SelectedOpeningFunctionals.rows

theorem read_matches_view
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (d : MatchingSupport.Data E)
    (hread : LiteralMatchingData.read rs = some d) :
    ∃ v : LiteralOpeningView.View,
      LiteralOpeningView.read rs = some v ∧
      d.W = v.word ∧ d.F = v.functionals ∧ d.F0 = v.baseFunctional := by
  obtain ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
    hcommon, _, _, _, _, _, _, _, hd⟩ :=
    LiteralMatchingFacts.read_success_components rs d hread
  refine ⟨common, hcommon, ?_, ?_, ?_⟩
  · calc
      d.W = (SelectedOpeningData.data
          (LiteralMatchingFacts.payloads staged row31) common.word word
          common.functionals common.baseFunctional gamma kappa alpha0 alpha1).W := by
            rw [hd]
      _ = common.word := rfl
  · calc
      d.F = (SelectedOpeningData.data
          (LiteralMatchingFacts.payloads staged row31) common.word word
          common.functionals common.baseFunctional gamma kappa alpha0 alpha1).F := by
            rw [hd]
      _ = common.functionals := rfl
  · calc
      d.F0 = (SelectedOpeningData.data
          (LiteralMatchingFacts.payloads staged row31) common.word word
          common.functionals common.baseFunctional gamma kappa alpha0 alpha1).F0 := by
            rw [hd]
      _ = common.baseFunctional := rfl

theorem read_rows_identity
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (d : MatchingSupport.Data E)
    (hread : LiteralMatchingData.read rs = some d) :
    ∃ v : LiteralOpeningView.View,
      LiteralOpeningView.read rs = some v ∧
      RawOpening.withRows (RingHom.id E)
        (SelectedOpeningFunctionals.rows (v.semantic.map Prod.snd) v.circlePoints) d = d := by
  obtain ⟨common, staged, row31, word, gamma, kappa, alpha0, alpha1,
    hcommon, _, _, _, _, _, _, _, hd⟩ :=
    LiteralMatchingFacts.read_success_components rs d hread
  have ⟨hcommonF, hcommonF0⟩ :=
    LiteralOpeningFunctionalFacts.read_functionals rs common hcommon
  have hF : d.F = SelectedOpeningFunctionals.functionals
      (E := AspisWideTower.WideExact) (common.semantic.map Prod.snd) common.circlePoints := by
    calc
      d.F = (SelectedOpeningData.data
          (LiteralMatchingFacts.payloads staged row31) common.word word
          common.functionals common.baseFunctional gamma kappa alpha0 alpha1).F := by
            rw [hd]
      _ = common.functionals := rfl
      _ = SelectedOpeningFunctionals.functionals
          (E := AspisWideTower.WideExact) (common.semantic.map Prod.snd) common.circlePoints :=
            hcommonF
  have hF0 : d.F0 = SelectedOpeningFunctionals.rawBase
      (E := AspisWideTower.WideExact) (common.semantic.map Prod.snd) common.circlePoints := by
    calc
      d.F0 = (SelectedOpeningData.data
          (LiteralMatchingFacts.payloads staged row31) common.word word
          common.functionals common.baseFunctional gamma kappa alpha0 alpha1).F0 := by
            rw [hd]
      _ = common.baseFunctional := rfl
      _ = SelectedOpeningFunctionals.rawBase
          (E := AspisWideTower.WideExact) (common.semantic.map Prod.snd) common.circlePoints :=
            hcommonF0
  exact ⟨common, hcommon,
    LiteralOpeningDataRows.withRows_eq_self d (common.semantic.map Prod.snd)
      common.circlePoints hF hF0⟩

#print axioms read_matches_view
#print axioms read_rows_identity

end AspisR1.LiteralMatchingSemanticData
end
