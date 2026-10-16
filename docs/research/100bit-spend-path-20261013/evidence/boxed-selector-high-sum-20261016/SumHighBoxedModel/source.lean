import SumHighSingleRange
import SumHighModelCorrespondence
import SelectorMarginalModel

/-! Actual singleton-range source summation at the same returned boxed
selector point. The marginal-model premise is discharged using the retained
partition-of-unity theorems and the checked source boxed-selector arrays. -/
set_option autoImplicit false
namespace AspisR1.SumHighBoxedModel
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SumHighInnerLoop
open AspisR1.SumHighSingleRange

abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

theorem boxed_singleton
    (point : Array QM 10#usize) (selectors : Selectors) (r : Range)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hstart : r.start.val ≤ r.end.val) (hend : r.end.val ≤ 64) :
    ∃ out,
      AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high
        selectors (singleton r) = .ok out ∧ Canonical out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out =
        R0P.g2SumHigh (pointSelector point) r.start.val (r.end.val - r.start.val) (by omega) := by
  obtain ⟨hhigh, _hlow, hhighModel, _hlowModel⟩ :=
    AspisR1.SelectorMarginalModel.boxed_marginals point selectors hpoint hbox
  obtain ⟨out, hrun, hcanonical, hmodel⟩ := singleton_success r selectors hstart hend hhigh
  refine ⟨out, hrun, hcanonical, ?_⟩
  exact hmodel.trans (AspisR1.SumHighModelCorrespondence.sumModel_eq_g2SumHigh
    selectors (pointSelector point) (r.end.val - r.start.val) r.start.val (by omega)
    hhighModel)

def pathRange : Range := { start := 57#usize, «end» := 63#usize }

theorem boxed_path_sum
    (point : Array QM 10#usize) (selectors : Selectors)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors) :
    ∃ out,
      AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high
        selectors (singleton pathRange) = .ok out ∧ Canonical out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out =
        R0P.g2SumHigh (pointSelector point) 57 6 (by omega) := by
  obtain ⟨out, hrun, hcanonical, hmodel⟩ :=
    boxed_singleton point selectors pathRange hpoint hbox
      (by simp only [pathRange]; scalar_tac) (by simp only [pathRange]; scalar_tac)
  refine ⟨out, hrun, hcanonical, ?_⟩
  have h57 : (57#usize).val = 57 := by scalar_tac
  have h63 : (63#usize).val = 63 := by scalar_tac
  simpa only [pathRange, h57, h63] using hmodel

#print axioms boxed_singleton
#print axioms boxed_path_sum
end
end AspisR1.SumHighBoxedModel
