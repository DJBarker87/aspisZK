import SelectorRowCall
import SelectorValueLaneModelComposition

/-! Reuse the old checked row method theorem on the same already-returned
boxed selectors. All actual row-operation success and its model are derived. -/
set_option autoImplicit false
namespace AspisR1.SameBoxedRowExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

theorem row_success (point : Array QM 10#usize) (selectors : Selectors)
    (row : Usize) (hrow : row.val < 1024)
    (hpoint : AspisR1.SelectorExpansionCorrectness.canonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors) :
    ∃ q, pool_v1.pair_forest_copy_terminal.Selectors.row selectors row = .ok q ∧
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM q ∧
      AspisR1.ExtractedMaskQM31Exact.decode q = pointSelector point ⟨row.val, hrow⟩ := by
  obtain ⟨actual, q, hactual, hrun, hcanonical, hvalue⟩ :=
    AspisR1.SelectorRowCall.boxed_row_matches_ten_factor point hpoint row hrow
  have heq : actual = selectors := Result.ok.inj (hactual.symm.trans hbox)
  subst actual
  exact ⟨q, hrun, hcanonical, hvalue⟩

#print axioms row_success
end AspisR1.SameBoxedRowExact
