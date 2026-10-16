import SelectorAtPointModel
import SelectorValueLaneModelComposition
import R0P.SemDeg

/-! Reuse the retained SemDegree partition-of-unity and high/low marginal
proofs to connect actual boxed selector arrays to the retained family model
at arbitrary field points, beyond Boolean rows. -/
set_option autoImplicit false
namespace AspisR1.SelectorMarginalModel
noncomputable section
open scoped BigOperators
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SelectorAtPointModel
open AspisR1.SelectorExpansionCorrectness

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

def modelPoint (point : Array QM 10#usize) : Fin 10 → ExactQM :=
  fun i => exactPoint point i.val

theorem tensor_eq_bitWeight {K : Type} [Field K] (z : Nat → K) (n row : Nat) :
    AspisV8.SelectedSelectorExpansion.tensorProduct z n row =
      R0P.SemDegree.bitWeight n (fun i => z i.val) row := by
  unfold AspisV8.SelectedSelectorExpansion.tensorProduct R0P.SemDegree.bitWeight
  change (∏ i ∈ Finset.range n,
      AspisV8.SelectedSelectorExpansion.factor (z i) (row.testBit (n - 1 - i))) =
    ∏ i : Fin n,
      AspisV8.SelectedSelectorExpansion.factor (z i.val) (row.testBit (n - 1 - i.val))
  exact (Fin.prod_univ_eq_prod_range (fun i =>
    AspisV8.SelectedSelectorExpansion.factor (z i) (row.testBit (n - 1 - i))) n).symm

theorem pointSelector_eq_selAt (point : Array QM 10#usize) :
    pointSelector point = R0P.SemSource.selAt (modelPoint point) := by
  funext row
  change AspisV8.SelectedSelectorExpansion.tensorProduct (exactPoint point) 10 row.val =
    R0P.SemSource.selAt (modelPoint point) row
  rw [tensor_eq_bitWeight, R0P.SemDegree.selAt_eq_bitWeight]
  rfl

theorem high_marginal (point : Array QM 10#usize) (h : Fin 64) :
    R0P.g2High (pointSelector point) h =
      AspisV8.SelectedSelectorExpansion.tensorProduct (exactPoint point) 6 h.val := by
  rw [pointSelector_eq_selAt, R0P.SemDegree.g2High_selAt]
  rw [tensor_eq_bitWeight]
  rfl

theorem low_marginal (point : Array QM 10#usize) (l : Fin 16) :
    R0P.g2Low (pointSelector point) l =
      AspisV8.SelectedSelectorExpansion.tensorProduct
        (fun i => exactPoint point (6 + i)) 4 l.val := by
  rw [pointSelector_eq_selAt, R0P.SemDegree.g2Low_selAt]
  rw [tensor_eq_bitWeight]
  rfl

theorem boxed_marginals
    (point : Array QM 10#usize) (selectors : Selectors)
    (hpoint : canonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors) :
    canonicalArray selectors.high ∧ canonicalArray selectors.low ∧
      (∀ h : Fin 64, decodedArray selectors.high h.val = R0P.g2High (pointSelector point) h) ∧
      (∀ l : Fin 16, decodedArray selectors.low l.val = R0P.g2Low (pointSelector point) l) := by
  obtain ⟨actual, hactual, hhigh, hlow, hhighModel, hlowModel⟩ :=
    boxed_at_point_products point hpoint
  have heq : actual = selectors := Result.ok.inj (hactual.symm.trans hbox)
  subst actual
  refine ⟨hhigh, hlow, ?_, ?_⟩
  · intro h
    exact (hhighModel h).trans (high_marginal point h).symm
  · intro l
    exact (hlowModel l).trans (low_marginal point l).symm

#print axioms tensor_eq_bitWeight
#print axioms pointSelector_eq_selAt
#print axioms high_marginal
#print axioms low_marginal
#print axioms boxed_marginals
end
end AspisR1.SelectorMarginalModel
