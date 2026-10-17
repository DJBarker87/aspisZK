import AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModelFuel
import CopyActiveMaskBasisRegroup

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisLoop0Grouped

abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev QM := field.QM31

def decodedHigh (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (i : Fin 64) : ExactQM :=
  AspisR1.ExtractedMaskQM31Exact.decode
    (self.high.val[i.val]'(by simpa [self.high.property] using i.isLt))

private theorem prefixValue_eq_range
    (self : pool_v1.pair_forest_copy_terminal.Selectors) (j : Fin 7) :
    ∀ n : Nat,
      AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.prefixValue self j n =
        ∑ i ∈ Finset.range n,
          AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.prefixContribution self j i := by
  intro n
  induction n with
  | zero => simp [AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.prefixValue]
  | succ n ih =>
      rw [AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.prefixValue_succ,
        ih, Finset.sum_range_succ]

theorem loop0_prefix_is_grouped_high
    (self : pool_v1.pair_forest_copy_terminal.Selectors) (j : Fin 7) :
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.prefixValue self j 64 =
      R0P.activeMaskGroupedHigh (decodedHigh self) j := by
  rw [prefixValue_eq_range]
  rw [← Fin.sum_univ_eq_sum_range
    (fun n : Nat =>
      AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.prefixContribution self j n) 64]
  apply Finset.sum_congr rfl
  intro i _
  have hmodel := AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.model_coordinate_agrees i
  have hkey :
      (AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate
          (R0P.copyActiveRowMasks i)).val = j.val ↔
        R0P.activeMaskCoordinate (R0P.copyActiveRowMasks i) = j := by
    constructor
    · intro h
      exact Fin.ext (hmodel.symm.trans h)
    · intro h
      have hval := congrArg Fin.val h
      exact hmodel.trans hval
  simp [R0P.activeMaskGroupedHigh, decodedHigh,
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.prefixContribution,
    hkey]

#print axioms loop0_prefix_is_grouped_high
end AspisR1SelectedMaskProbe.ActiveMaskBasisLoop0Grouped
