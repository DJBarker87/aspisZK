import AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModelFuel
import AspisR1SelectedMaskProbe.ActiveMaskBasisLoop0Grouped
import AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Fuel
import AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1FiniteModel
import AspisR1.ArrayZeroExact
import CopyEndpointExact
import CopyActiveMaskBasisRegroup

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisComplete

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.ArrayUpdateCanonicalExact.CanonicalArray a
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev modelSelectors := AspisR1.CopyEndpointExact.modelSelectors
abbrev loop0Prefix := AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.prefixValue

private theorem sourceHigh_eq_modelHigh
    (self : pool_v1.pair_forest_copy_terminal.Selectors) :
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoop0Grouped.decodedHigh self =
      (modelSelectors self).high := by
  funext i
  simp [AspisR1SelectedMaskProbe.ActiveMaskBasisLoop0Grouped.decodedHigh,
    modelSelectors, AspisR1.CopyEndpointExact.modelSelectors,
    AspisR1.SelectorExpansionCorrectness.decodedArray,
    AspisR1.SelectorExpansionCorrectness.decodedAt,
    AspisR1.SelectorExpansionCorrectness.decode]

private theorem sourceLow_eq_modelLow
    (self : pool_v1.pair_forest_copy_terminal.Selectors) :
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step.LowSumModel self =
      (modelSelectors self).low := by
  funext i
  simp [AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step.LowSumModel,
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1SourceLow.decodedLow,
    modelSelectors, AspisR1.CopyEndpointExact.modelSelectors,
    AspisR1.SelectorExpansionCorrectness.decodedArray,
    AspisR1.SelectorExpansionCorrectness.decodedAt,
    AspisR1.SelectorExpansionCorrectness.decode]

set_option backward.isDefEq.respectTransparency false in

/-- Exact source execution of both active-mask loops, with no selector-domain
assumption. The result decodes to the retained seven-coordinate basis model. -/
theorem active_mask_basis_success
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (hhigh : CanonicalArray self.high) (hlow : CanonicalArray self.low) :
    ∃ out : QM,
      pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis self = .ok out ∧
      CanonicalQM out ∧ decode out = R0P.activeMaskBasisModel (modelSelectors self) := by
  let zeroHigh := Array.repeat 7#usize field.QM31.ZERO
  have hzeroHigh : CanonicalArray zeroHigh := by
    simpa [zeroHigh] using AspisR1.ArrayZeroExact.repeat_zero_canonical
  have hinitial0 : ∀ j : Fin 7, decode
      (AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.cell zeroHigh j) =
        loop0Prefix self j 0 := by
    intro j
    change AspisR1.CopyEndpointExact.decodedCells zeroHigh j = _
    rw [AspisR1.ArrayZeroExact.repeat_zero_decoded]
    simp [loop0Prefix,
      AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.prefixValue]
  obtain ⟨highSums, hloop0, hhighSums, hprefix⟩ :=
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModelFuel.loop0_success_fuel_prefix
      self zeroHigh 0#usize 64 (by decide) hhigh hzeroHigh hinitial0
  have hloop1Initial : decode field.QM31.ZERO =
      AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Fuel.prefixValue
        self highSums 0 := by
    simp [AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Fuel.prefixValue,
      AspisR1.ExtractedMaskConstants.zero_decode]
  obtain ⟨out, hloop1, hout, hresult⟩ :=
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Fuel.loop1_success_fuel_prefix
      self highSums field.QM31.ZERO 0#usize 7 (by decide)
      hhighSums hlow (by simpa using AspisR1.ExtractedMaskConstants.zero_canonical)
      hloop1Initial
  have hprefixSum : decode out =
      ∑ j : Fin 7,
        decode (AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1FiniteModel.cell highSums j) *
          AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step.LowSumMeaning
            (AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step.LowSumModel self)
            (R0P.activeMaskBasisMasks j) := by
    change AspisR1.ExtractedMaskQM31Exact.decode out = _
    rw [hresult]
    change AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1FiniteModel.prefixValue
      self highSums 7 = _
    rw [AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1FiniteModel.prefixValue_seven_eq_finset_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rfl
  have hhighGrouped : ∀ j : Fin 7,
      decode (AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1FiniteModel.cell highSums j) =
        R0P.activeMaskGroupedHigh (modelSelectors self).high j := by
    intro j
    have hcell :
        AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModelFuel.cell highSums j =
          AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1FiniteModel.cell highSums j := rfl
    calc
      decode (AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1FiniteModel.cell highSums j) =
          decode (AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModelFuel.cell highSums j) :=
        congrArg decode hcell.symm
      _ = AspisR1SelectedMaskProbe.ActiveMaskBasisLoopModel.prefixValue self j 64 := hprefix j
      _ = R0P.activeMaskGroupedHigh
          (AspisR1SelectedMaskProbe.ActiveMaskBasisLoop0Grouped.decodedHigh self) j :=
        AspisR1SelectedMaskProbe.ActiveMaskBasisLoop0Grouped.loop0_prefix_is_grouped_high self j
      _ = R0P.activeMaskGroupedHigh (modelSelectors self).high j := by
        rw [sourceHigh_eq_modelHigh]
  have hmodel : decode out = R0P.activeMaskBasisModel (modelSelectors self) := by
    rw [hprefixSum]
    simp_rw [hhighGrouped]
    rw [sourceLow_eq_modelLow]
    rfl
  refine ⟨out, ?_, hout, ?_⟩
  · rw [pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis]
    rw [hloop0]
    change pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1
      self highSums field.QM31.ZERO 0#usize = .ok out
    exact hloop1
  · rw [hmodel]

#print axioms active_mask_basis_success
end AspisR1SelectedMaskProbe.ActiveMaskBasisComplete
