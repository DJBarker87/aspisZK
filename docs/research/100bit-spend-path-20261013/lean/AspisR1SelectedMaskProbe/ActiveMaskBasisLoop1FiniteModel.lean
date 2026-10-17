import AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Fuel

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1FiniteModel

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev LowSumMeaning := AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step.LowSumMeaning
abbrev LowSumModel := AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step.LowSumModel
abbrev cell {n : Usize} (a : Array QM n) (j : Fin n.val) : QM :=
  AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Fuel.cell a j
abbrev term (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (highSums : Array QM 7#usize) (i : Nat) : ExactQM :=
  AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Fuel.term self highSums i
abbrev prefixValue (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (highSums : Array QM 7#usize) (i : Nat) : ExactQM :=
  AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Fuel.prefixValue self highSums i

def termFin (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (highSums : Array QM 7#usize) (j : Fin 7) : ExactQM :=
  AspisR1.ExtractedMaskQM31Exact.decode (cell highSums j) *
    LowSumMeaning (LowSumModel self) (R0P.activeMaskBasisMasks j)

theorem prefixValue_seven_eq_finset_sum
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (highSums : Array QM 7#usize) :
    prefixValue self highSums 7 = ∑ j : Fin 7, termFin self highSums j := by
  simp [prefixValue, AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Fuel.prefixValue,
    term, termFin, AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Fuel.term,
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Fuel.cell,
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step.LowSumMeaning,
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step.LowSumModel,
    Fin.sum_univ_succ, add_assoc]

#print axioms prefixValue_seven_eq_finset_sum
end AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1FiniteModel
