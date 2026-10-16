import SelectorValueLaneModelComposition

/-! The actual source range-selector prefix, including map output reads and
the checked field-addition chain, for the same boxed selectors used later by
the conservation tail. -/
set_option autoImplicit false
namespace AspisR1.ValueLaneRangeSelectorRun
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev CanonicalArray {N : Usize} (a : Array QM N) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a

def run (selectors : Selectors) : Result QM := do
  let values ← core.array.Array.map
    pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    AspisR1.SelectorValueLaneMap.selectorIndices selectors
  let q0 ← Array.index_usize values 0#usize
  let q1 ← field.QM31.add field.QM31.ZERO q0
  let q2 ← Array.index_usize values 1#usize
  let q3 ← field.QM31.add q1 q2
  let q4 ← Array.index_usize values 2#usize
  field.QM31.add q3 q4

theorem same_boxed_range_selector
    (point : Array QM 10#usize) (selectors : Selectors)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors) :
    ∃ selector : QM,
      run selectors = .ok selector ∧ Canonical selector ∧
      AspisR1.ExtractedMaskQM31Exact.decode selector =
        AspisR1.SelectorValueLaneModelComposition.valueFamilyRangeCoefficient point := by
  obtain ⟨selectors', q0, q2, q4, selector, hbox', _hc0, _hc2, _hc4,
    hmap, hadd, hcanonical, hvalue⟩ :=
    AspisR1.SelectorValueLaneModelComposition.generated_value_selector_is_valueFamily_coefficient
      point hpoint
  have heq : selectors' = selectors := Result.ok.inj (hbox'.symm.trans hbox)
  subst selectors'
  refine ⟨selector, ?_, hcanonical, hvalue⟩
  have hread0 : Array.index_usize
      (⟨[q0, q2, q4], by rfl⟩ : Array QM 3#usize) 0#usize = .ok q0 := by rfl
  have hread1 : Array.index_usize
      (⟨[q0, q2, q4], by rfl⟩ : Array QM 3#usize) 1#usize = .ok q2 := by rfl
  have hread2 : Array.index_usize
      (⟨[q0, q2, q4], by rfl⟩ : Array QM 3#usize) 2#usize = .ok q4 := by rfl
  unfold run
  simp only [hmap, bind_tc_ok, hread0]
  simp_rw [hread1, hread2, bind_tc_ok]
  exact hadd

#print axioms same_boxed_range_selector
end AspisR1.ValueLaneRangeSelectorRun
