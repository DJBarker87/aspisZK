import SelectorValueLaneMap
import R0P.Value

/-! This final arithmetic layer identifies the actual generated `[0,2,4]`
selector sum with the coefficient used by the retained `R0P.valueFamily`
model, at an arbitrary point. It does not claim the later 33-cell iterator. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLaneModelComposition

open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

def pointSelector (point : Array QM 10#usize) (row : Fin 1024) : ExactQM :=
  AspisV8.SelectedSelectorExpansion.tensorProduct
    (AspisR1.SelectorAtPointModel.exactPoint point) 10 row.val

def valueFamilyCoefficientFor {K : Type} [Field K] (sel : R0P.Sel K) : K :=
  (((0 + sel 1008) + sel 1010) + sel 1012)

def valueFamilyRangeCoefficient (point : Array QM 10#usize) : ExactQM :=
  valueFamilyCoefficientFor (pointSelector point)

theorem generated_value_selector_is_valueFamily_coefficient
    (point : Array QM 10#usize)
    (hpoint : AspisR1.SelectorExpansionCorrectness.canonicalArray point) :
    ∃ selectors : pool_v1.pair_forest_copy_terminal.Selectors,
      ∃ q0 q2 q4 sum : QM,
        pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors ∧
        pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          selectors 0#usize = .ok (q0, selectors) ∧
        pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          selectors 2#usize = .ok (q2, selectors) ∧
        pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
          selectors 4#usize = .ok (q4, selectors) ∧
        core.array.Array.map
          pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
          AspisR1.SelectorValueLaneMap.selectorIndices selectors =
            .ok ⟨[q0, q2, q4], by rfl⟩ ∧
        (do
          let q1 ← field.QM31.add field.QM31.ZERO q0
          let q3 ← field.QM31.add q1 q2
          field.QM31.add q3 q4) = .ok sum ∧
        AspisR1.ExtractedMaskTowerAdd.CanonicalQM sum ∧
        AspisR1.ExtractedMaskQM31Exact.decode sum = valueFamilyRangeCoefficient point := by
  obtain ⟨selectors, q0, q2, q4, sum, hbox, hcall0, hcall2, hcall4,
    hmap, hadd, hcanon, hdecode⟩ :=
    AspisR1.SelectorValueLaneMap.boxed_value_lane_map_then_two_adds point hpoint
  refine ⟨selectors, q0, q2, q4, sum, hbox, hcall0, hcall2, hcall4,
    hmap, hadd, hcanon, ?_⟩
  calc
    AspisR1.ExtractedMaskQM31Exact.decode sum =
        AspisV8.SelectedSelectorExpansion.tensorProduct
          (AspisR1.SelectorAtPointModel.exactPoint point) 10 1008 +
        AspisV8.SelectedSelectorExpansion.tensorProduct
          (AspisR1.SelectorAtPointModel.exactPoint point) 10 1010 +
        AspisV8.SelectedSelectorExpansion.tensorProduct
          (AspisR1.SelectorAtPointModel.exactPoint point) 10 1012 := hdecode
    _ = valueFamilyRangeCoefficient point := by
      simp [valueFamilyRangeCoefficient, valueFamilyCoefficientFor, pointSelector]

/-- At a general selector function, the pure value-family multiplier is the
same left-to-right `[0,2,4]` coefficient used by the extracted source. -/
theorem valueFamily_uses_rangeCoefficient_for
    {K : Type} [Field K] (sel : R0P.Sel K) (pub : R0P.Public K)
    (o : R0P.Openings K) :
    (R0P.valueFamily (K := K)).residuals pub o sel =
      (R0P.valueRange o).map
        (fun r => valueFamilyCoefficientFor sel * r) ++
        [sel 1014 * ((o.z 0 - o.z 1) - o.z 2),
         sel 1014 * (o.succ 0 - o.succ 1)] := by
  rfl

theorem valueFamily_uses_rangeCoefficient
    (point : Array QM 10#usize) (pub : R0P.Public ExactQM)
    (o : R0P.Openings ExactQM) :
    (R0P.valueFamily (K := ExactQM)).residuals pub o
      (pointSelector point) =
      (R0P.valueRange o).map
        (fun r => valueFamilyRangeCoefficient point * r) ++
        [pointSelector point 1014 *
            ((o.z 0 - o.z 1) - o.z 2),
         pointSelector point 1014 * (o.succ 0 - o.succ 1)] := by
  change (R0P.valueFamily (K := ExactQM)).residuals pub o
      (pointSelector point) =
    (R0P.valueRange o).map
      (fun r => valueFamilyCoefficientFor (pointSelector point) * r) ++
      [pointSelector point 1014 * ((o.z 0 - o.z 1) - o.z 2),
       pointSelector point 1014 * (o.succ 0 - o.succ 1)]
  exact valueFamily_uses_rangeCoefficient_for
    (sel := pointSelector point) pub o

#print axioms generated_value_selector_is_valueFamily_coefficient
#print axioms valueFamily_uses_rangeCoefficient_for
#print axioms valueFamily_uses_rangeCoefficient
end AspisR1.SelectorValueLaneModelComposition
