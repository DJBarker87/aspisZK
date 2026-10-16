import SelectorValueLaneRangeListCorrespondence
import SelectorValueLaneIndexedLoop3
import SelectorValueLaneModelComposition
import ValueLaneExactResidualBridge
import R0P.Value

/-! The actual source range construction is factored after its exact prefix:
zero allocation, the three source preprocessing loops, reconstruction, checked
scales, reads and tail writes. The final indexed loop multiplies every cell by
the selector computed from the same boxed point. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLaneRangeConstruction

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Loop3 := AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3
abbrev CanonicalArray {n : Usize} (a : Array QM n) : Prop :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev exactVector (a : Array QM 33#usize) :=
  AspisR1.ValueLaneExactResidualBridge.exactVector a
abbrev exactOpenings := AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings

/-- The complete source range stage after `range_selector` is computed. -/
def rangeConstruction (openings : Openings) (rangeSelector : QM) :
    Result (Array QM 33#usize) := do
  let range ← AspisR1.SelectorValueLaneFullRangeValues.rangePrefixConstruction openings
  Loop3 rangeSelector range 0#usize

/-- The exact source result, canonicality, and weighted residual-list meaning
for the same selector used by the generated range loop. -/
theorem rangeConstruction_weighted_list
    (openings : Openings) (rangeSelector : QM)
    (hopenZ : AspisR1.SelectorValueLanePreprocessMeaning.CanonicalArray openings.z)
    (hopenSucc : AspisR1.SelectorValueLanePreprocessMeaning.CanonicalArray openings.succ_z)
    (hopenXor : AspisR1.SelectorValueLanePreprocessMeaning.CanonicalArray openings.xor12_z)
    (hselector : AspisR1.ExtractedMaskTowerAdd.CanonicalQM rangeSelector) :
    ∃ preweighted : Array QM 33#usize,
      AspisR1.SelectorValueLaneFullRangeValues.rangePrefixConstruction openings = .ok preweighted ∧
      ∃ out : Array QM 33#usize,
        rangeConstruction openings rangeSelector = .ok out ∧
        CanonicalArray out ∧
        List.ofFn (exactVector out) =
          (R0P.valueRange (exactOpenings openings)).map
            (fun r => decode rangeSelector * r) := by
  obtain ⟨preweighted, hpreCanonical, hpreRun, hpreList⟩ :=
    AspisR1.SelectorValueLaneRangeListCorrespondence.generated_range_list_eq_valueRange
      openings hopenZ hopenSucc hopenXor
  obtain ⟨out, hloop, houtCanonical, hvalues⟩ :=
    AspisR1.SelectorValueLaneIndexedLoop3.add_value_lanes_loop3_from_zero
      rangeSelector preweighted hselector hpreCanonical
  have hrun : rangeConstruction openings rangeSelector = .ok out := by
    simp only [rangeConstruction, hpreRun, hloop, bind_tc_ok]
  have hpreExact : List.ofFn (exactVector preweighted) =
      R0P.valueRange (exactOpenings openings) := by
    change List.ofFn (fun i : Fin 33 =>
      AspisR1.SelectorValueLanePreprocessMeaning.cell preweighted i) = _
    exact hpreList
  have hweighted : List.ofFn (exactVector out) =
      (List.ofFn (exactVector preweighted)).map
        (fun r => decode rangeSelector * r) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    change decode (out.val[i.val]'(by simpa [out.property] using i.isLt)) =
      decode rangeSelector *
        decode (preweighted.val[i.val]'(by simpa [preweighted.property] using i.isLt))
    have hvaluesi := hvalues i
    rw [AspisR1.SelectorValueLaneIndexedLoop3.cellAt_eq_getElem out i,
      AspisR1.SelectorValueLaneIndexedLoop3.cellAt_eq_getElem preweighted i] at hvaluesi
    exact hvaluesi
  rw [hpreExact] at hweighted
  exact ⟨preweighted, hpreRun, out, hrun, houtCanonical, hweighted⟩

/-- Instantiate the exact range-list theorem with the generated boxed-point
selector map and its left-to-right two-add sum. -/
theorem boxed_point_rangeConstruction_weighted_list
    (openings : Openings) (point : Array QM 10#usize)
    (hopenZ : AspisR1.SelectorValueLanePreprocessMeaning.CanonicalArray openings.z)
    (hopenSucc : AspisR1.SelectorValueLanePreprocessMeaning.CanonicalArray openings.succ_z)
    (hopenXor : AspisR1.SelectorValueLanePreprocessMeaning.CanonicalArray openings.xor12_z)
    (hpoint : CanonicalArray point) :
    ∃ selectors : pool_v1.pair_forest_copy_terminal.Selectors,
      ∃ q0 q2 q4 rangeSelector : QM,
        ∃ preweighted : Array QM 33#usize,
          ∃ out : Array QM 33#usize,
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
              field.QM31.add q3 q4) = .ok rangeSelector ∧
            AspisR1.SelectorValueLaneFullRangeValues.rangePrefixConstruction openings =
              .ok preweighted ∧
            rangeConstruction openings rangeSelector = .ok out ∧
            CanonicalArray out ∧
            List.ofFn (exactVector out) =
              (R0P.valueRange (exactOpenings openings)).map
                (fun r => decode rangeSelector * r) := by
  obtain ⟨selectors,q0,q2,q4,rangeSelector,hbox,hc0,hc2,hc4,hmap,hadd,
      hselector,hdecode⟩ :=
    AspisR1.SelectorValueLaneModelComposition.generated_value_selector_is_valueFamily_coefficient
      point hpoint
  obtain ⟨preweighted,hpreRun,out,hrun,hout,hlist⟩ :=
    rangeConstruction_weighted_list openings rangeSelector
      hopenZ hopenSucc hopenXor hselector
  exact ⟨selectors,q0,q2,q4,rangeSelector,preweighted,out,
    hbox,hc0,hc2,hc4,hmap,hadd,hpreRun,hrun,hout,hlist⟩

#print axioms rangeConstruction_weighted_list
#print axioms boxed_point_rangeConstruction_weighted_list
end AspisR1.SelectorValueLaneRangeConstruction
