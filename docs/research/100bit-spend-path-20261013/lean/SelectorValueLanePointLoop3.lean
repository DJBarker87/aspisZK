import SelectorValueLaneMap
import SelectorValueLaneIndexedLoop3
import SelectorExpansionCorrectness

/-! Compose the actual boxed-point selector map/two-adds with the final
source loop. The 33-cell range is an explicit canonical input supplied by
the preceding source stages; this theorem derives both actual call success
and the indexed loop's output canonicality. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLanePointLoop3

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev CanonicalArray {n : Usize} (a : Array QM n) : Prop :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev Loop3 := AspisR1SelectedMaskProbeIndexed.pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3

/-- The generated selector computation and generated 33-cell loop compose
for every canonical point and canonical input range. -/
theorem boxed_point_then_loop3
    (point : Array QM 10#usize) (range : Array QM 33#usize)
    (hpoint : CanonicalArray point) (hrange : CanonicalArray range) :
    ∃ selectors : Selectors, ∃ q0 q2 q4 selector : QM,
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
        field.QM31.add q3 q4) = .ok selector ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM selector ∧
      AspisR1.ExtractedMaskQM31Exact.decode selector =
        AspisV8.SelectedSelectorExpansion.tensorProduct
          (AspisR1.SelectorAtPointModel.exactPoint point) 10 1008 +
        AspisV8.SelectedSelectorExpansion.tensorProduct
          (AspisR1.SelectorAtPointModel.exactPoint point) 10 1010 +
        AspisV8.SelectedSelectorExpansion.tensorProduct
          (AspisR1.SelectorAtPointModel.exactPoint point) 10 1012 ∧
      Loop3 selector range 0#usize = .ok out ∧
      CanonicalArray out ∧
      ∀ j : Fin 33,
        AspisR1.ExtractedMaskQM31Exact.decode
          (out.val[j.val]'(by simpa [out.property] using j.isLt)) =
        AspisR1.ExtractedMaskQM31Exact.decode selector *
          AspisR1.ExtractedMaskQM31Exact.decode
            (range.val[j.val]'(by simpa [range.property] using j.isLt)) := by
  obtain ⟨selectors, q0, q2, q4, selector, hbox, hcall0, hcall2, hcall4,
      hmap, hadd, hselector, hdecode⟩ :=
    AspisR1.SelectorValueLaneMap.boxed_value_lane_map_then_two_adds point hpoint
  obtain ⟨out, hloop, hout, hvalues⟩ :=
    AspisR1.SelectorValueLaneIndexedLoop3.add_value_lanes_loop3_from_zero
      selector range hselector hrange
  refine ⟨selectors, q0, q2, q4, selector, out, hbox, hcall0, hcall2,
    hcall4, hmap, hadd, hselector, hdecode, hloop, hout, ?_⟩
  intro j
  have hj := j.isLt
  have hv := hvalues j
  change AspisR1.ExtractedMaskQM31Exact.decode
      (if h : j.val < 33 then out.val[j.val]'(by simpa [out.property] using h)
       else field.QM31.ZERO) =
    AspisR1.ExtractedMaskQM31Exact.decode selector *
      AspisR1.ExtractedMaskQM31Exact.decode
        (if h : j.val < 33 then range.val[j.val]'(by simpa [range.property] using h)
         else field.QM31.ZERO) at hv
  simpa only [dif_pos hj] using hv

#print axioms boxed_point_then_loop3
end AspisR1.SelectorValueLanePointLoop3
