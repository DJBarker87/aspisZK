import SelectorValueLaneCall
import ExtractedMaskQM31Exact
import ExtractedMaskConstants
import SelectorArrayMapRuntimeSlice
import SelectorArrayMapSuccess

/-! The first three source value selectors are mapped at indices [0,2,4]
with a state-preserving callback. We prove the generated map result and the
subsequent field-addition chain symbolically; no enclosing lane loop is claimed. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLaneMap

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SelectorValueLaneCall
open AspisR1.SelectorRowCall
open AspisR1.ExtractedMaskTowerAdd
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev CallMut := pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut

private theorem usize_add_eq_ok (a b out : Usize)
    (hval : a.val + b.val = out.val)
    (hbound : a.val + b.val ≤ Usize.max) :
    UScalar.add a b = .ok out := by
  have hchecked : (a + b : Result Usize) ⦃ x => x.val = a.val + b.val ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hbound
  obtain ⟨x, hx, hxval⟩ := Aeneas.Std.WP.spec_imp_exists hchecked
  change (a + b : Result Usize) = .ok out
  rw [hx]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hxval]
  exact hval

private theorem smallUsize_bound (n : Nat) (hn : n < 1024) :
    n < 2 ^ UScalarTy.Usize.numBits := by
  rw [UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
  have hmax := Usize.cMax_bound_concrete.1
  omega

private theorem fixed_offset_success (i : Usize) (hi : i.val < 16) :
    ∃ out : Usize, (1008#usize + i : Result Usize) = .ok out ∧
      out.val = 1008 + i.val := by
  have hb : 1008 + i.val < 2 ^ UScalarTy.Usize.numBits := by
    apply smallUsize_bound
    omega
  obtain ⟨out, hrun, hval⟩ :=
    AspisR1.ExtractedMaskReducerOps.tryMk_success (ty := .Usize) (1008 + i.val) hb
  have hresult : (1008#usize + i : Result Usize) = .ok out := by
    change UScalar.add 1008#usize i = .ok out
    simpa [UScalar.add] using hrun
  exact ⟨out, hresult, hval⟩

private theorem value_base_success :
    (16#usize * pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK : Result Usize)
      = .ok (1008#usize) := by
  have hb : 16 * 63 < 2 ^ UScalarTy.Usize.numBits := by
    cases System.Platform.numBits_eq <;> norm_num [UScalarTy.Usize_numBits_eq, *]
  obtain ⟨base, hrun, hval⟩ :=
    AspisR1.ExtractedMaskReducerOps.tryMk_success (ty := .Usize) (16 * 63) hb
  have hbase : base = (1008#usize) := by
    apply UScalar.eq_of_val_eq
    simpa [pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK] using hval
  change UScalar.mul 16#usize
      pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK = .ok (1008#usize)
  calc
    UScalar.mul 16#usize
        pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK = .ok base := by
          simpa [UScalar.mul, pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK] using hrun
    _ = .ok (1008#usize) := by rw [hbase]

private theorem callback_at_zero
    (selectors : Selectors) (hhigh : AspisR1.SelectorExpansionCorrectness.canonicalArray selectors.high)
    (hlow : AspisR1.SelectorExpansionCorrectness.canonicalArray selectors.low) :
    ∃ q : QM, CallMut selectors 0#usize = .ok (q, selectors) ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM q ∧
      AspisR1.ExtractedMaskQM31Exact.decode q = AspisR1.SelectorExpansionCorrectness.decodedArray selectors.high 63 *
        AspisR1.SelectorExpansionCorrectness.decodedArray selectors.low 0 := by
  have hrow : (1008#usize).val < 1024 := by scalar_tac
  obtain ⟨q, hrowrun, hcanon, hdecode⟩ :=
    row_success_of_canonical selectors 1008#usize hrow hhigh hlow
  refine ⟨q, ?_, hcanon, ?_⟩
  · change pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      selectors 0#usize = .ok (q, selectors)
    unfold pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    simp only [value_base_success, bind_tc_ok]
    obtain ⟨out, hoff, hout⟩ := fixed_offset_success 0#usize (by norm_num)
    have hout' : out = 1008#usize := by
      apply UScalar.eq_of_val_eq
      simpa using hout
    rw [hout'] at hoff
    simp only [hoff, bind_tc_ok, hrowrun]
  · have hv : (1008#usize).val = 1008 := by scalar_tac
    simpa [hv] using hdecode

private theorem callback_at_two
    (selectors : Selectors) (hhigh : AspisR1.SelectorExpansionCorrectness.canonicalArray selectors.high)
    (hlow : AspisR1.SelectorExpansionCorrectness.canonicalArray selectors.low) :
    ∃ q : QM, CallMut selectors 2#usize = .ok (q, selectors) ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM q ∧
      AspisR1.ExtractedMaskQM31Exact.decode q = AspisR1.SelectorExpansionCorrectness.decodedArray selectors.high 63 *
        AspisR1.SelectorExpansionCorrectness.decodedArray selectors.low 2 := by
  have hrow : (1010#usize).val < 1024 := by scalar_tac
  obtain ⟨q, hrowrun, hcanon, hdecode⟩ :=
    row_success_of_canonical selectors 1010#usize hrow hhigh hlow
  refine ⟨q, ?_, hcanon, ?_⟩
  · change pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      selectors 2#usize = .ok (q, selectors)
    unfold pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    simp only [value_base_success, bind_tc_ok]
    obtain ⟨out, hoff, hout⟩ := fixed_offset_success 2#usize (by norm_num)
    have hout' : out = 1010#usize := by
      apply UScalar.eq_of_val_eq
      simpa using hout
    rw [hout'] at hoff
    simp only [hoff, bind_tc_ok, hrowrun]
  · have hv : (1010#usize).val = 1010 := by scalar_tac
    simpa [hv] using hdecode

private theorem callback_at_four
    (selectors : Selectors) (hhigh : AspisR1.SelectorExpansionCorrectness.canonicalArray selectors.high)
    (hlow : AspisR1.SelectorExpansionCorrectness.canonicalArray selectors.low) :
    ∃ q : QM, CallMut selectors 4#usize = .ok (q, selectors) ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM q ∧
      AspisR1.ExtractedMaskQM31Exact.decode q = AspisR1.SelectorExpansionCorrectness.decodedArray selectors.high 63 *
        AspisR1.SelectorExpansionCorrectness.decodedArray selectors.low 4 := by
  have hrow : (1012#usize).val < 1024 := by scalar_tac
  obtain ⟨q, hrowrun, hcanon, hdecode⟩ :=
    row_success_of_canonical selectors 1012#usize hrow hhigh hlow
  refine ⟨q, ?_, hcanon, ?_⟩
  · change pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      selectors 4#usize = .ok (q, selectors)
    unfold pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    simp only [value_base_success, bind_tc_ok]
    obtain ⟨out, hoff, hout⟩ := fixed_offset_success 4#usize (by norm_num)
    have hout' : out = 1012#usize := by
      apply UScalar.eq_of_val_eq
      simpa using hout
    rw [hout'] at hoff
    simp only [hoff, bind_tc_ok, hrowrun]
  · have hv : (1012#usize).val = 1012 := by scalar_tac
    simpa [hv] using hdecode

private theorem zero_canonical : AspisR1.ExtractedMaskTowerAdd.CanonicalQM field.QM31.ZERO :=
  AspisR1.ExtractedMaskConstants.zero_canonical

def selectorIndices : Array Usize 3#usize :=
  Array.make 3#usize [0#usize, 2#usize, 4#usize]

theorem selector_map_then_two_adds
    (selectors : Selectors)
    (hhigh : AspisR1.SelectorExpansionCorrectness.canonicalArray selectors.high)
    (hlow : AspisR1.SelectorExpansionCorrectness.canonicalArray selectors.low) :
    ∃ q0 q2 q4 s : QM,
      CallMut selectors 0#usize = .ok (q0, selectors) ∧
      CallMut selectors 2#usize = .ok (q2, selectors) ∧
      CallMut selectors 4#usize = .ok (q4, selectors) ∧
      core.array.Array.map
        pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        selectorIndices selectors = .ok ⟨[q0, q2, q4], by rfl⟩ ∧
      (do
        let q1 ← field.QM31.add field.QM31.ZERO q0
        let q3 ← field.QM31.add q1 q2
        field.QM31.add q3 q4) = .ok s ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM s ∧
      AspisR1.ExtractedMaskQM31Exact.decode s = AspisR1.ExtractedMaskQM31Exact.decode q0 + AspisR1.ExtractedMaskQM31Exact.decode q2 + AspisR1.ExtractedMaskQM31Exact.decode q4 ∧
      AspisR1.ExtractedMaskQM31Exact.decode q0 = AspisR1.SelectorExpansionCorrectness.decodedArray selectors.high 63 *
        AspisR1.SelectorExpansionCorrectness.decodedArray selectors.low 0 ∧
      AspisR1.ExtractedMaskQM31Exact.decode q2 = AspisR1.SelectorExpansionCorrectness.decodedArray selectors.high 63 *
        AspisR1.SelectorExpansionCorrectness.decodedArray selectors.low 2 ∧
      AspisR1.ExtractedMaskQM31Exact.decode q4 = AspisR1.SelectorExpansionCorrectness.decodedArray selectors.high 63 *
        AspisR1.SelectorExpansionCorrectness.decodedArray selectors.low 4 := by
  obtain ⟨q0, hcall0, hcan0, hdec0⟩ := callback_at_zero selectors hhigh hlow
  obtain ⟨q2, hcall2, hcan2, hdec2⟩ := callback_at_two selectors hhigh hlow
  obtain ⟨q4, hcall4, hcan4, hdec4⟩ := callback_at_four selectors hhigh hlow
  have hstate : AspisV8R19.TraversalRuntime.mapState
      pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      ([0#usize, 2#usize, 4#usize] : List Usize) selectors =
        .ok ([q0, q2, q4], selectors) := by
    simp only [AspisV8R19.TraversalRuntime.mapState, hcall0, hcall2, hcall4, bind_tc_ok]
  have hstateArray : AspisV8R19.TraversalRuntime.mapState
      pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      selectorIndices.val selectors = .ok ([q0, q2, q4], selectors) := by
    simpa [selectorIndices, Array.make] using hstate
  have hmap : core.array.Array.map
      pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      selectorIndices selectors = .ok ⟨[q0, q2, q4], by rfl⟩ := by
    have hmap' := Aeneas.Std.core.array.Array.map_success
      pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      selectorIndices selectors [q0, q2, q4] selectors hstateArray
    exact hmap'
  have hzero := zero_canonical
  obtain ⟨q1, hadd1, hcan1, hdec1⟩ := current_qm_add_exact field.QM31.ZERO q0 hzero hcan0
  obtain ⟨q3, hadd2, hcan3, hdec3⟩ := current_qm_add_exact q1 q2 hcan1 hcan2
  obtain ⟨s, hadd3, hcanS, hdecS⟩ := current_qm_add_exact q3 q4 hcan3 hcan4
  refine ⟨q0, q2, q4, s, hcall0, hcall2, hcall4, hmap, ?_, hcanS, ?_, hdec0, hdec2, hdec4⟩
  · simp only [hadd1, bind_tc_ok, hadd2, bind_tc_ok, hadd3]
  · rw [hdecS, hdec3, hdec1]
    simp [AspisR1.ExtractedMaskConstants.zero_decode]

/-- The selector arrays themselves are obtained from the actual boxed-point
source method, so callers need only provide a canonical ten-cell point. -/
theorem boxed_value_lane_map_then_two_adds
    (point : Array QM 10#usize)
    (hpoint : AspisR1.SelectorExpansionCorrectness.canonicalArray point) :
    ∃ selectors : Selectors, ∃ q0 q2 q4 s : QM,
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors ∧
      CallMut selectors 0#usize = .ok (q0, selectors) ∧
      CallMut selectors 2#usize = .ok (q2, selectors) ∧
      CallMut selectors 4#usize = .ok (q4, selectors) ∧
      core.array.Array.map
        pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        selectorIndices selectors = .ok ⟨[q0, q2, q4], by rfl⟩ ∧
      (do
        let q1 ← field.QM31.add field.QM31.ZERO q0
        let q3 ← field.QM31.add q1 q2
        field.QM31.add q3 q4) = .ok s ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM s ∧
      AspisR1.ExtractedMaskQM31Exact.decode s =
        AspisV8.SelectedSelectorExpansion.tensorProduct
          (AspisR1.SelectorAtPointModel.exactPoint point) 10 1008 +
        AspisV8.SelectedSelectorExpansion.tensorProduct
          (AspisR1.SelectorAtPointModel.exactPoint point) 10 1010 +
        AspisV8.SelectedSelectorExpansion.tensorProduct
          (AspisR1.SelectorAtPointModel.exactPoint point) 10 1012 := by
  obtain ⟨selectors, hbox, hhigh, hlow, hrows⟩ :=
    AspisR1.SelectorRowSemantic.boxed_row_products point hpoint
  obtain ⟨q0, q2, q4, s, hcall0, hcall2, hcall4, hmap, hadd, hcanon, hdecode,
    hdecode0, hdecode2, hdecode4⟩ := selector_map_then_two_adds selectors hhigh hlow
  have hbits0 := AspisV8.SelectedSelectorExpansion.selected_index_arithmetic 1008
  have hbits2 := AspisV8.SelectedSelectorExpansion.selected_index_arithmetic 1010
  have hbits4 := AspisV8.SelectedSelectorExpansion.selected_index_arithmetic 1012
  norm_num at hbits0 hbits2 hbits4
  have hrow0 : AspisR1.SelectorExpansionCorrectness.decodedArray selectors.high 63 *
      AspisR1.SelectorExpansionCorrectness.decodedArray selectors.low 0 =
      AspisV8.SelectedSelectorExpansion.tensorProduct
        (AspisR1.SelectorAtPointModel.exactPoint point) 10 1008 := by
    simpa [hbits0.1, hbits0.2] using (hrows ⟨1008, by norm_num⟩).2
  have hrow2 : AspisR1.SelectorExpansionCorrectness.decodedArray selectors.high 63 *
      AspisR1.SelectorExpansionCorrectness.decodedArray selectors.low 2 =
      AspisV8.SelectedSelectorExpansion.tensorProduct
        (AspisR1.SelectorAtPointModel.exactPoint point) 10 1010 := by
    simpa [hbits2.1, hbits2.2] using (hrows ⟨1010, by norm_num⟩).2
  have hrow4 : AspisR1.SelectorExpansionCorrectness.decodedArray selectors.high 63 *
      AspisR1.SelectorExpansionCorrectness.decodedArray selectors.low 4 =
      AspisV8.SelectedSelectorExpansion.tensorProduct
        (AspisR1.SelectorAtPointModel.exactPoint point) 10 1012 := by
    simpa [hbits4.1, hbits4.2] using (hrows ⟨1012, by norm_num⟩).2
  refine ⟨selectors, q0, q2, q4, s, hbox, hcall0, hcall2, hcall4, hmap,
    hadd, hcanon, ?_⟩
  rw [hdecode, hdecode0, hdecode2, hdecode4, hrow0, hrow2, hrow4]

#print axioms selector_map_then_two_adds
#print axioms boxed_value_lane_map_then_two_adds
end AspisR1.SelectorValueLaneMap
