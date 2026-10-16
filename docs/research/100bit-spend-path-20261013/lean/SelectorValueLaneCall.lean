import SelectorRowCall
import SelectorValueLaneGeneratedSlice
import ExtractedMaskReducerOps

/-! The actual `add_value_lanes` callback consumes selector row 63 with a small
in-lane offset. This composition establishes successful source reads and the
corresponding exact ten-factor weight; it does not claim the enclosing map or
lane aggregation. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLaneCall

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SelectorAtPointModel
open AspisR1.SelectorRowCall
open AspisR1.SelectorExpansionCorrectness

abbrev QM := field.QM31
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev CallMut := pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut

private theorem small_bound (n : Nat) (hn : n < 1024) :
    n < 2 ^ UScalarTy.Usize.numBits := by
  rw [UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
  have hmax := Usize.cMax_bound_concrete.1
  omega

private theorem add_value_base_success :
    (16#usize * pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK : Result Usize)
      = .ok (1008#usize) := by
  have hb : 16 * 63 < 2 ^ UScalarTy.Usize.numBits := by
    apply small_bound
    norm_num
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

private theorem add_value_offset_success (i : Usize) (hi : i.val < 16) :
    ∃ row : Usize,
      (1008#usize + i : Result Usize) = .ok row ∧ row.val = 1008 + i.val := by
  have hb : 1008 + i.val < 2 ^ UScalarTy.Usize.numBits := by
    apply small_bound
    omega
  obtain ⟨row, hrun, hval⟩ :=
    AspisR1.ExtractedMaskReducerOps.tryMk_success (ty := .Usize) (1008 + i.val) hb
  have hresult : (1008#usize + i : Result Usize) = .ok row := by
    change UScalar.add 1008#usize i = .ok row
    simpa [UScalar.add] using hrun
  exact ⟨row, hresult, hval⟩

theorem add_value_callback_success
    (point : Array QM 10#usize) (hpoint : canonicalArray point)
    (i : Usize) (hi : i.val < 16) :
    ∃ selectors : Selectors, ∃ q : QM,
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors ∧
      CallMut selectors i = .ok (q, selectors) ∧
      AspisR1.SelectorRowCall.CanonicalQM q ∧
      AspisR1.ExtractedMaskQM31Exact.decode q =
        AspisV8.SelectedSelectorExpansion.tensorProduct
          (exactPoint point) 10 (1008 + i.val) := by
  obtain ⟨row, hadd, hrowval⟩ := add_value_offset_success i hi
  have hrow : row.val < 1024 := by omega
  obtain ⟨selectors, q, hbox, hcallRow, hcanon, hdecode⟩ :=
    boxed_row_matches_ten_factor point hpoint row hrow
  refine ⟨selectors, q, hbox, ?_, hcanon, ?_⟩
  · change pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      selectors i = .ok (q, selectors)
    unfold pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    simp only [add_value_base_success, bind_tc_ok, hadd, bind_tc_ok, hcallRow]
  · simpa [hrowval] using hdecode

#print axioms add_value_callback_success
end AspisR1.SelectorValueLaneCall
