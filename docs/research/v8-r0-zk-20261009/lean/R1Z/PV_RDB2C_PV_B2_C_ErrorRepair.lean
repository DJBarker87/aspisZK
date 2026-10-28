import R1Z.PV_RDB2C_PV_B2_C_RawWeights253Funs
set_option autoImplicit false
namespace PV_B2_C_ErrorRepair
open Aeneas Aeneas.Std Result PV_B2_253c1

/-- The frozen fixed-array read fails independently of its contents. -/
theorem index_failure (table : Array U16 1024#usize) (j : Usize)
    (hj : (1024#usize).val ≤ j.val) :
    Array.index_usize table j = fail .arrayOutOfBounds := by
  simp only [Array.index_usize,Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_none (by simpa only [table.property] using hj)]

/-- The repaired emission uses the same indexing failure for every invalid D index. -/
theorem copied_row_failure (j : Usize) (hj : (1024#usize).val ≤ j.val) :
    host_weights.host_row .D j = fail .arrayOutOfBounds := by
  simp only [host_weights.host_row,index_failure _ j hj,bind_tc_fail]

theorem copied_raw_failure (w : host_weights.Weights) (hw : w.variant = .D)
    (j : Usize) (hj : (1024#usize).val ≤ j.val) :
    pv_b2_raw w 0#usize j = fail .arrayOutOfBounds := by
  simp only [pv_b2_raw,host_weights.Weights.raw,host_weights.raw_value,
    ite_true,hw,copied_row_failure j hj,bind_tc_fail]

/-- Complete Result equality at the retained counterexample input, for any
frozen table and every continuation. This makes no assumption on table data. -/
theorem op253_counterexample_repaired (w : host_weights.Weights)
    (hw : w.variant = .D) (table : Array U16 1024#usize)
    (k : U16 → Result aspis_core.field.QM31) :
    pv_b2_raw w 0#usize 1024#usize =
      (Array.index_usize table 1024#usize >>= k) := by
  rw [copied_raw_failure w hw _ (Nat.le_refl _),
    index_failure table _ (Nat.le_refl _),bind_tc_fail]

#print axioms index_failure
#print axioms copied_row_failure
#print axioms copied_raw_failure
#print axioms op253_counterexample_repaired
end PV_B2_C_ErrorRepair
